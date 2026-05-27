"""Tests for hqiv_orbital_flyby_omaxwell.py."""

import math
import unittest

import hqiv_orbital_flyby_omaxwell as orb


class TestHQIVOrbitalFlyby(unittest.TestCase):
    def test_phi_of_shell_matches_lean(self) -> None:
        self.assertAlmostEqual(orb.phi_of_shell(4), 10.0)

    def test_geff_ratio_unity_at_reference(self) -> None:
        body = orb.EARTH
        phi = body.phi_reference()
        self.assertAlmostEqual(orb.geff_ratio(phi, phi), 1.0)

    def test_newton_points_inward(self) -> None:
        a = orb.newton_accel((orb.R_EARTH, 0.0, 0.0), orb.EARTH)
        self.assertLess(a[0], 0.0)
        self.assertAlmostEqual(a[1], 0.0)
        self.assertAlmostEqual(a[2], 0.0)

    def test_j2_zero_on_axis(self) -> None:
        a = orb.j2_accel((0.0, 0.0, 2.0 * orb.R_EARTH), orb.EARTH)
        self.assertAlmostEqual(a[0], 0.0)
        self.assertAlmostEqual(a[1], 0.0)

    def test_sun_moon_positions_are_finite(self) -> None:
        sun = orb.sun_position_geocentric("1998-01-23")
        moon = orb.moon_position_geocentric("1998-01-23")
        self.assertAlmostEqual(orb._norm(sun) / orb.AU, 1.0, delta=0.02)
        self.assertAlmostEqual(orb._norm(moon) / orb.MOON_SEMIMAJOR_AXIS, 1.0, delta=0.2)

    def test_third_body_tide_vanishes_at_geocenter(self) -> None:
        case = orb.FLYBY_CATALOG["near_1998"]
        a = orb.earth_third_body_accel((0.0, 0.0, 0.0), case)
        self.assertLess(orb._norm(a), 1e-18)

    def test_sun_moon_advance_with_time_offset(self) -> None:
        iso = "1998-01-23"
        s0 = orb.sun_position_geocentric(iso, 0.0)
        s1 = orb.sun_position_geocentric(iso, 86_400.0)
        m0 = orb.moon_position_geocentric(iso, 0.0)
        m1 = orb.moon_position_geocentric(iso, 86_400.0)
        delta_sun_deg = math.degrees(math.acos(max(-1.0, min(1.0, orb._dot(s0, s1) / (orb._norm(s0) * orb._norm(s1))))))
        delta_moon_deg = math.degrees(math.acos(max(-1.0, min(1.0, orb._dot(m0, m1) / (orb._norm(m0) * orb._norm(m1))))))
        self.assertAlmostEqual(delta_sun_deg, 1.0, delta=0.1)
        self.assertAlmostEqual(delta_moon_deg, 13.0, delta=2.0)

    def test_rk4_fourth_order_convergence_on_kepler(self) -> None:
        gm = orb.EARTH.gm
        r0 = orb.R_EARTH * 3.0
        v_circ = math.sqrt(gm / r0)
        state0 = orb.OrbitState(r=(r0, 0.0, 0.0), v=(0.0, v_circ, 0.0), t=0.0)
        T = 2.0 * math.pi * math.sqrt(r0 ** 3 / gm)

        def energy_err(dt: float) -> float:
            steps = int(round(T / dt))
            settings = orb.PropagationSettings(
                dt=T / steps, t_max=T * 2.0, use_j2=False, use_third_bodies=False
            )
            state = state0
            for _ in range(steps):
                state = orb.rk4_step(state, orb.EARTH, None, settings, 1.0)
            e0 = 0.5 * orb._dot(state0.v, state0.v) - gm / orb._norm(state0.r)
            e1 = 0.5 * orb._dot(state.v, state.v) - gm / orb._norm(state.r)
            return abs(e1 - e0) / abs(e0)

        e1 = energy_err(60.0)
        e2 = energy_err(120.0)
        ratio = e2 / max(e1, 1e-30)
        # RK4 local error is O(dt^5); over a fixed period the per-step doubling ⇒ 2^4 = 16×.
        self.assertGreater(ratio, 12.0)
        self.assertLess(e1, 1.0e-8)

    def test_geff_as_time_factor_scales_total_uniformly(self) -> None:
        r = (orb.R_EARTH * 1.5, 0.0, 0.0)
        v = (0.0, 8000.0, 1000.0)
        case = orb.FLYBY_CATALOG["near_1998"]
        settings = orb.propagation_settings_for(orb.EARTH, case)
        base = orb.HQIVOrbitCoupling(
            paper_inertia_screen=True,
            modified_inertia_geodesic=False,
            geff_on_newton=True,
            angular_momentum_screen=False,
            vacuum_scale=0.0,
            metric_phi_scale=0.0,
            lapse_drag_phi=False,
            horizon_repartition=False,
            horizon_metric_channel=False,
        )
        coup_time = orb.replace(base, geff_as_time_factor=True)
        a_time, _, _ = orb.total_accel(r, v, orb.EARTH, coup_time, settings, 1.0, case)
        phi_dim = orb.phi_readout(r, orb.EARTH)
        screen_w = orb.modified_inertia_at_point(
            r, v, orb.newton_accel(r, orb.EARTH), orb.EARTH, coup_time, settings, case
        ).screen_weight
        g_ratio = orb.screened_geff_ratio(phi_dim, orb.EARTH.phi_reference(), screen_w)
        a_grav_no_geff = orb._add(
            orb.newton_accel(r, orb.EARTH),
            orb.j2_accel(r, orb.EARTH) if settings.use_j2 else (0.0, 0.0, 0.0),
        )
        a_grav_no_geff = orb._add(
            a_grav_no_geff,
            orb.earth_third_body_accel(r, case) if settings.use_third_bodies else (0.0, 0.0, 0.0),
        )
        for i in range(3):
            self.assertAlmostEqual(a_time[i], a_grav_no_geff[i] * g_ratio, places=10)
        far = (orb.R_EARTH * 1000.0, 0.0, 0.0)
        v_far = (0.0, 100.0, 0.0)
        coup_src = orb.replace(base, geff_as_time_factor=False)
        a_far_src, _, _ = orb.total_accel(far, v_far, orb.EARTH, coup_src, settings, 1.0, case)
        a_far_time, _, _ = orb.total_accel(far, v_far, orb.EARTH, coup_time, settings, 1.0, case)
        self.assertNotAlmostEqual(a_far_src[0], a_far_time[0], places=20)

    def test_derived_vector_fraction_is_gamma_not_half(self) -> None:
        r = (orb.R_EARTH * 2.0, 0.0, 0.0)
        v = (8000.0, 0.0, 500.0)
        settings = orb.PropagationSettings(h_reference=8.0e10)
        coup = orb.HQIVOrbitCoupling(lapse_drag_vector_fraction=None)
        lam = orb.derived_horizon_vector_fraction(r, v, orb.EARTH, coup, settings)
        self.assertLess(lam, orb.GAMMA_HQIV + 1e-12)
        self.assertGreater(lam, 0.0)
        self.assertNotAlmostEqual(lam, 0.5, places=2)
        fixed = orb.derived_horizon_vector_fraction(
            r, v, orb.EARTH, orb.replace(coup, lapse_drag_vector_fraction=0.5), settings
        )
        self.assertAlmostEqual(fixed, 0.5)

    def test_derived_vector_fraction_vanishes_on_equatorial_lock(self) -> None:
        r = (orb.R_EARTH * 2.0, 0.0, 0.0)
        v = (0.0, 8000.0, 0.0)
        settings = orb.PropagationSettings(h_reference=1.0e9)
        coup = orb.HQIVOrbitCoupling(lapse_drag_vector_fraction=None)
        lam = orb.derived_horizon_vector_fraction(r, v, orb.EARTH, coup, settings)
        self.assertLess(lam, 1.0e-6)

    def test_co_spin_lapse_vanishes_on_spin_axis(self) -> None:
        eq = orb.co_spin_lapse_fraction((orb.R_EARTH * 2.0, 0.0, 0.0), orb.EARTH)
        pole = orb.co_spin_lapse_fraction((0.0, 0.0, orb.R_EARTH * 2.0), orb.EARTH)
        self.assertGreater(eq, 0.0)
        self.assertLess(pole, 1.0e-12)
        flat = orb.co_spin_lapse_fraction(
            (0.0, 0.0, orb.R_EARTH * 2.0), orb.EARTH, use_colatitude=False
        )
        self.assertEqual(flat, 0.0)

    def test_co_spin_lapse_uses_doppler_projection(self) -> None:
        r = (orb.R_EARTH * 2.0, 0.0, 0.0)
        tangential = orb.co_spin_lapse_fraction(r, (0.0, 8000.0, 0.0), orb.EARTH)
        polar = orb.co_spin_lapse_fraction(r, (0.0, 0.0, 8000.0), orb.EARTH)
        radial = orb.co_spin_lapse_fraction(r, (8000.0, 0.0, 0.0), orb.EARTH)
        self.assertGreater(tangential, 0.0)
        self.assertLess(polar, tangential * 1.0e-12)
        self.assertLess(radial, tangential * 1.0e-12)

    def test_lense_thirring_direction_perpendicular_to_spin_and_radius(self) -> None:
        r = (orb.R_EARTH * 2.0, orb.R_EARTH * 0.5, orb.R_EARTH * 0.3)
        d = orb.lense_thirring_direction(r, orb.EARTH)
        omega = orb.EARTH.spin_vector()
        self.assertAlmostEqual(orb._dot(d, r) / orb._norm(r), 0.0, places=12)
        self.assertAlmostEqual(orb._dot(d, omega) / orb._norm(omega), 0.0, places=12)
        self.assertAlmostEqual(orb._norm(d), 1.0, places=12)
        self.assertEqual(orb.lense_thirring_direction((0.0, 0.0, orb.R_EARTH), orb.EARTH), (0.0, 0.0, 0.0))

    def test_horizon_repartition_uses_metric_not_phi_pump(self) -> None:
        r = (orb.R_EARTH * 2.0, 0.0, 0.0)
        v = (0.0, 8000.0, 0.0)
        a_gr = orb.newton_accel(r, orb.EARTH)
        rep = orb.HQIVOrbitCoupling(
            lapse_drag_phi=True,
            horizon_repartition=True,
            horizon_metric_channel=True,
        )
        leg = orb.replace(rep, horizon_repartition=False)
        phi_rep = orb.effective_phi_acceleration_si(r, v, a_gr, orb.EARTH, rep, None)
        phi_leg = orb.effective_phi_acceleration_si(r, v, a_gr, orb.EARTH, leg, None)
        self.assertAlmostEqual(phi_rep, orb.phi_acceleration_si(r, orb.EARTH), places=20)
        self.assertGreater(phi_leg, phi_rep)
        settings = orb.PropagationSettings()
        self.assertGreater(
            orb._norm(orb.horizon_metric_accel(r, v, a_gr, orb.EARTH, rep, settings, None)),
            0.0,
        )

    def test_hqiv_perturbation_small_far_field(self) -> None:
        r = (100.0 * orb.R_EARTH, 0.0, 0.0)
        v = (1000.0, 0.0, 0.0)
        coupling = orb.HQIVOrbitCoupling(
            vacuum_scale=1.0,
            metric_phi_scale=1.0,
            paper_inertia_screen=False,
        )
        a = orb.hqiv_perturbation_accel(r, v, orb.EARTH, coupling, screen_weight=1.0)
        self.assertLess(orb._norm(a), 0.05)

    def test_modified_inertia_geodesic_divides_gravity_by_f(self) -> None:
        """Paper law: a = a_GR / f when modified_inertia_geodesic is on."""
        r = (orb.R_EARTH, 0.0, 0.0)
        v = (0.0, 7500.0, 0.0)
        settings = orb.PropagationSettings()
        coupling = orb.HQIVOrbitCoupling(
            paper_inertia_screen=True,
            modified_inertia_geodesic=True,
            angular_momentum_screen=False,
            geff_on_newton=False,
            vacuum_scale=0.0,
            metric_phi_scale=0.0,
            lapse_drag_phi=False,
            horizon_repartition=False,
        )
        a_hqiv, _, f_val = orb.total_accel(r, v, orb.EARTH, coupling, settings)
        a_gr = orb.newton_accel(r, orb.EARTH, 1.0)
        a_gr = orb._add(a_gr, orb.j2_accel(r, orb.EARTH, 1.0))
        self.assertGreater(f_val, 0.0)
        self.assertLess(f_val, 1.0)
        for i in range(3):
            self.assertAlmostEqual(a_hqiv[i], a_gr[i] / f_val, places=5)

    def test_inertia_screen_suppresses_at_high_acceleration(self) -> None:
        phi_a = orb.phi_acceleration_homogeneous_si()
        a_high = 10.0  # m/s² flyby-scale
        w = orb.inertia_screen_weight(a_high, phi_a)
        self.assertLess(w, 1e-6)
        a_low = 1e-11
        w_low = orb.inertia_screen_weight(a_low, phi_a)
        self.assertGreater(w_low, 0.5)

    def test_classical_energy_near_conserved_short_arc(self) -> None:
        case = orb.FLYBY_CATALOG["generic_deep"]
        settings = orb.PropagationSettings(dt=5.0, t_max=5000.0)
        state = orb.flyby_initial_state(case, orb.EARTH)
        e0 = 0.5 * orb._dot(state.v, state.v) - orb.EARTH.gm / orb._norm(state.r)
        for _ in range(200):
            state = orb.rk4_step(state, orb.EARTH, None, settings, case.spin_sign)
        e1 = 0.5 * orb._dot(state.v, state.v) - orb.EARTH.gm / orb._norm(state.r)
        rel = abs(e1 - e0) / abs(e0)
        self.assertLess(rel, 1e-4)

    def test_spin_reversal_flips_hqiv_vacuum_channel(self) -> None:
        """The spin-odd vacuum chart channel should flip when planet spin is reversed."""
        r = (orb.R_EARTH, 0.2 * orb.R_EARTH, 0.1 * orb.R_EARTH)
        v = (1000.0, 7500.0, 200.0)
        coupling = orb.HQIVOrbitCoupling(
            vacuum_scale=1.0,
            metric_phi_scale=0.0,
            horizon_repartition=False,
            suppress_vacuum_spin_coupling=False,
        )
        a_pos = orb.hqiv_perturbation_accel(r, v, orb.EARTH, coupling, spin_sign=1.0)
        a_neg = orb.hqiv_perturbation_accel(r, v, orb.EARTH, coupling, spin_sign=-1.0)
        self.assertGreater(orb._norm(a_pos), 0.0)
        for i in range(3):
            self.assertAlmostEqual(a_pos[i], -a_neg[i])

    def test_propagate_returns_finite_delta_v(self) -> None:
        case = orb.FLYBY_CATALOG["galileo_1990"]
        settings = orb.PropagationSettings(dt=4.0, t_max=120_000.0)
        row = orb.propagate_flyby(case, orb.EARTH, None, settings)
        self.assertFalse(math.isnan(float(row["delta_v_mm_s"])))

    def test_unit_from_lat_lon_pole_and_equator(self) -> None:
        eq = orb.unit_from_lat_lon(0.0, 0.0)
        self.assertAlmostEqual(eq[2], 0.0, places=8)
        pole = orb.unit_from_lat_lon(90.0, 0.0)
        self.assertAlmostEqual(pole[2], 1.0, places=8)

    def test_angular_momentum_screen_higher_on_polar_geometry(self) -> None:
        """Low |L_z|/|L| (polar-style) yields larger (1−f) than full equatorial lock."""
        body = orb.EARTH
        h_ref = 8.0e10
        r_eq = (orb.R_EARTH, 0.0, 0.0)
        v_eq = (0.0, 8000.0, 0.0)
        r_pol = (0.0, 0.0, orb.R_EARTH)
        v_pol = (8000.0, 0.0, 0.0)
        a_n = orb.newton_accel(r_eq, body)
        w_eq, _, _ = orb.angular_momentum_inertia_screen_weight(r_eq, v_eq, a_n, body, h_ref)
        a_n2 = orb.newton_accel(r_pol, body)
        w_pol, _, _ = orb.angular_momentum_inertia_screen_weight(r_pol, v_pol, a_n2, body, h_ref)
        self.assertGreater(w_pol, w_eq)

    def test_shell_equatorial_fraction_floor(self) -> None:
        self.assertAlmostEqual(orb.shell_equatorial_fraction_floor(4), 1.0 / 25.0)
        self.assertAlmostEqual(orb.shell_equatorial_fraction_floor(0), 1.0)

    def test_polar_phi_boost_saturates_at_ladder(self) -> None:
        """h_z=0, ρ=1 ⇒ boost (m+1)² for m=4 (25× on φ)."""
        boost = orb.polar_fiber_phi_boost(0.0, 1.0, 1.0, 1.0, 4)
        self.assertAlmostEqual(boost, 25.0)

    def test_oumuamua_interstellar_propagates(self) -> None:
        case = orb.INTERSTELLAR_CATALOG["oumuamua_2017"]
        body = orb.SUN
        settings = orb.propagation_settings_for(body, case)
        row = orb.propagate_flyby(case, body, None, settings)
        self.assertFalse(math.isnan(float(row["delta_v_mm_s"])))
        self.assertGreater(float(row["r_ca_km"]), 0.0)
        q_au = 0.255
        self.assertLess(abs(float(row["r_ca_km"]) / (orb.AU / 1e3) - q_au), 0.15)

    def test_sun_uses_rotating_bunched_lapse(self) -> None:
        self.assertGreater(orb.SUN.omega, 0.0)
        self.assertEqual(orb.SUN.lapse_radius(), orb.SUN.radius)
        equator_eps = orb.co_spin_lapse_fraction((orb.SUN.radius, 0.0, 0.0), orb.SUN)
        pole_eps = orb.co_spin_lapse_fraction((0.0, 0.0, orb.SUN.radius), orb.SUN)
        self.assertGreater(equator_eps, 0.0)
        self.assertEqual(pole_eps, 0.0)

    def test_orbital_angular_rindler_circular_null(self) -> None:
        r_mag = 3.0 * orb.R_EARTH
        r = (r_mag, 0.0, 0.0)
        v = (0.0, math.sqrt(orb.GM_EARTH / r_mag), 0.0)
        a = orb.newton_accel(r, orb.EARTH, 1.0)
        self.assertAlmostEqual(orb.orbital_angular_rindler_scale(r, v, a), 0.0)

    def test_orbital_angular_rindler_hyperbolic_positive_and_ablatable(self) -> None:
        case = orb.INTERSTELLAR_CATALOG["oumuamua_2017"]
        body = orb.SUN
        r = (case.impact_parameter, 0.0, 0.0)
        v = (case.v_inf, case.v_inf, 0.0)
        a = orb.newton_accel(r, body, 1.0)
        self.assertGreater(orb.orbital_angular_rindler_scale(r, v, a), 0.0)

        settings = orb.propagation_settings_for(body, case)
        settings = orb.replace(settings, h_reference=orb.flyby_h_reference(case))
        on = orb.paper_nominal_coupling()
        off = orb.replace(on, orbital_angular_rindler=False)
        f_on = orb.modified_inertia_at_point(r, v, a, body, on, settings, case).f_blend
        f_off = orb.modified_inertia_at_point(r, v, a, body, off, settings, case).f_blend
        self.assertGreater(f_on, f_off)

    def test_equator_to_pole_exceeds_equator_exchange(self) -> None:
        """Tilted oblate plane (b_azimuth=90) should yield larger |Δλ| than coplanar equator."""
        settings = orb.PropagationSettings(dt=4.0, t_max=200_000.0)
        pole = orb.propagate_flyby(orb.FLYBY_CATALOG["equator_to_pole"], orb.EARTH, None, settings)
        equ = orb.propagate_flyby(orb.FLYBY_CATALOG["equator_to_equator"], orb.EARTH, None, settings)
        ex_pole = float(pole["latitude_exchange_deg"])
        ex_equ = float(equ["latitude_exchange_deg"])
        self.assertGreater(ex_pole, ex_equ)
        self.assertGreater(abs(float(pole["asymptote_lat_out_deg"])), abs(float(equ["asymptote_lat_out_deg"])))


if __name__ == "__main__":
    unittest.main()
