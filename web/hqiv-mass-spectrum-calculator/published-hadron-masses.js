/**
 * PDG / literature hadron masses — comparison layer only (not HQIV inputs).
 * Loads data/hadron_published_masses.json when served over HTTP.
 */
(function (root) {
  "use strict";

  const DEFAULT_JSON_PATH = "../../data/hadron_published_masses.json";
  let cache = null;

  function relErrPct(modelMeV, pubMeV) {
    if (!pubMeV || pubMeV === 0) return null;
    return ((modelMeV - pubMeV) / pubMeV) * 100;
  }

  function lookupPublished(db, configId, pdgName) {
    if (!db) return null;
    if (configId && db.by_config_id && db.by_config_id[configId]) {
      return db.by_config_id[configId];
    }
    if (pdgName && db.by_key && db.by_key[pdgName]) {
      return db.by_key[pdgName];
    }
    return null;
  }

  function compareToPublished(db, modelGeV, configId, pdgName) {
    const pub = lookupPublished(db, configId, pdgName);
    if (!pub) return null;
    const modelMeV = modelGeV * 1000;
    const deltaMeV = modelMeV - pub.mass_MeV;
    const rel = relErrPct(modelMeV, pub.mass_MeV);
    return {
      published: pub,
      model_MeV: modelMeV,
      model_GeV: modelGeV,
      delta_MeV: deltaMeV,
      rel_err_pct: rel,
      sigma_pull:
        pub.uncertainty_MeV > 0 ? deltaMeV / pub.uncertainty_MeV : null,
    };
  }

  function entriesByCategory(db) {
    if (!db || !db.entries) return {};
    const out = {};
    for (const e of db.entries) {
      const c = e.category || "other";
      if (!out[c]) out[c] = [];
      out[c].push(e);
    }
    return out;
  }

  function getPublishedMasses() {
    return cache;
  }

  function fetchPublishedMasses(jsonPath) {
    if (cache) return Promise.resolve(cache);
    const path = jsonPath || DEFAULT_JSON_PATH;
    return fetch(path)
      .then((r) => (r.ok ? r.json() : null))
      .then((j) => {
        if (j) cache = j;
        return j;
      })
      .catch(() => cache);
  }

  function setPublishedMasses(data) {
    cache = data;
  }

  root.HQIVPublishedHadrons = {
    DEFAULT_JSON_PATH,
    fetchPublishedMasses,
    getPublishedMasses,
    setPublishedMasses,
    lookupPublished,
    compareToPublished,
    entriesByCategory,
    relErrPct,
  };
})(typeof globalThis !== "undefined" ? globalThis : window);
