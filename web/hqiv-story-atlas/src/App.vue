<script setup lang="ts">
import katex from "katex";
import { computed, onBeforeUnmount, onMounted, ref, watch } from "vue";
import { derivations } from "@/data/derivations";
import { categories, type CategoryId, type StoryItem } from "@/data/storyMenu";

const activeCategory = ref<CategoryId>("foundations");
const activeItemId = ref<string | null>(categories[0]?.items[0]?.id ?? null);
const activeTermKey = ref<string | null>(null);

const activeCategoryDef = computed(() => categories.find((c) => c.id === activeCategory.value)!);
const activeItem = computed<StoryItem | null>(() => {
  const id = activeItemId.value;
  if (!id) return null;
  return activeCategoryDef.value.items.find((i) => i.id === id) ?? null;
});
const activeDerivation = computed(() =>
  activeItem.value?.derivationId ? derivations[activeItem.value.derivationId] : undefined,
);
const activeTerm = computed(() => {
  if (!activeDerivation.value || !activeTermKey.value) return null;
  return activeDerivation.value.terms.find((term) => term.key === activeTermKey.value) ?? null;
});
const renderedMainEquation = computed(() => {
  if (!activeDerivation.value) return null;
  return katex.renderToString(activeDerivation.value.equationLatex, {
    throwOnError: false,
    displayMode: true,
  });
});
const cardDescription = computed(() => activeDerivation.value?.teachingDescription ?? activeItem.value?.summary ?? "");
const symbolGlossary = computed(() => activeDerivation.value?.symbolGlossary ?? []);
const sourceStatusLabel = computed(() => {
  const status = activeDerivation.value?.sourceStatus;
  if (status === "derived-here") return "Derived in this module";
  if (status === "imported-from-paper") return "Derived in HQIV paper";
  if (status === "consistency-check") return "Consistency check here";
  return null;
});
const animatedShell = ref(1);
const shellPalette = [
  { m: 1, color: "#ef4444", label: "hot" },
  { m: 2, color: "#f59e0b", label: "warm" },
  { m: 3, color: "#fde047", label: "mild" },
  { m: 4, color: "#22c55e", label: "cool" },
  { m: 5, color: "#3b82f6", label: "colder" },
];
let shellTimer: ReturnType<typeof setInterval> | null = null;

watch(activeCategory, (cat) => {
  const first = categories.find((c) => c.id === cat)?.items[0];
  activeItemId.value = first?.id ?? null;
});
watch(activeItem, () => {
  activeTermKey.value = activeDerivation.value?.terms[0]?.key ?? null;
});
watch(
  () => activeDerivation.value?.id,
  (id) => {
    if (shellTimer) {
      clearInterval(shellTimer);
      shellTimer = null;
    }
    if (id === "lightcone-foundation") {
      animatedShell.value = 1;
      shellTimer = setInterval(() => {
        animatedShell.value = animatedShell.value >= 5 ? 1 : animatedShell.value + 1;
      }, 1100);
    }
  },
  { immediate: true },
);
onMounted(() => {
  if (!shellTimer && activeDerivation.value?.id === "lightcone-foundation") {
    shellTimer = setInterval(() => {
      animatedShell.value = animatedShell.value >= 5 ? 1 : animatedShell.value + 1;
    }, 1100);
  }
});
onBeforeUnmount(() => {
  if (shellTimer) clearInterval(shellTimer);
});

function selectCategory(id: CategoryId) {
  activeCategory.value = id;
}
function goToItem(itemId: string) {
  for (const category of categories) {
    const match = category.items.find((it) => it.id === itemId);
    if (match) {
      activeCategory.value = category.id;
      activeItemId.value = itemId;
      return;
    }
  }
}
function renderStep(latex: string): string {
  return katex.renderToString(latex, { throwOnError: false, displayMode: false });
}
function leanSourceUrl(leanPath: string): string | null {
  const base = import.meta.env.VITE_LEAN_FILE_BASE as string | undefined;
  if (!base || !base.trim()) return null;
  return `${base.replace(/\/$/, "")}/${leanPath}`;
}
</script>

<template>
  <div class="atlas">
    <header class="top">
      <div class="brand">
        <span class="brand-mark">HQIV</span>
        <span class="brand-title">Story Atlas</span>
        <span class="brand-sub">physics derivations (math-first), sourced from `Hqiv/Story`</span>
      </div>
      <nav class="cat-nav" aria-label="Physics areas">
        <button
          v-for="c in categories"
          :key="c.id"
          type="button"
          class="cat-btn"
          :class="{ on: c.id === activeCategory }"
          @click="selectCategory(c.id)"
        >
          {{ c.navLabel }}
        </button>
      </nav>
    </header>

    <div class="body">
      <aside class="rail" :aria-label="activeCategoryDef.headline">
        <h2 class="rail-head">{{ activeCategoryDef.headline }}</h2>
        <p class="rail-intro">{{ activeCategoryDef.intro }}</p>
        <ul class="item-list">
          <li v-for="it in activeCategoryDef.items" :key="it.id">
            <button
              type="button"
              class="item-btn"
              :class="{ on: it.id === activeItemId }"
              @click="activeItemId = it.id"
            >
              <span class="item-title">{{ it.title }}</span>
              <span v-if="it.tentPole" class="tent">tent pole</span>
            </button>
          </li>
        </ul>
      </aside>

      <main class="main">
        <template v-if="activeItem">
          <div class="main-head">
            <h1>{{ activeItem.title }}</h1>
            <span v-if="activeItem.tentPole" class="tent large">Tent pole</span>
            <span v-if="sourceStatusLabel" class="status-pill">{{ sourceStatusLabel }}</span>
          </div>
          <p class="summary">{{ cardDescription }}</p>
          <div class="equation-card">
            <h3
              class="eyebrow"
              :id="activeDerivation?.id === 'lightcone-foundation'
                ? 'chapter-1-core-equation'
                : activeDerivation?.id === 'lightcone-3d-intuition'
                  ? 'chapter-1a-core-equation'
                  : activeDerivation?.id === 'lightcone-simplex-count'
                    ? 'chapter-1b-core-equation'
                    : activeDerivation?.id === 'auxiliary-field-ladder'
                      ? 'chapter-1c-core-equation'
                    : undefined"
            >
              Core equation
            </h3>
            <p v-if="activeDerivation" class="one-line">{{ activeDerivation.oneLine }}</p>
            <div
              v-if="activeDerivation && renderedMainEquation"
              class="equation"
              v-html="renderedMainEquation"
            />
            <p v-if="activeDerivation?.equationPhrase" class="equation-phrase">
              {{ activeDerivation.equationPhrase }}
            </p>
            <p v-else class="pending">
              Math card coming soon for this proof. Lean mapping already categorized.
            </p>
          </div>
          <section v-if="symbolGlossary.length" class="symbols">
            <h3 class="eyebrow">Equation symbols</h3>
            <div class="symbol-row">
              <a
                v-for="sym in symbolGlossary"
                :key="sym.key"
                class="sym sym-op"
                :href="sym.firstIntroduced ? `#${sym.firstIntroduced.anchor}` : undefined"
                :title="`${sym.english ?? sym.label}: ${sym.meaning}`"
              >
                <span class="sym-label">{{ sym.label }}</span>
                <span class="sym-english">{{ sym.english ?? "term" }}</span>
              </a>
            </div>
          </section>
          <section v-if="activeDerivation?.canvas?.type === 'lightcone-shells'" class="canvas-panel">
            <h3 class="eyebrow">{{ activeDerivation.canvas.title }}</h3>
            <svg viewBox="0 0 520 300" role="img" aria-label="Lightcone shell ladder diagram">
              <rect x="0" y="0" width="520" height="300" fill="#0f1722" />
              <line x1="38" y1="245" x2="350" y2="245" stroke="#4b5c70" stroke-width="1.4" />
              <line x1="194" y1="272" x2="194" y2="24" stroke="#4b5c70" stroke-width="1.4" />
              <line x1="194" y1="245" x2="92" y2="143" stroke="#6ee7b7" stroke-width="1.8" />
              <line x1="194" y1="245" x2="296" y2="143" stroke="#6ee7b7" stroke-width="1.8" />
              <circle cx="194" cy="245" r="4" fill="#f472b6" />
              <g fill="#cbd5e1" font-size="10">
                <text x="325" y="261">space x</text>
                <text x="201" y="28">time t</text>
                <text x="201" y="239">origin</text>
              </g>
              <g v-for="shell in shellPalette" :key="shell.m">
                <g
                  v-for="dot in shell.m"
                  :key="`${shell.m}-${dot}`"
                  :opacity="animatedShell === shell.m ? 1 : 0.18"
                >
                  <circle
                    :cx="194 + (dot - (shell.m + 1) / 2) * 11"
                    :cy="225 - shell.m * 20"
                    r="7"
                    :fill="shell.color"
                    stroke="#0b1220"
                    stroke-width="1"
                  />
                </g>
                <text x="303" :y="228 - shell.m * 20" fill="#dbe7f5" font-size="11">
                  m={{ shell.m }}
                </text>
              </g>
              <g fill="#9fb0c6" font-size="10">
                <text x="302" y="42">active shell: m={{ animatedShell }}</text>
              </g>
              <defs>
                <linearGradient id="tempGradient" x1="0%" y1="0%" x2="100%" y2="0%">
                  <stop offset="0%" stop-color="#ef4444" />
                  <stop offset="25%" stop-color="#f59e0b" />
                  <stop offset="50%" stop-color="#fde047" />
                  <stop offset="75%" stop-color="#22c55e" />
                  <stop offset="100%" stop-color="#3b82f6" />
                </linearGradient>
              </defs>
              <rect x="302" y="252" width="184" height="12" rx="6" fill="url(#tempGradient)" />
              <text x="302" y="247" fill="#b7c7dc" font-size="10">temperature (hot → cool)</text>
              <text x="302" y="278" fill="#b7c7dc" font-size="10">dot count = shell index m</text>
            </svg>
            <p class="canvas-caption">{{ activeDerivation.canvas.caption }}</p>
          </section>
          <section v-else-if="activeDerivation?.canvas?.type === 'lightcone-3d-intuition'" class="canvas-panel">
            <h3 class="eyebrow">{{ activeDerivation.canvas.title }}</h3>
            <svg viewBox="0 0 520 300" role="img" aria-label="3D light cone intuition">
              <rect x="0" y="0" width="520" height="300" fill="#0f1722" />
              <polygon points="90,264 260,60 430,264" fill="#143248" opacity="0.42" stroke="#6ee7b7" stroke-width="1.5" />
              <ellipse cx="260" cy="245" rx="115" ry="24" fill="none" stroke="#60a5fa" stroke-width="1.4" opacity="0.85" />
              <ellipse cx="260" cy="210" rx="86" ry="18" fill="none" stroke="#34d399" stroke-width="1.2" opacity="0.85" />
              <ellipse cx="260" cy="178" rx="58" ry="12" fill="none" stroke="#f59e0b" stroke-width="1.2" opacity="0.85" />
              <ellipse cx="260" cy="150" rx="36" ry="8" fill="none" stroke="#ef4444" stroke-width="1.2" opacity="0.85" />
              <circle cx="260" cy="136" r="4" fill="#f472b6" />
              <text x="273" y="140" fill="#dbe7f5" font-size="11">origin (hot)</text>
              <text x="332" y="248" fill="#c5d6eb" font-size="11">shell m=4</text>
              <text x="328" y="213" fill="#c5d6eb" font-size="11">shell m=3</text>
              <text x="323" y="181" fill="#c5d6eb" font-size="11">shell m=2</text>
              <text x="316" y="153" fill="#c5d6eb" font-size="11">shell m=1</text>
              <text x="24" y="265" fill="#9fb0c6" font-size="10">Each shell layer can be discretized by triples (x,y,z) with x+y+z=m.</text>
            </svg>
            <p class="canvas-caption">{{ activeDerivation.canvas.caption }}</p>
          </section>
          <section v-else-if="activeDerivation?.canvas?.type === 'hockey-stick'" class="canvas-panel">
            <h3 class="eyebrow">{{ activeDerivation.canvas.title }}</h3>
            <svg viewBox="0 0 520 280" role="img" aria-label="Hockey stick cumulative growth">
              <rect x="0" y="0" width="520" height="280" fill="#0f1722" />
              <line x1="48" y1="230" x2="485" y2="230" stroke="#4b5c70" stroke-width="1.4" />
              <line x1="48" y1="230" x2="48" y2="34" stroke="#4b5c70" stroke-width="1.4" />
              <polyline fill="none" stroke="#f59e0b" stroke-width="2.5" points="70,218 120,206 170,190 220,168 270,138 320,98 370,46" />
              <polyline fill="none" stroke="#60a5fa" stroke-width="2" points="70,220 120,214 170,206 220,196 270,184 320,170 370,154" opacity="0.9" />
              <g fill="#dbe7f5" font-size="10">
                <text x="458" y="245">shell m</text>
                <text x="10" y="40" transform="rotate(-90 10,40)">count</text>
                <text x="78" y="216">new</text>
                <text x="380" y="46">cumulative</text>
              </g>
            </svg>
            <p class="canvas-caption">{{ activeDerivation.canvas.caption }}</p>
          </section>
          <section v-else-if="activeDerivation?.canvas?.type === 'tvphi'" class="canvas-panel">
            <h3 class="eyebrow">{{ activeDerivation.canvas.title }}</h3>
            <svg viewBox="0 0 520 280" role="img" aria-label="Temperature vs phi over shells">
              <rect x="0" y="0" width="520" height="280" fill="#0f1722" />
              <line x1="48" y1="230" x2="485" y2="230" stroke="#4b5c70" stroke-width="1.4" />
              <line x1="48" y1="230" x2="48" y2="34" stroke="#4b5c70" stroke-width="1.4" />
              <polyline fill="none" stroke="#60a5fa" stroke-width="2.5" points="70,72 120,116 170,148 220,171 270,188 320,200 370,210" />
              <polyline fill="none" stroke="#ef4444" stroke-width="2.5" points="70,214 120,198 170,182 220,166 270,150 320,134 370,118" />
              <g fill="#dbe7f5" font-size="10">
                <text x="458" y="245">shell m</text>
                <text x="10" y="40" transform="rotate(-90 10,40)">value</text>
                <text x="374" y="209">T(m)</text>
                <text x="374" y="118">φ(m)</text>
              </g>
            </svg>
            <p class="canvas-caption">{{ activeDerivation.canvas.caption }}</p>
          </section>
          <section v-else-if="activeDerivation?.canvas?.type === 'reference-shell-map'" class="canvas-panel">
            <h3 class="eyebrow">{{ activeDerivation.canvas.title }}</h3>
            <svg viewBox="0 0 520 220" role="img" aria-label="Reference shell map">
              <rect x="0" y="0" width="520" height="220" fill="#0f1722" />
              <line x1="40" y1="160" x2="480" y2="160" stroke="#4b5c70" stroke-width="1.5" />
              <g fill="#dbe7f5" font-size="11">
                <circle cx="90" cy="160" r="6" fill="#ef4444" />
                <text x="72" y="183">m=1</text>
                <text x="52" y="146">qcdShell</text>
                <circle cx="180" cy="160" r="6" fill="#f59e0b" />
                <text x="164" y="183">m=2</text>
                <circle cx="270" cy="160" r="6" fill="#fde047" />
                <text x="254" y="183">m=3</text>
                <circle cx="360" cy="160" r="7" fill="#22c55e" />
                <text x="344" y="183">m=4</text>
                <text x="324" y="146">referenceM</text>
              </g>
              <path d="M100 120 L350 120" stroke="#60a5fa" stroke-width="2" marker-end="url(#arrowBlue)" />
              <text x="155" y="110" fill="#9fb0c6" font-size="11">stepsFromQCDToLockin = 3</text>
              <text x="48" y="36" fill="#9fb0c6" font-size="10">This anchor map is why later T_QCD / lock-in statements are meaningful rather than arbitrary labels.</text>
              <defs>
                <marker id="arrowBlue" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">
                  <path d="M 0 0 L 10 5 L 0 10 z" fill="#60a5fa" />
                </marker>
              </defs>
            </svg>
            <p class="canvas-caption">{{ activeDerivation.canvas.caption }}</p>
          </section>
          <section v-else-if="activeDerivation?.canvas?.type === 'curvature-stack'" class="canvas-panel">
            <h3 class="eyebrow">{{ activeDerivation.canvas.title }}</h3>
            <svg viewBox="0 0 520 240" role="img" aria-label="Curvature stack">
              <rect x="0" y="0" width="520" height="240" fill="#0f1722" />
              <rect x="40" y="150" width="120" height="56" rx="8" fill="#1f2937" stroke="#334155" />
              <text x="52" y="180" fill="#dbe7f5" font-size="11">cube directions</text>
              <text x="78" y="194" fill="#9fb0c6" font-size="10">(6)</text>
              <rect x="200" y="120" width="120" height="56" rx="8" fill="#1f2937" stroke="#334155" />
              <text x="212" y="150" fill="#dbe7f5" font-size="11">octonion dim</text>
              <text x="248" y="164" fill="#9fb0c6" font-size="10">(7)</text>
              <rect x="360" y="90" width="120" height="56" rx="8" fill="#1f2937" stroke="#334155" />
              <text x="370" y="120" fill="#dbe7f5" font-size="11">curvature norm</text>
              <text x="394" y="134" fill="#9fb0c6" font-size="10">6^7 * sqrt(3)</text>
              <path d="M160 178 L200 148" stroke="#60a5fa" stroke-width="2" />
              <path d="M320 148 L360 118" stroke="#60a5fa" stroke-width="2" />
              <text x="48" y="38" fill="#9fb0c6" font-size="10">No free curvature knob: geometric pieces are stacked before shell imprints are computed.</text>
            </svg>
            <p class="canvas-caption">{{ activeDerivation.canvas.caption }}</p>
          </section>
          <section v-else-if="activeDerivation?.canvas?.type === 'deltaE-shells'" class="canvas-panel">
            <h3 class="eyebrow">{{ activeDerivation.canvas.title }}</h3>
            <svg viewBox="0 0 520 240" role="img" aria-label="DeltaE shells">
              <rect x="0" y="0" width="520" height="240" fill="#0f1722" />
              <line x1="46" y1="196" x2="482" y2="196" stroke="#4b5c70" stroke-width="1.4" />
              <line x1="46" y1="196" x2="46" y2="34" stroke="#4b5c70" stroke-width="1.4" />
              <polyline fill="none" stroke="#f472b6" stroke-width="2.4" points="70,92 120,104 170,120 220,136 270,151 320,164 370,176" />
              <g fill="#dbe7f5" font-size="10">
                <text x="454" y="211">shell m</text>
                <text x="10" y="38" transform="rotate(-90 10,38)">δE(m)</text>
                <text x="82" y="88">high imprint</text>
                <text x="372" y="176">lower imprint</text>
              </g>
            </svg>
            <p class="canvas-caption">{{ activeDerivation.canvas.caption }}</p>
          </section>
          <section v-else-if="activeDerivation?.canvas?.type === 'omega-horizon'" class="canvas-panel">
            <h3 class="eyebrow">{{ activeDerivation.canvas.title }}</h3>
            <svg viewBox="0 0 520 240" role="img" aria-label="Omega horizon dependence">
              <rect x="0" y="0" width="520" height="240" fill="#0f1722" />
              <line x1="46" y1="196" x2="482" y2="196" stroke="#4b5c70" stroke-width="1.4" />
              <line x1="46" y1="196" x2="46" y2="34" stroke="#4b5c70" stroke-width="1.4" />
              <polyline fill="none" stroke="#60a5fa" stroke-width="2.2" points="70,176 130,160 190,144 250,130 310,116 370,104" />
              <polyline fill="none" stroke="#f59e0b" stroke-width="2.2" points="70,164 130,150 190,137 250,126 310,116 370,108" />
              <polyline fill="none" stroke="#f472b6" stroke-width="2.2" points="70,186 130,176 190,167 250,158 310,149 370,140" />
              <g fill="#dbe7f5" font-size="10">
                <text x="454" y="211">shell n</text>
                <text x="10" y="38" transform="rotate(-90 10,38)">Ω_k(n;N)</text>
                <text x="378" y="103">N = referenceM</text>
                <text x="378" y="118">N = later horizon</text>
                <text x="378" y="142">N = earlier horizon</text>
                <text x="56" y="28">dynamic curvature from shell + horizon</text>
              </g>
            </svg>
            <p class="canvas-caption">{{ activeDerivation.canvas.caption }}</p>
          </section>
          <section v-else-if="activeDerivation?.canvas?.type === 'alpha-overlap'" class="canvas-panel">
            <h3 class="eyebrow">{{ activeDerivation.canvas.title }}</h3>
            <svg viewBox="0 0 520 260" role="img" aria-label="Alpha overlap integral intuition">
              <rect x="0" y="0" width="520" height="260" fill="#0f1722" />
              <circle cx="185" cy="130" r="92" fill="#1d4ed822" stroke="#60a5fa" stroke-width="1.5" />
              <circle cx="255" cy="130" r="92" fill="#f59e0b22" stroke="#f59e0b" stroke-width="1.5" />
              <ellipse cx="220" cy="130" rx="58" ry="86" fill="#22c55e33" stroke="#22c55e" stroke-width="1.2" />
              <text x="138" y="38" fill="#bfdbfe" font-size="10">local horizon patch</text>
              <text x="244" y="38" fill="#fde68a" font-size="10">cosmic horizon patch</text>
              <text x="186" y="132" fill="#d9f99d" font-size="11">overlap</text>
              <text x="58" y="216" fill="#cbd5e1" font-size="11">∬ overlap kernel -> geometric coefficient (paper route)</text>
              <text x="58" y="234" fill="#93c5fd" font-size="10">pairs with discrete shell counting identity -> α = 3/5</text>
              <text x="344" y="115" fill="#dbe7f5" font-size="11">f(a,φ)=a/(a+φ/6)</text>
              <text x="332" y="132" fill="#9fb0c6" font-size="10">1/6 from overlap geometry</text>
            </svg>
            <p class="canvas-caption">{{ activeDerivation.canvas.caption }}</p>
          </section>
          <section v-else-if="activeDerivation?.canvas?.type === 'lattice-real-time'" class="canvas-panel">
            <h3 class="eyebrow">{{ activeDerivation.canvas.title }}</h3>
            <svg viewBox="0 0 520 250" role="img" aria-label="Lattice to real-time interface">
              <rect x="0" y="0" width="520" height="250" fill="#0f1722" />
              <rect x="40" y="50" width="190" height="160" rx="8" fill="#172132" stroke="#334155" />
              <rect x="290" y="50" width="190" height="160" rx="8" fill="#132a22" stroke="#335c4a" />
              <text x="66" y="72" fill="#c7d2fe" font-size="11">Discrete lattice layer</text>
              <text x="314" y="72" fill="#bbf7d0" font-size="11">Continuum chart layer</text>
              <g fill="#dbe7f5">
                <circle cx="82" cy="104" r="4" /><circle cx="112" cy="122" r="4" /><circle cx="148" cy="94" r="4" />
                <circle cx="178" cy="138" r="4" /><circle cx="98" cy="160" r="4" /><circle cx="158" cy="176" r="4" />
              </g>
              <g fill="#bbf7d0">
                <circle cx="334" cy="104" r="3" /><circle cx="366" cy="122" r="3" /><circle cx="402" cy="94" r="3" />
                <circle cx="430" cy="136" r="3" /><circle cx="350" cy="160" r="3" /><circle cx="410" cy="176" r="3" />
              </g>
              <path d="M230 130 L290 130" stroke="#60a5fa" stroke-width="2" marker-end="url(#arrowBridge)" />
              <text x="233" y="120" fill="#93c5fd" font-size="10">x_i = a n_i</text>
              <defs>
                <marker id="arrowBridge" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">
                  <path d="M 0 0 L 10 5 L 0 10 z" fill="#60a5fa" />
                </marker>
              </defs>
            </svg>
            <p class="canvas-caption">{{ activeDerivation.canvas.caption }}</p>
          </section>
          <section v-else-if="activeDerivation?.canvas?.type === 'rapidity-aux-bridge'" class="canvas-panel">
            <h3 class="eyebrow">{{ activeDerivation.canvas.title }}</h3>
            <svg viewBox="0 0 520 240" role="img" aria-label="Rapidity auxiliary bridge">
              <rect x="0" y="0" width="520" height="240" fill="#0f1722" />
              <rect x="56" y="70" width="130" height="54" rx="8" fill="#1f2937" stroke="#334155" />
              <text x="72" y="98" fill="#dbe7f5" font-size="11">φ, t, δθ'(m)</text>
              <rect x="212" y="70" width="130" height="54" rx="8" fill="#1f2937" stroke="#334155" />
              <text x="224" y="98" fill="#dbe7f5" font-size="11">rapidity angle</text>
              <rect x="368" y="70" width="110" height="54" rx="8" fill="#1f2937" stroke="#334155" />
              <text x="383" y="98" fill="#dbe7f5" font-size="11">gauge phase</text>
              <path d="M186 97 L212 97" stroke="#60a5fa" stroke-width="2" marker-end="url(#arrowBridge2)" />
              <path d="M342 97 L368 97" stroke="#60a5fa" stroke-width="2" marker-end="url(#arrowBridge2)" />
              <text x="78" y="162" fill="#9fb0c6" font-size="10">i φ t δθ'(m) = i polarAngleFromRapidity(φ,t,m)</text>
              <defs>
                <marker id="arrowBridge2" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">
                  <path d="M 0 0 L 10 5 L 0 10 z" fill="#60a5fa" />
                </marker>
              </defs>
            </svg>
            <p class="canvas-caption">{{ activeDerivation.canvas.caption }}</p>
          </section>
          <section v-else-if="activeDerivation?.canvas?.type === 'so8-closure-map'" class="canvas-panel">
            <h3 class="eyebrow">{{ activeDerivation.canvas.title }}</h3>
            <svg viewBox="0 0 520 260" role="img" aria-label="SO8 closure map">
              <rect x="0" y="0" width="520" height="260" fill="#0f1722" />
              <circle cx="130" cy="128" r="54" fill="#172132" stroke="#334155" />
              <circle cx="260" cy="128" r="64" fill="#1c2435" stroke="#475569" />
              <circle cx="410" cy="128" r="72" fill="#162d24" stroke="#335c4a" />
              <text x="110" y="132" fill="#c7d2fe" font-size="11">G₂</text>
              <text x="238" y="132" fill="#dbe7f5" font-size="11">G₂ ∪ Δ</text>
              <text x="388" y="132" fill="#bbf7d0" font-size="11">SO(8)</text>
              <path d="M182 128 L196 128" stroke="#60a5fa" stroke-width="2" marker-end="url(#arrowBridge3)" />
              <path d="M324 128 L338 128" stroke="#60a5fa" stroke-width="2" marker-end="url(#arrowBridge3)" />
              <text x="52" y="226" fill="#9fb0c6" font-size="10">closure witnesses: skew + bracket span + linear independence (dim 28)</text>
              <defs>
                <marker id="arrowBridge3" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">
                  <path d="M 0 0 L 10 5 L 0 10 z" fill="#60a5fa" />
                </marker>
              </defs>
            </svg>
            <p class="canvas-caption">{{ activeDerivation.canvas.caption }}</p>
          </section>
          <section v-else-if="activeDerivation?.canvas?.type === 'conservation-flow'" class="canvas-panel">
            <h3 class="eyebrow">{{ activeDerivation.canvas.title }}</h3>
            <svg viewBox="0 0 520 240" role="img" aria-label="Conservation flow">
              <rect x="0" y="0" width="520" height="240" fill="#0f1722" />
              <rect x="40" y="90" width="120" height="52" rx="8" fill="#1f2937" stroke="#334155" />
              <rect x="200" y="90" width="120" height="52" rx="8" fill="#1f2937" stroke="#334155" />
              <rect x="360" y="90" width="120" height="52" rx="8" fill="#1f2937" stroke="#334155" />
              <text x="58" y="118" fill="#dbe7f5" font-size="11">light-cone O count</text>
              <text x="224" y="118" fill="#dbe7f5" font-size="11">HQVM metric</text>
              <text x="376" y="118" fill="#dbe7f5" font-size="11">phase conserved</text>
              <path d="M160 116 L200 116" stroke="#60a5fa" stroke-width="2" />
              <path d="M320 116 L360 116" stroke="#60a5fa" stroke-width="2" />
            </svg>
            <p class="canvas-caption">{{ activeDerivation.canvas.caption }}</p>
          </section>
          <section v-else-if="activeDerivation?.canvas?.type === 'action-stationarity'" class="canvas-panel">
            <h3 class="eyebrow">{{ activeDerivation.canvas.title }}</h3>
            <svg viewBox="0 0 520 240" role="img" aria-label="Action stationarity">
              <rect x="0" y="0" width="520" height="240" fill="#0f1722" />
              <rect x="42" y="58" width="150" height="60" rx="8" fill="#1f2937" stroke="#334155" />
              <rect x="206" y="58" width="150" height="60" rx="8" fill="#1f2937" stroke="#334155" />
              <rect x="370" y="58" width="110" height="60" rx="8" fill="#1f2937" stroke="#334155" />
              <text x="74" y="92" fill="#dbe7f5" font-size="11">S_O Maxwell</text>
              <text x="230" y="92" fill="#dbe7f5" font-size="11">S_grav HQVM</text>
              <text x="398" y="92" fill="#dbe7f5" font-size="11">S_total</text>
              <path d="M192 88 L206 88" stroke="#60a5fa" stroke-width="2" />
              <path d="M356 88 L370 88" stroke="#60a5fa" stroke-width="2" />
              <text x="56" y="168" fill="#9fb0c6" font-size="10">EL_O = 0 and S_grav = 0 generate the packaged equations.</text>
            </svg>
            <p class="canvas-caption">{{ activeDerivation.canvas.caption }}</p>
          </section>
          <section v-else-if="activeDerivation?.canvas?.type === 'covariant-balance'" class="canvas-panel">
            <h3 class="eyebrow">{{ activeDerivation.canvas.title }}</h3>
            <svg viewBox="0 0 520 240" role="img" aria-label="Covariant balance">
              <rect x="0" y="0" width="520" height="240" fill="#0f1722" />
              <line x1="60" y1="190" x2="460" y2="190" stroke="#4b5c70" stroke-width="1.2" />
              <text x="62" y="182" fill="#dbe7f5" font-size="10">1/sqrt(-g) sum_mu sqrt(-g) F^{mu nu}</text>
              <text x="62" y="78" fill="#9fb0c6" font-size="10">HQVM inverse metric + Christoffel-aware packaging</text>
              <rect x="70" y="96" width="180" height="52" rx="8" fill="#1f2937" stroke="#334155" />
              <rect x="280" y="96" width="180" height="52" rx="8" fill="#1f2937" stroke="#334155" />
              <text x="90" y="125" fill="#dbe7f5" font-size="11">metric-raised F</text>
              <text x="302" y="125" fill="#dbe7f5" font-size="11">covariant residual</text>
              <path d="M250 122 L280 122" stroke="#60a5fa" stroke-width="2" />
            </svg>
            <p class="canvas-caption">{{ activeDerivation.canvas.caption }}</p>
          </section>
          <section v-else-if="activeDerivation?.canvas?.type === 'plasma-bridge'" class="canvas-panel">
            <h3 class="eyebrow">{{ activeDerivation.canvas.title }}</h3>
            <svg viewBox="0 0 520 240" role="img" aria-label="Plasma bridge">
              <rect x="0" y="0" width="520" height="240" fill="#0f1722" />
              <rect x="44" y="90" width="140" height="56" rx="8" fill="#1f2937" stroke="#334155" />
              <rect x="208" y="90" width="140" height="56" rx="8" fill="#1f2937" stroke="#334155" />
              <rect x="372" y="90" width="104" height="56" rx="8" fill="#1f2937" stroke="#334155" />
              <text x="63" y="122" fill="#dbe7f5" font-size="11">J_src (generic)</text>
              <text x="224" y="122" fill="#dbe7f5" font-size="11">J_O_plasma</text>
              <text x="390" y="122" fill="#dbe7f5" font-size="11">EL slot</text>
              <path d="M184 118 L208 118" stroke="#60a5fa" stroke-width="2" />
              <path d="M348 118 L372 118" stroke="#60a5fa" stroke-width="2" />
              <text x="66" y="64" fill="#9fb0c6" font-size="10">Only source specialization changes; EL structure remains fixed.</text>
            </svg>
            <p class="canvas-caption">{{ activeDerivation.canvas.caption }}</p>
          </section>
          <section v-else-if="activeDerivation?.canvas?.type === 'continuum-bridge'" class="canvas-panel">
            <h3 class="eyebrow">{{ activeDerivation.canvas.title }}</h3>
            <svg viewBox="0 0 520 240" role="img" aria-label="Continuum gradient bridge">
              <rect x="0" y="0" width="520" height="240" fill="#0f1722" />
              <rect x="42" y="90" width="132" height="56" rx="8" fill="#1f2937" stroke="#334155" />
              <rect x="194" y="90" width="144" height="56" rx="8" fill="#1f2937" stroke="#334155" />
              <rect x="358" y="90" width="120" height="56" rx="8" fill="#1f2937" stroke="#334155" />
              <text x="64" y="122" fill="#dbe7f5" font-size="11">grad_phi</text>
              <text x="204" y="122" fill="#dbe7f5" font-size="11">coordsGradient</text>
              <text x="372" y="122" fill="#dbe7f5" font-size="11">g^nu mu d_mu phi</text>
              <path d="M174 118 L194 118" stroke="#60a5fa" stroke-width="2" />
              <path d="M338 118 L358 118" stroke="#60a5fa" stroke-width="2" />
              <text x="58" y="64" fill="#9fb0c6" font-size="10">Same EL/action slots, upgraded gradient semantics.</text>
            </svg>
            <p class="canvas-caption">{{ activeDerivation.canvas.caption }}</p>
          </section>
          <section v-else-if="activeDerivation?.canvas?.type === 'mass-layers'" class="canvas-panel">
            <h3 class="eyebrow">{{ activeDerivation.canvas.title }}</h3>
            <svg viewBox="0 0 520 240" role="img" aria-label="Mass layer ordering">
              <rect x="0" y="0" width="520" height="240" fill="#0f1722" />
              <rect x="64" y="142" width="120" height="48" rx="8" fill="#1f2937" stroke="#334155" />
              <rect x="200" y="112" width="120" height="48" rx="8" fill="#1f2937" stroke="#334155" />
              <rect x="336" y="82" width="120" height="48" rx="8" fill="#1f2937" stroke="#334155" />
              <text x="90" y="170" fill="#dbe7f5" font-size="11">neutrino l=1</text>
              <text x="220" y="140" fill="#dbe7f5" font-size="11">charged l=2</text>
              <text x="366" y="110" fill="#dbe7f5" font-size="11">quark l=3</text>
              <path d="M184 160 L200 136" stroke="#60a5fa" stroke-width="2" />
              <path d="M320 130 L336 106" stroke="#60a5fa" stroke-width="2" />
              <text x="66" y="58" fill="#9fb0c6" font-size="10">intrinsicWaveComplexity = l^2 provides strict ordering scaffold.</text>
            </svg>
            <p class="canvas-caption">{{ activeDerivation.canvas.caption }}</p>
          </section>
          <section v-else-if="activeDerivation?.canvas?.type === 'forces-map'" class="canvas-panel">
            <h3 class="eyebrow">{{ activeDerivation.canvas.title }}</h3>
            <svg viewBox="0 0 520 240" role="img" aria-label="Forces sector map and units">
              <rect x="0" y="0" width="520" height="240" fill="#0f1722" />
              <rect x="46" y="74" width="120" height="56" rx="8" fill="#1f2937" stroke="#334155" />
              <rect x="198" y="74" width="120" height="56" rx="8" fill="#1f2937" stroke="#334155" />
              <rect x="350" y="74" width="120" height="56" rx="8" fill="#1f2937" stroke="#334155" />
              <text x="74" y="106" fill="#dbe7f5" font-size="11">a=0 -> EM</text>
              <text x="215" y="106" fill="#dbe7f5" font-size="11">a=1..3 -> Weak</text>
              <text x="365" y="106" fill="#dbe7f5" font-size="11">a>=4 -> Strong</text>
              <line x1="60" y1="176" x2="460" y2="176" stroke="#4b5c70" stroke-width="1.3" />
              <text x="66" y="168" fill="#9fb0c6" font-size="10">Residual_metric = 0 iff Residual_SI = 0</text>
            </svg>
            <p class="canvas-caption">{{ activeDerivation.canvas.caption }}</p>
          </section>
          <section v-else-if="activeDerivation?.canvas?.type === 'thermo-laws'" class="canvas-panel">
            <h3 class="eyebrow">{{ activeDerivation.canvas.title }}</h3>
            <svg viewBox="0 0 520 250" role="img" aria-label="Thermodynamics laws capstone">
              <rect x="0" y="0" width="520" height="250" fill="#0f1722" />
              <rect x="40" y="92" width="130" height="54" rx="8" fill="#1f2937" stroke="#334155" />
              <rect x="196" y="62" width="130" height="54" rx="8" fill="#1f2937" stroke="#334155" />
              <rect x="352" y="32" width="130" height="54" rx="8" fill="#1f2937" stroke="#334155" />
              <text x="70" y="124" fill="#dbe7f5" font-size="11">Zeroth law</text>
              <text x="230" y="94" fill="#dbe7f5" font-size="11">First law</text>
              <text x="386" y="64" fill="#dbe7f5" font-size="11">Second law</text>
              <path d="M170 116 L196 89" stroke="#60a5fa" stroke-width="2" />
              <path d="M326 89 L352 58" stroke="#60a5fa" stroke-width="2" />
              <text x="52" y="184" fill="#9fb0c6" font-size="10">T(m)=T(n)</text>
              <text x="188" y="184" fill="#9fb0c6" font-size="10">sum T_cons * w = T_ref</text>
              <text x="348" y="184" fill="#9fb0c6" font-size="10">sum u Delta u <= 0</text>
              <text x="48" y="210" fill="#9fb0c6" font-size="10">Capstone is derived from ladder + discrete heat identities, not postulated constants.</text>
            </svg>
            <p class="canvas-caption">{{ activeDerivation.canvas.caption }}</p>
          </section>
          <section v-else-if="activeDerivation?.canvas?.type === 'algebra-ladder'" class="canvas-panel">
            <h3 class="eyebrow">{{ activeDerivation.canvas.title }}</h3>
            <svg viewBox="0 0 520 240" role="img" aria-label="Algebra ladder">
              <rect x="0" y="0" width="520" height="240" fill="#0f1722" />
              <rect x="50" y="90" width="90" height="50" rx="8" fill="#1f2937" stroke="#334155" />
              <rect x="170" y="90" width="90" height="50" rx="8" fill="#1f2937" stroke="#334155" />
              <rect x="290" y="90" width="90" height="50" rx="8" fill="#1f2937" stroke="#334155" />
              <rect x="410" y="90" width="60" height="50" rx="8" fill="#1f2937" stroke="#334155" />
              <text x="85" y="120" fill="#dbe7f5" font-size="11">R</text>
              <text x="205" y="120" fill="#dbe7f5" font-size="11">C</text>
              <text x="325" y="120" fill="#dbe7f5" font-size="11">H</text>
              <text x="432" y="120" fill="#dbe7f5" font-size="11">O</text>
              <path d="M140 115 L170 115" stroke="#60a5fa" stroke-width="2" />
              <path d="M260 115 L290 115" stroke="#60a5fa" stroke-width="2" />
              <path d="M380 115 L410 115" stroke="#60a5fa" stroke-width="2" />
              <text x="54" y="172" fill="#9fb0c6" font-size="10">commutative/associative -> noncommutative -> nonassociative</text>
            </svg>
            <p class="canvas-caption">{{ activeDerivation.canvas.caption }}</p>
          </section>
          <section v-else-if="activeDerivation?.canvas?.type === 'fano-wheel'" class="canvas-panel">
            <h3 class="eyebrow">{{ activeDerivation.canvas.title }}</h3>
            <svg viewBox="0 0 520 260" role="img" aria-label="Fano plane wheel">
              <rect x="0" y="0" width="520" height="260" fill="#0f1722" />
              <circle cx="260" cy="130" r="78" fill="none" stroke="#60a5fa" stroke-width="1.4" />
              <circle cx="260" cy="58" r="6" fill="#f59e0b" />
              <circle cx="198" cy="92" r="6" fill="#f59e0b" />
              <circle cx="322" cy="92" r="6" fill="#f59e0b" />
              <circle cx="184" cy="166" r="6" fill="#f59e0b" />
              <circle cx="336" cy="166" r="6" fill="#f59e0b" />
              <circle cx="260" cy="206" r="6" fill="#f59e0b" />
              <circle cx="260" cy="130" r="6" fill="#22c55e" />
              <line x1="260" y1="58" x2="184" y2="166" stroke="#34d399" />
              <line x1="260" y1="58" x2="336" y2="166" stroke="#34d399" />
              <line x1="184" y1="166" x2="336" y2="166" stroke="#34d399" />
              <text x="52" y="236" fill="#9fb0c6" font-size="10">Oriented triples encode unit products; reversing order flips sign.</text>
            </svg>
            <p class="canvas-caption">{{ activeDerivation.canvas.caption }}</p>
          </section>
          <section v-else-if="activeDerivation?.canvas?.type === 'associator-map'" class="canvas-panel">
            <h3 class="eyebrow">{{ activeDerivation.canvas.title }}</h3>
            <svg viewBox="0 0 520 240" role="img" aria-label="Associator map">
              <rect x="0" y="0" width="520" height="240" fill="#0f1722" />
              <rect x="70" y="68" width="150" height="50" rx="8" fill="#1f2937" stroke="#334155" />
              <rect x="300" y="68" width="150" height="50" rx="8" fill="#1f2937" stroke="#334155" />
              <text x="98" y="98" fill="#dbe7f5" font-size="11">(xy)z</text>
              <text x="332" y="98" fill="#dbe7f5" font-size="11">x(yz)</text>
              <path d="M220 93 L300 93" stroke="#60a5fa" stroke-width="2" />
              <text x="182" y="148" fill="#f472b6" font-size="11">[x,y,z] = (xy)z - x(yz)</text>
              <text x="64" y="182" fill="#9fb0c6" font-size="10">Nonzero associator means grouping matters in octonion multiplication.</text>
            </svg>
            <p class="canvas-caption">{{ activeDerivation.canvas.caption }}</p>
          </section>
          <section v-else-if="activeDerivation?.canvas?.type === 'phase-anchor-start'" class="canvas-panel">
            <h3 class="eyebrow">{{ activeDerivation.canvas.title }}</h3>
            <svg viewBox="0 0 520 240" role="img" aria-label="Phase anchor at start">
              <rect x="0" y="0" width="520" height="240" fill="#0f1722" />
              <line x1="56" y1="188" x2="470" y2="188" stroke="#4b5c70" stroke-width="1.3" />
              <line x1="56" y1="188" x2="56" y2="34" stroke="#4b5c70" stroke-width="1.3" />
              <circle cx="56" cy="188" r="5" fill="#22c55e" />
              <text x="66" y="182" fill="#dbe7f5" font-size="11">δθ′(0)=0</text>
              <path d="M56 188 C150 160, 240 140, 330 120" stroke="#60a5fa" fill="none" stroke-width="2" opacity="0.6" />
              <text x="60" y="222" fill="#9fb0c6" font-size="10">Start anchor fixes the left endpoint in phase-time space.</text>
            </svg>
            <p class="canvas-caption">{{ activeDerivation.canvas.caption }}</p>
          </section>
          <section v-else-if="activeDerivation?.canvas?.type === 'phase-anchor-cycle'" class="canvas-panel">
            <h3 class="eyebrow">{{ activeDerivation.canvas.title }}</h3>
            <svg viewBox="0 0 520 240" role="img" aria-label="Phase anchor at cycle endpoint">
              <rect x="0" y="0" width="520" height="240" fill="#0f1722" />
              <line x1="56" y1="188" x2="470" y2="188" stroke="#4b5c70" stroke-width="1.3" />
              <line x1="56" y1="188" x2="56" y2="34" stroke="#4b5c70" stroke-width="1.3" />
              <path d="M56 188 C170 160, 290 112, 440 52" stroke="#60a5fa" fill="none" stroke-width="2" />
              <circle cx="440" cy="52" r="5" fill="#f59e0b" />
              <text x="302" y="44" fill="#dbe7f5" font-size="11">δθ′(2π/ϕ)=2π</text>
              <line x1="440" y1="52" x2="440" y2="188" stroke="#334155" stroke-dasharray="4 4" />
              <text x="58" y="222" fill="#9fb0c6" font-size="10">Right endpoint is pinned to one full phase turn (2π).</text>
            </svg>
            <p class="canvas-caption">{{ activeDerivation.canvas.caption }}</p>
          </section>
          <section v-else-if="activeDerivation?.canvas?.type === 'phase-band'" class="canvas-panel">
            <h3 class="eyebrow">{{ activeDerivation.canvas.title }}</h3>
            <svg viewBox="0 0 520 240" role="img" aria-label="Bounded phase band">
              <rect x="0" y="0" width="520" height="240" fill="#0f1722" />
              <line x1="56" y1="188" x2="470" y2="188" stroke="#4b5c70" stroke-width="1.3" />
              <line x1="56" y1="52" x2="470" y2="52" stroke="#4b5c70" stroke-width="1.3" />
              <rect x="56" y="52" width="414" height="136" fill="#22c55e22" stroke="#22c55e55" />
              <path d="M56 188 C130 170, 220 126, 300 110 C360 98, 410 78, 470 52" stroke="#60a5fa" fill="none" stroke-width="2.2" />
              <text x="64" y="46" fill="#dbe7f5" font-size="11">upper rail: 2π</text>
              <text x="64" y="202" fill="#dbe7f5" font-size="11">lower rail: 0</text>
              <text x="58" y="222" fill="#9fb0c6" font-size="10">Trajectory stays between rails for all intermediate times.</text>
            </svg>
            <p class="canvas-caption">{{ activeDerivation.canvas.caption }}</p>
          </section>
          <div v-if="!symbolGlossary.length && activeItem.tags?.length" class="tags">
            <span v-for="t in activeItem.tags" :key="t" class="tag">{{ t }}</span>
          </div>
          <section v-if="activeDerivation" class="terms">
            <h3 class="eyebrow">Terms you can inspect</h3>
            <div class="term-buttons">
              <button
                v-for="term in activeDerivation.terms"
                :key="term.key"
                type="button"
                class="term-btn"
                :class="{ on: term.key === activeTermKey }"
                @mouseenter="activeTermKey = term.key"
                @focus="activeTermKey = term.key"
                @click="activeTermKey = term.key"
              >
                {{ term.label }}
              </button>
            </div>
            <div v-if="activeTerm" class="term-panel">
              <h4>{{ activeTerm.label }}</h4>
              <p><strong>Meaning:</strong> {{ activeTerm.meaning }}</p>
              <p><strong>Derived from:</strong> {{ activeTerm.derivedFrom }}</p>
            </div>
          </section>
          <section v-if="activeDerivation" class="steps">
            <h3 class="eyebrow">Derivation steps</h3>
            <ol>
              <li v-for="step in activeDerivation.steps" :key="step.title">
                <p class="step-title">{{ step.title }}</p>
                <div class="step-math" v-html="renderStep(step.latex)" />
                <p class="step-note">{{ step.note }}</p>
              </li>
            </ol>
          </section>
          <details class="lean">
            <summary class="eyebrow">Formal source (Lean provenance)</summary>
            <code class="path mono">{{ activeItem.leanPath }}</code>
            <p v-if="activeDerivation?.formalSource?.leanSymbol" class="symbol-line">
              Symbol: <code class="mono">{{ activeDerivation.formalSource.leanSymbol }}</code>
            </p>
            <pre v-if="activeDerivation?.formalSource?.snippet" class="lean-snippet"><code>{{ activeDerivation.formalSource.snippet }}</code></pre>
            <p v-if="!leanSourceUrl(activeItem.leanPath)" class="hint">
              Set
              <code class="mono">VITE_LEAN_FILE_BASE</code>
              (e.g. your GitHub
              <code class="mono">…/blob/main/</code>
              URL) in
              <code class="mono">.env</code>
              to enable “open in browser” links.
            </p>
            <a
              v-else
              class="open"
              :href="leanSourceUrl(activeItem.leanPath)!"
              target="_blank"
              rel="noreferrer"
            >Open file in remote tree</a>
            <div v-if="activeDerivation?.paperReference" class="paper-ref">
              <p class="symbol-line">
                Paper derivation reference:
                <code class="mono">{{ activeDerivation.paperReference.path }}</code>
              </p>
              <p class="hint">{{ activeDerivation.paperReference.sectionHint }} — {{ activeDerivation.paperReference.note }}</p>
            </div>
          </details>
          <section v-if="activeDerivation?.nextLeanStep" class="next-step">
            <h3 class="eyebrow">Next logical Lean step</h3>
            <button type="button" class="next-btn" @click="goToItem(activeDerivation.nextLeanStep.itemId)">
              {{ activeDerivation.nextLeanStep.label }}
            </button>
          </section>
        </template>
        <p v-else class="empty">Select an entry from the list.</p>
      </main>
    </div>
  </div>
</template>

<style scoped>
.atlas {
  min-height: 100%;
  display: flex;
  flex-direction: column;
}

.top {
  flex-shrink: 0;
  min-height: var(--nav-h);
  padding: 0 1rem;
  display: flex;
  flex-wrap: wrap;
  align-items: center;
  justify-content: space-between;
  gap: 0.75rem 1.25rem;
  border-bottom: 1px solid var(--border);
  background: linear-gradient(168deg, #101820 0%, var(--bg) 72%);
}

.brand {
  display: flex;
  flex-wrap: wrap;
  align-items: baseline;
  gap: 0.5rem 0.75rem;
  padding: 0.65rem 0;
}

.brand-mark {
  font-weight: 700;
  letter-spacing: 0.06em;
  color: var(--accent);
  font-size: 0.95rem;
}

.brand-title {
  font-weight: 600;
  font-size: 1.05rem;
}

.brand-sub {
  font-size: 0.78rem;
  color: var(--muted);
  width: 100%;
}

@media (min-width: 720px) {
  .brand-sub {
    width: auto;
  }
}

.cat-nav {
  display: flex;
  flex-wrap: wrap;
  gap: 0.2rem;
  padding: 0.35rem 0;
}

.cat-btn {
  font: inherit;
  font-size: 0.82rem;
  font-weight: 500;
  padding: 0.45rem 0.7rem;
  border-radius: 8px;
  border: 1px solid transparent;
  background: transparent;
  color: var(--muted);
  cursor: pointer;
  transition:
    color 0.15s,
    background 0.15s,
    border-color 0.15s;
}

.cat-btn:hover {
  color: var(--text);
  background: var(--panel2);
}

.cat-btn.on {
  color: var(--text);
  background: var(--panel);
  border-color: var(--accent-dim);
  color: var(--accent);
}

.body {
  flex: 1;
  display: grid;
  grid-template-columns: minmax(260px, 340px) 1fr;
  min-height: 0;
}

@media (max-width: 800px) {
  .body {
    grid-template-columns: 1fr;
  }
}

.rail {
  border-right: 1px solid var(--border);
  background: var(--panel);
  padding: 1.1rem 1rem 1.5rem;
  overflow-y: auto;
}

@media (max-width: 800px) {
  .rail {
    border-right: none;
    border-bottom: 1px solid var(--border);
    max-height: 42vh;
  }
}

.rail-head {
  font-size: 0.95rem;
  font-weight: 600;
  margin: 0 0 0.5rem;
  line-height: 1.35;
  letter-spacing: -0.02em;
}

.rail-intro {
  margin: 0 0 1rem;
  font-size: 0.82rem;
  color: var(--muted);
  line-height: 1.45;
}

.item-list {
  list-style: none;
  margin: 0;
  padding: 0;
  display: flex;
  flex-direction: column;
  gap: 0.35rem;
}

.item-btn {
  width: 100%;
  text-align: left;
  font: inherit;
  font-size: 0.8rem;
  padding: 0.55rem 0.65rem;
  border-radius: 8px;
  border: 1px solid var(--border);
  background: var(--panel2);
  color: var(--text);
  cursor: pointer;
  display: flex;
  flex-wrap: wrap;
  align-items: center;
  justify-content: space-between;
  gap: 0.35rem;
  transition:
    border-color 0.15s,
    background 0.15s;
}

.item-btn:hover {
  border-color: #3d4d60;
}

.item-btn.on {
  border-color: var(--accent);
  background: #152028;
}

.item-title {
  flex: 1;
  min-width: 0;
  line-height: 1.35;
}

.tent {
  flex-shrink: 0;
  font-size: 0.62rem;
  font-weight: 600;
  text-transform: uppercase;
  letter-spacing: 0.06em;
  color: var(--tent);
  border: 1px solid #f472b655;
  padding: 0.12rem 0.35rem;
  border-radius: 4px;
}

.tent.large {
  font-size: 0.68rem;
}

.status-pill {
  font-size: 0.68rem;
  border: 1px solid #60a5fa66;
  color: #93c5fd;
  border-radius: 999px;
  padding: 0.2rem 0.45rem;
}

.main {
  padding: 1.35rem 1.5rem 2.5rem;
  overflow-y: auto;
}

.main-head {
  display: flex;
  flex-wrap: wrap;
  align-items: center;
  gap: 0.65rem 1rem;
  margin-bottom: 0.75rem;
}

.main h1 {
  margin: 0;
  font-size: 1.35rem;
  font-weight: 600;
  letter-spacing: -0.02em;
  line-height: 1.25;
}

.summary {
  margin: 0 0 1rem;
  max-width: 52rem;
  font-size: 0.95rem;
  color: #c5ced9;
  line-height: 1.55;
}

.equation-card,
.terms,
.steps {
  max-width: 52rem;
  margin-bottom: 1rem;
  padding: 1rem 1.1rem;
  border-radius: 10px;
  border: 1px solid var(--border);
  background: var(--panel);
}

.eyebrow {
  margin: 0 0 0.55rem;
  font-size: 0.72rem;
  text-transform: uppercase;
  letter-spacing: 0.08em;
  color: var(--muted);
  font-weight: 600;
}

.one-line {
  margin: 0 0 0.8rem;
  color: #cfd9e5;
}

.equation {
  overflow-x: auto;
  border: 1px solid var(--border);
  border-radius: 8px;
  padding: 0.8rem;
  background: #111923;
}

.equation-phrase {
  margin: 0.75rem 0 0;
  color: #d6e2f0;
  font-size: 0.9rem;
}

.pending {
  margin: 0;
  color: var(--muted);
}

.tags {
  display: flex;
  flex-wrap: wrap;
  gap: 0.35rem;
  margin-bottom: 1.5rem;
}

.tag {
  font-size: 0.72rem;
  padding: 0.2rem 0.45rem;
  border-radius: 999px;
  background: #1e2836;
  color: var(--muted);
  border: 1px solid var(--border);
}

.symbols,
.canvas-panel {
  max-width: 52rem;
  margin-bottom: 1rem;
  padding: 1rem 1.1rem;
  border-radius: 10px;
  border: 1px solid var(--border);
  background: var(--panel);
}

.symbol-row {
  display: flex;
  flex-wrap: wrap;
  gap: 0.55rem;
}

.sym {
  display: inline-flex;
  align-items: center;
  gap: 0.45rem;
  padding: 0.32rem 0.58rem;
  border-radius: 999px;
  border: 1px solid var(--border);
  background: #182434;
  color: var(--text);
  text-decoration: none;
}

.sym:hover {
  border-color: var(--accent);
}

.sym-label {
  font-family: "IBM Plex Mono", ui-monospace, monospace;
  font-size: 0.83rem;
}

.sym-english {
  font-size: 0.75rem;
  color: #9fb0c6;
}

.canvas-panel svg {
  width: 100%;
  max-width: 680px;
  border-radius: 8px;
  border: 1px solid var(--border);
  background: #0f1722;
}

.canvas-caption {
  margin: 0.55rem 0 0;
  color: #c5ced9;
  font-size: 0.86rem;
}

.term-buttons {
  display: flex;
  flex-wrap: wrap;
  gap: 0.45rem;
  margin-bottom: 0.8rem;
}

.term-btn {
  border: 1px solid var(--border);
  border-radius: 999px;
  background: #1a2432;
  color: var(--text);
  padding: 0.28rem 0.65rem;
  cursor: pointer;
  font-size: 0.8rem;
}

.term-btn.on {
  border-color: var(--accent);
  color: var(--accent);
}

.term-panel {
  border: 1px solid var(--border);
  border-radius: 8px;
  background: #121b26;
  padding: 0.7rem 0.8rem;
}

.term-panel h4 {
  margin: 0 0 0.35rem;
  font-size: 0.95rem;
}

.term-panel p {
  margin: 0.25rem 0;
  color: #cbd5e1;
  font-size: 0.88rem;
}

.steps ol {
  margin: 0;
  padding-left: 1.1rem;
  display: grid;
  gap: 0.9rem;
}

.step-title {
  margin: 0 0 0.35rem;
  font-weight: 600;
}

.step-math {
  overflow-x: auto;
  border-left: 2px solid var(--accent-dim);
  padding-left: 0.7rem;
  margin-bottom: 0.35rem;
}

.step-note {
  margin: 0;
  color: #c5ced9;
}

.lean {
  max-width: 52rem;
  padding: 1rem 1.1rem;
  border-radius: 10px;
  border: 1px solid var(--border);
  background: var(--panel);
}

.lean summary {
  cursor: pointer;
  list-style: none;
}

.lean summary::-webkit-details-marker {
  display: none;
}

.lean h3 {
  margin: 0 0 0.5rem;
  font-size: 0.72rem;
  text-transform: uppercase;
  letter-spacing: 0.08em;
  color: var(--muted);
  font-weight: 600;
}

.path {
  display: block;
  word-break: break-all;
  color: var(--accent);
  font-size: 0.85rem;
}

.symbol-line {
  margin: 0.55rem 0 0.4rem;
  color: #d3dceb;
  font-size: 0.84rem;
}

.lean-snippet {
  margin: 0 0 0.6rem;
  padding: 0.75rem;
  border-radius: 8px;
  border: 1px solid var(--border);
  background: #111923;
  color: #dbe7f5;
  overflow-x: auto;
  font-size: 0.8rem;
  line-height: 1.45;
}

.paper-ref {
  margin-top: 0.45rem;
}

.hint {
  margin: 0.75rem 0 0;
  font-size: 0.82rem;
  color: var(--muted);
}

.open {
  display: inline-block;
  margin-top: 0.75rem;
  font-size: 0.88rem;
  font-weight: 500;
}

.next-step {
  max-width: 52rem;
  margin-top: 1rem;
  padding: 1rem 1.1rem;
  border-radius: 10px;
  border: 1px solid var(--border);
  background: var(--panel);
}

.next-btn {
  border: 1px solid var(--accent-dim);
  color: var(--accent);
  background: #13202a;
  padding: 0.5rem 0.72rem;
  border-radius: 8px;
  cursor: pointer;
  font: inherit;
  font-size: 0.86rem;
}

.empty {
  color: var(--muted);
}
</style>
