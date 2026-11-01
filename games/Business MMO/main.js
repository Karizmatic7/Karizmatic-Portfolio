'use strict';

// ---------- Config ----------
const CENTER = [-82.595, 34.828];
const BBOX = '34.825,-82.600,34.832,-82.590'; // south,west,north,east
const MIRRORS = [
  'https://overpass-api.de/api/interpreter',
  'https://overpass.private.coffee/api/interpreter',
  'https://maps.mail.ru/osm/tools/overpass/api/interpreter',
  'https://overpass.openstreetmap.ru/api/interpreter'
];
const QUERY = `[out:json][timeout:25];
  (way["building"](${BBOX}); relation["building"](${BBOX}); way["highway"](${BBOX}););
  out body; >; out skel qt;
  node["highway"~"^(traffic_signals|stop|give_way|crossing)$"](${BBOX});
  out body;`;
const CACHE_KEY = 'ecosim-osm-' + BBOX; // real data is saved after one success so reloads don't hit Overpass
const TILE_M = 2; // one interior tile = 2 m x 2 m of real floor
const ZONES = {
  industrial:  { color: '#8d6e63', rate: 120 }, // $ per m2
  commercial:  { color: '#5c6bc0', rate: 200 },
  residential: { color: '#607d8b', rate: 90 },
  other:       { color: '#546e7a', rate: 60 }
};
const TIERS = [[80, 'Shed'], [250, 'Shop'], [1000, 'Workshop'], [4000, 'Factory'], [Infinity, 'Plant']];
// Machines no longer pass goods on their own: someone (a paid worker) or something (a belt) has to move them.
const MACH = {
  E: { name: 'Extractor', cost: 200, color: 0xffa726 }, // makes ore
  S: { name: 'Smelter', cost: 500, color: 0xe53935 },   // 2 ore -> 1 metal
  C: { name: 'Crate', cost: 100, color: 0x8d6e63 }      // stores goods in the building's stock
};
const OUTPUT = { E: 'ore', S: 'metal' };
const ACCEPTS = { S: ['ore'], C: ['ore', 'metal'] };
const PRICES = { ore: 2, metal: 9 }; // test-buyer prices only; real prices will come from player listings
const SELL_RATE = 0.8; // selling a property returns 80% of its current price; the rest is a transaction cost
const HIRE_COST = 300, WAGE = 0.3, SPEED = 1.8, BELT_COST = 50; // $, $ per second per worker, tiles/s, $ per belt tile
let tool = 'E', pending = null;
const EMPTY = { type: 'FeatureCollection', features: [] };

// ---------- Saved state (swap for a server later) ----------
const SAVE_KEY = 'ecosim-save-v1';
let save = { cash: 50000, owned: {}, layouts: {}, stock: {}, fac: {} };
try { Object.assign(save, JSON.parse(localStorage.getItem(SAVE_KEY)) || {}); } catch (e) { /* fresh save */ }
save.stock = save.stock || {};
save.fac = save.fac || {};
if (save.gridV !== 2) { // floor grids are now aligned to each building, so old machine positions no longer apply
  save.fac = {}; save.layouts = {}; save.stock = {}; save.gridV = 2;
}
for (const id in save.layouts) { // carry machines over from older saves
  if (!save.fac[id]) save.fac[id] = { m: Array.isArray(save.layouts[id]) ? {} : save.layouts[id], routes: [], workers: [], nid: 1 };
}
const persist = () => { try { localStorage.setItem(SAVE_KEY, JSON.stringify(save)); } catch (e) { /* ignore */ } };

const TEST_MODE = true; // true = start with $1,000,000,000 so you can test freely; set to false for normal money
if (TEST_MODE && save.cash < 1e9) save.cash = 1e9;

let buildings = []; // meta per building, index = feature id
let sel = null;     // selected building index
let view = null;    // last interior transform, used for click hit-testing

const $ = (id) => document.getElementById(id);
const money = (n) => '$' + Math.floor(n).toLocaleString('en-US');

// ---------- Geometry helpers ----------
function toMeters(ring, lon0, lat0) {
  // Longitude degrees shrink with latitude; the old code ignored this and stretched interiors.
  const kx = 111320 * Math.cos(lat0 * Math.PI / 180), ky = 110540;
  return ring.map(([lon, lat]) => [(lon - lon0) * kx, (lat - lat0) * ky]);
}

function ringArea(r) {
  let a = 0;
  for (let i = 0, j = r.length - 1; i < r.length; j = i++) a += (r[j][0] + r[i][0]) * (r[j][1] - r[i][1]);
  return Math.abs(a / 2);
}

function pointInRing(x, y, ring) {
  let inside = false;
  for (let i = 0, j = ring.length - 1; i < ring.length; j = i++) {
    const [xi, yi] = ring[i], [xj, yj] = ring[j];
    if ((yi > y) !== (yj > y) && x < (xj - xi) * (y - yi) / (yj - yi) + xi) inside = !inside;
  }
  return inside;
}

// Inside the outer wall and not inside a courtyard hole.
const pointInBuilding = (x, y, rings) =>
  pointInRing(x, y, rings[0]) && !rings.slice(1).some((h) => pointInRing(x, y, h));

function polygonsOf(g) {
  return g.type === 'Polygon' ? [g.coordinates] : g.type === 'MultiPolygon' ? g.coordinates : [];
}

// Rotate a footprint so its tightest bounding rectangle is axis-aligned (long side along x) with its corner at 0,0.
// The interior grid is then square to the building's own walls, whatever its heading in the real world.
function alignToAxes(rings) {
  const o = rings[0], step = Math.max(1, Math.floor(o.length / 200));
  let best = { area: Infinity, a: 0, w: 0, h: 0 };
  for (let i = 0; i < o.length - 1; i += step) {
    const a = Math.atan2(o[i + 1][1] - o[i][1], o[i + 1][0] - o[i][0]);
    const c = Math.cos(a), s = Math.sin(a);
    let x0 = Infinity, x1 = -Infinity, y0 = Infinity, y1 = -Infinity;
    for (const [x, y] of o) {
      const u = x * c + y * s, v = -x * s + y * c;
      if (u < x0) x0 = u; if (u > x1) x1 = u;
      if (v < y0) y0 = v; if (v > y1) y1 = v;
    }
    const area = (x1 - x0) * (y1 - y0);
    if (area < best.area - 1e-6) best = { area, a, w: x1 - x0, h: y1 - y0 };
  }
  const a = best.a + (best.h > best.w ? Math.PI / 2 : 0);
  const c = Math.cos(a), s = Math.sin(a);
  const rot = rings.map((r) => r.map(([x, y]) => [x * c + y * s, -x * s + y * c]));
  const xs = rot[0].map((p) => p[0]), ys = rot[0].map((p) => p[1]);
  const mx = Math.min(...xs), my = Math.min(...ys);
  return { rings: rot.map((r) => r.map(([x, y]) => [x - mx, y - my])), w: Math.max(...xs) - mx, h: Math.max(...ys) - my };
}

// ---------- Turn an OSM feature into a game property ----------
function enrich(f, uid) {
  const polys = polygonsOf(f.geometry);
  if (!polys.length) return null;
  const rings = polys.reduce((a, b) => (ringArea(b[0]) > ringArea(a[0]) ? b : a)); // largest part
  const n = rings[0].length;
  const lon0 = rings[0].reduce((s, p) => s + p[0], 0) / n;
  const lat0 = rings[0].reduce((s, p) => s + p[1], 0) / n;
  const m0 = rings.map((r) => toMeters(r, lon0, lat0));
  const area = ringArea(m0[0]) - m0.slice(1).reduce((s, r) => s + ringArea(r), 0);
  if (area < 4) return null;
  const { rings: m, w: bw, h: bh } = alignToAxes(m0); // only size and shape survive; compass heading is dropped

  const p = f.properties || {};
  const t = String(p.building || '');
  const zone = /industrial|warehouse|factory|manufacture/.test(t) ? 'industrial'
    : (/retail|commercial|office|supermarket|shop/.test(t) || p.shop) ? 'commercial'
    : /house|residential|apartments|detached|semidetached|terrace|dormitory/.test(t) ? 'residential'
    : 'other';
  const tier = TIERS.find(([max]) => area < max)[1];
  const levels = parseFloat(p['building:levels']);
  const h = parseFloat(p.height) || (levels ? levels * 3.2 : zone === 'industrial' ? 8 : 5);
  const osmId = String(f.id);

  buildings[uid] = {
    osmId, zone, tier, area,
    name: p.name || `${tier} ${osmId.replace(/^\w+\//, '#')}`,
    price: Math.round(area * ZONES[zone].rate / 100) * 100,
    m, dim: [bw, bh]
  };
  return { type: 'Feature', id: uid, geometry: f.geometry, properties: { uid, h, color: ZONES[zone].color } };
}

// ---------- Map ----------
const map = new maplibregl.Map({
  container: 'map',
  // No tiles and no token: the game draws its own streets and buildings.
  style: { version: 8, sources: {}, layers: [{ id: 'bg', type: 'background', paint: { 'background-color': '#0a0f14' } }] },
  center: CENTER, zoom: 16, pitch: 50, bearing: -17.6
});
map.addControl(new maplibregl.NavigationControl({ visualizePitch: true }));

map.on('load', () => {
  map.addSource('roads', { type: 'geojson', data: EMPTY });
  map.addLayer({ // kerb edge, slightly wider than the asphalt
    id: 'roads-case', type: 'line', source: 'roads',
    paint: {
      'line-color': ['case', ['==', ['get', 'walk'], 1], '#53655a', '#4b525b'],
      'line-width': ['interpolate', ['exponential', 2], ['zoom'], 14, ['*', ['+', ['get', 'rw'], 1.2], 0.25], 20, ['*', ['+', ['get', 'rw'], 1.2], 16]]
    }
  });
  map.addLayer({
    id: 'roads', type: 'line', source: 'roads',
    paint: {
      'line-color': ['case', ['==', ['get', 'walk'], 1], '#3f5046', '#2b3036'],
      'line-width': ['interpolate', ['exponential', 2], ['zoom'], 14, ['*', ['get', 'rw'], 0.25], 20, ['*', ['get', 'rw'], 16]]
    }
  });
  map.addSource('paint', { type: 'geojson', data: EMPTY }); // lane lines
  const pw = ['interpolate', ['exponential', 2], ['zoom'], 15, 0.2, 20, 6.4]; // ~0.4 m wide: a little bold so it shows from a distance
  map.addLayer({ id: 'paint-solid', type: 'line', source: 'paint', filter: ['!=', ['get', 'k'], 'dash'],
    paint: { 'line-color': ['match', ['get', 'k'], 'edge', '#e6e6e6', '#f2c200'], 'line-width': pw } });
  map.addLayer({ id: 'paint-dash', type: 'line', source: 'paint', filter: ['==', ['get', 'k'], 'dash'],
    paint: { 'line-color': '#f2c200', 'line-width': pw, 'line-dasharray': [8, 20] } });
  map.addSource('paintfill', { type: 'geojson', data: EMPTY }); // crosswalk bars and stop lines
  map.addLayer({ id: 'paintfill', type: 'fill', source: 'paintfill', paint: { 'fill-color': ['get', 'c'], 'fill-opacity': 0.9 } });
  map.addSource('buildings', { type: 'geojson', data: EMPTY });
  map.addLayer({
    id: 'buildings', type: 'fill-extrusion', source: 'buildings',
    paint: {
      'fill-extrusion-color': ['case',
        ['boolean', ['feature-state', 'selected'], false], '#ffb300',
        ['boolean', ['feature-state', 'owned'], false], '#00bcd4',
        ['get', 'color']],
      'fill-extrusion-height': ['get', 'h'],
      'fill-extrusion-base': 0,
      'fill-extrusion-opacity': 0.85
    }
  });
  const parts = { 'fill-extrusion-color': ['get', 'c'], 'fill-extrusion-base': ['get', 'b'], 'fill-extrusion-height': ['get', 'h'] };
  ['props'].forEach((id) => {
    map.addSource(id, { type: 'geojson', data: EMPTY });
    map.addLayer({ id, type: 'fill-extrusion', source: id, paint: parts });
  });
  try { map.addLayer(trafficLayer()); } catch (err) { console.error(err); $('mapStatus').textContent = 'Traffic layer failed: ' + err.message; }
  map.on('click', 'buildings', (e) => select(e.features[0].properties.uid));
  map.on('mouseenter', 'buildings', () => { map.getCanvas().style.cursor = 'pointer'; });
  map.on('mouseleave', 'buildings', () => { map.getCanvas().style.cursor = ''; });
  loadBuildings();
});

// Fallback when Overpass can't be reached: a generated street grid of varied buildings (same shape as OSM data).
function demoCity() {
  let seed = 7;
  const rnd = () => (seed = (seed * 16807) % 2147483647) / 2147483647; // fixed seed: same city every load
  const kx = 111320 * Math.cos(CENTER[1] * Math.PI / 180), ky = 110540;
  const toLL = (x, y) => [CENTER[0] + x / kx, CENTER[1] + y / ky];
  const rect = (x, y, w, h) => [[x, y], [x + w, y], [x + w, y + h], [x, y + h], [x, y]].map(([a, b]) => toLL(a, b));
  const BLOCK = 110, STEP = 124, feats = [];
  const add = (type, x, y, w, h) => {
    const id = 'demo/' + feats.length;
    feats.push({ type: 'Feature', id, properties: { building: type, id }, geometry: { type: 'Polygon', coordinates: [rect(x, y, w, h)] } });
  };
  for (let i = -3; i < 3; i++) {
    for (let j = -3; j < 3; j++) {
      const bx = i * STEP, by = j * STEP;
      if (rnd() < 0.25) { add('industrial', bx + 8, by + 10, BLOCK * 0.8, BLOCK * 0.6); continue; }
      for (let c = 0; c < 4; c++) {
        for (let r = 0; r < 4; r++) {
          const lw = BLOCK / 4, lh = BLOCK / 4, w = lw * (0.4 + rnd() * 0.5), h = lh * (0.4 + rnd() * 0.5);
          add(['house', 'house', 'house', 'retail', 'commercial', 'warehouse'][Math.floor(rnd() * 6)], bx + c * lw + 2, by + r * lh + 2, w, h);
        }
      }
    }
  }
  const roads = [];
  for (let k = -3; k <= 3; k++) {
    const o = k * STEP - (STEP - BLOCK) / 2;
    [[[o, -3 * STEP], [o, 3 * STEP]], [[-3 * STEP, o], [3 * STEP, o]]].forEach((l) =>
      roads.push({ type: 'Feature', properties: { highway: 'residential' }, geometry: { type: 'LineString', coordinates: l.map(([x, y]) => toLL(x, y)) } }));
  }
  return { type: 'FeatureCollection', features: feats.concat(roads) };
}

async function overpass(query) {
  const errs = [];
  for (const url of MIRRORS) {
    const ctl = new AbortController();
    const timer = setTimeout(() => ctl.abort(), 8000);
    const host = new URL(url).host;
    $('mapStatus').textContent = `Asking ${host}...`;
    try {
      const res = await fetch(url, {
        method: 'POST',
        headers: { 'Content-Type': 'application/x-www-form-urlencoded' },
        body: 'data=' + encodeURIComponent(query),
        signal: ctl.signal
      });
      if (!res.ok) throw new Error('HTTP ' + res.status);
      return await res.json();
    } catch (e) {
      errs.push(`${host}: ${e.name === 'AbortError' ? 'timed out' : e.message}`);
      console.warn(errs[errs.length - 1]);
    } finally {
      clearTimeout(timer);
    }
  }
  throw new Error(errs.join('; '));
}

async function loadBuildings(force, fileRaw) { // force is truthy when the Reload button passes its click event
  const status = $('mapStatus');
  status.textContent = 'Fetching OSM data...';
  const query = QUERY;
  let note = '';
  try {
    let gj;
    try {
      let raw = fileRaw || null; // fileRaw: JSON the player saved from a browser tab
      try { if (!raw && !force) raw = JSON.parse(localStorage.getItem(CACHE_KEY)); } catch (e) { raw = null; }
      if (!raw) {
        try { raw = await overpass(query); }
        catch (e) { // live servers refuse local files: keep the saved real data instead of dropping to the demo city
          try { raw = JSON.parse(localStorage.getItem(CACHE_KEY)); } catch (e2) { raw = null; }
          if (!raw) throw e;
          note = ' Live fetch failed, so your saved copy was used.';
        }
      }
      const isGeo = raw.type === 'FeatureCollection'; // Overpass Turbo's GeoJSON export
      if (!raw.elements && !isGeo) throw new Error('file is neither Overpass JSON nor GeoJSON');
      try { localStorage.setItem(CACHE_KEY, JSON.stringify(raw)); } catch (e) { /* too big to cache: fine */ }
      gj = isGeo ? raw : osmtogeojson(raw);
    } catch (err) {
      console.error(err);
      gj = demoCity();
      note = ` Demo city shown because real data failed (${err.message}).`;
    }
    buildings = [];
    const bFeats = [], roads = [], ctls = [];
    gj.features.forEach((f) => {
      const t = f.geometry && f.geometry.type;
      if (f.properties.building && (t === 'Polygon' || t === 'MultiPolygon')) {
        const g = enrich(f, buildings.length);
        if (g) bFeats.push(g);
      } else if (f.properties.highway && t === 'LineString' && ROAD[f.properties.highway]) {
        f.properties.rw = ROAD[f.properties.highway][0];
        f.properties.walk = ROAD[f.properties.highway][1] === 0 ? 1 : 0;
        roads.push(f);
      } else if (t === 'Point' && /^(traffic_signals|stop|give_way|crossing)$/.test(f.properties.highway || '')) {
        ctls.push(f);
      }
    });
    map.getSource('roads').setData({ type: 'FeatureCollection', features: roads });
    map.getSource('buildings').setData({ type: 'FeatureCollection', features: bFeats });
    startTraffic(roads, ctls);
    sel = null;
    buildings.forEach((b, i) => { if (save.owned[b.osmId]) setState(i, { owned: true }); });
    status.textContent = `Loaded ${bFeats.length} buildings. Click one.${note}`;
    renderInfo(); drawInterior();
  } catch (error) {
    status.textContent = 'Error while loading: ' + error.message;
    console.error(error);
  }
}

const setState = (id, s) => map.setFeatureState({ source: 'buildings', id }, s);

function select(uid) {
  if (sel !== null) setState(sel, { selected: false });
  sel = uid;
  setState(uid, { selected: true });
  renderInfo(); drawInterior();
}

// ---------- Property card, buying and selling ----------
function salePayout(b) { // what you would get for the building and everything in it
  const L = facOf(b.osmId, true), st = save.stock[b.osmId] || { ore: 0, metal: 0 };
  let machines = 0;
  for (const k in L.m) machines += MACH[L.m[k].t].cost / 2; // machines refund at 50%, same as Remove
  const land = Math.round(b.price * SELL_RATE), goods = st.ore * PRICES.ore + st.metal * PRICES.metal;
  return { land, machines, goods, total: land + machines + goods, nM: Object.keys(L.m).length, nW: L.workers.length };
}

function renderInfo() {
  $('cash').textContent = money(save.cash) + (TEST_MODE ? ' (test mode)' : '');
  const b = buildings[sel], btn = $('buyBtn');
  if (!b) { $('info').textContent = 'Select a building on the map.'; btn.disabled = true; btn.textContent = 'Buy'; $('sellPropBtn').disabled = true; $('sellPropBtn').textContent = 'Sell'; return; }
  const owned = !!save.owned[b.osmId];
  $('info').innerHTML = `<b>${b.name}</b><br>${b.tier} &middot; ${b.zone} zone &middot; ${Math.round(b.dim[0])} x ${Math.round(b.dim[1])} m (${Math.round(b.area)} m&sup2;)` +
    `<br>${owned ? 'You own this property.' : 'Price: ' + money(b.price)}`;
  btn.textContent = owned ? 'Owned' : 'Buy for ' + money(b.price);
  btn.disabled = owned || save.cash < b.price;
  const sb = $('sellPropBtn');
  sb.disabled = !owned;
  sb.textContent = owned ? 'Sell for ' + money(salePayout(b).total) : 'Sell';
}

$('buyBtn').addEventListener('click', () => {
  const b = buildings[sel];
  if (!b || save.owned[b.osmId] || save.cash < b.price) return;
  save.cash -= b.price;
  save.owned[b.osmId] = true;
  setState(sel, { owned: true });
  persist(); renderInfo(); drawInterior();
});
$('sellPropBtn').addEventListener('click', () => {
  const b = buildings[sel];
  if (!b || !save.owned[b.osmId]) return;
  const p = salePayout(b);
  if (!confirm(`Sell ${b.name}?\n\nBuilding (${SELL_RATE * 100}% of its price): ${money(p.land)}\n${p.nM} machines (half of what you paid): ${money(p.machines)}\nStock in the building: ${money(p.goods)}\n${p.nW} workers let go, all routes and belts removed\n\nYou receive ${money(p.total)}. This can't be undone.`)) return;
  save.cash += p.total;
  delete save.owned[b.osmId]; delete save.fac[b.osmId]; delete save.stock[b.osmId]; delete save.layouts[b.osmId];
  pending = null;
  setState(sel, { owned: false });
  persist(); renderInfo(); drawInterior();
});
$('loadDataBtn').addEventListener('click', loadBuildings);
$('dataLink').href = 'https://overpass-turbo.eu/?Q=' + encodeURIComponent(QUERY) + '&R';
$('queryBox').value = QUERY;
$('osmFile').addEventListener('change', async (e) => {
  const f = e.target.files[0];
  if (!f) return;
  try { loadBuildings(false, JSON.parse(await f.text())); }
  catch (err) { $('mapStatus').textContent = 'That file is not valid JSON: ' + err.message; }
});
window.addEventListener('resize', drawInterior);

// ---------- Factory data ----------
const BLANK = { m: {}, routes: [], workers: [], nid: 1 };
function facOf(id, readOnly) {
  if (save.fac[id]) return save.fac[id];
  if (readOnly) return BLANK;
  return (save.fac[id] = { m: {}, routes: [], workers: [], nid: 1 });
}

function pathOf(a, b) { // L-shaped belt path, as tile coordinates
  const [x1, y1] = a.split(',').map(Number), [x2, y2] = b.split(',').map(Number);
  const p = [[x1, y1]];
  let x = x1, y = y1;
  while (x !== x2) { x += Math.sign(x2 - x); p.push([x, y]); }
  while (y !== y2) { y += Math.sign(y2 - y); p.push([x, y]); }
  return p;
}

// ---------- Simulation (pure on the save object, so it can be tested without a browser) ----------
function stepFactory(sv, dt) {
  for (const id of Object.keys(sv.fac)) {
    const L = sv.fac[id];
    const stock = sv.stock[id] = sv.stock[id] || { ore: 0, metal: 0 };
    const give = (dst, item, n) => { // hand items to a machine; returns how many it took
      if (!(ACCEPTS[dst.t] || []).includes(item)) return 0;
      const k = dst.t === 'S' ? Math.min(n, 6 - dst.in) : n;
      if (k <= 0) return 0;
      if (dst.t === 'S') dst.in += k; else stock[item] += k;
      return k;
    };

    for (const key in L.m) { // machines work on their own
      const m = L.m[key];
      if (m.t === 'E') { if (m.out < 10 && (m.p += dt) >= 4) { m.out++; m.p = 0; } }
      else if (m.t === 'S' && m.in >= 2 && m.out < 10 && (m.p += dt) >= 6) { m.in -= 2; m.out++; m.p = 0; }
    }

    for (const r of L.routes) { // belts: automatic, paid for once
      if (r.mode !== 'b') continue;
      const src = L.m[r.from], dst = L.m[r.to];
      if (!src || !dst) continue;
      const its = r.items = r.items || [];
      r.cool = (r.cool || 0) - dt;
      if (src.out > 0 && r.cool <= 0 && (!its.length || its[its.length - 1] > 0.8)) { src.out--; its.push(0); r.cool = 1; }
      for (let i = 0; i < its.length; i++) its[i] = Math.min(its[i] + 2 * dt, i === 0 ? r.len : its[i - 1] - 0.8);
      if (its.length && its[0] >= r.len && give(dst, r.item, 1)) its.shift();
    }

    for (const w of L.workers) { // workers: paid by the second, follow their route list in order
      const pay = WAGE * dt;
      w.paid = sv.cash >= pay;
      if (!w.paid) continue;
      sv.cash -= pay;
      const mine = L.routes.filter((r) => r.mode === 'w' && r.w === w.id);
      if (!mine.length) continue;
      w.i = (w.i || 0) % mine.length;
      const r = mine[w.i], src = L.m[r.from], dst = L.m[r.to];
      if (!src || !dst) { w.i++; continue; }
      const [tx, ty] = (w.s === 'd' ? r.to : r.from).split(',').map(Number);
      const dx = tx + 0.5 - w.x, dy = ty + 0.5 - w.y, dist = Math.hypot(dx, dy);
      if (dist > 0.3) { const st = Math.min(dist, SPEED * dt); w.x += dx / dist * st; w.y += dy / dist * st; continue; }
      if (w.s === 'd') {
        if (w.carry && (ACCEPTS[dst.t] || []).includes(w.carry.item)) {
          w.carry.n -= give(dst, w.carry.item, w.carry.n);
          if (w.carry.n > 0) continue; // destination full: wait here
        }
        w.carry = null; w.s = 'p'; w.i++;
      } else if (src.out > 0) {
        const n = Math.min(3, src.out);
        src.out -= n; w.carry = { item: r.item, n }; w.s = 'd';
      } else if (mine.length > 1) w.i++; // nothing to pick up: try the next route
    }
  }
}

// ---------- 3D interior ----------
const BOX = typeof THREE !== 'undefined' ? new THREE.BoxGeometry(1, 1, 1) : null;
const CYL = typeof THREE !== 'undefined' ? new THREE.CylinderGeometry(1, 1, 1, 16) : null;
const CONE = typeof THREE !== 'undefined' ? new THREE.ConeGeometry(1, 1, 12) : null;
const SPH = typeof THREE !== 'undefined' ? new THREE.SphereGeometry(1, 12, 8) : null;
const MATS = {};
const mat = (c, extra) => {
  const k = c + JSON.stringify(extra || {});
  return MATS[k] || (MATS[k] = new THREE.MeshLambertMaterial(Object.assign({ color: c }, extra)));
};
const ITEM_COLOR = { ore: 0xcfa36b, metal: 0xb0bec5 };
const GL = { r: null, tiles: null, key: null, az: 0.6, el: 0.95, dist: 40, w: 0, h: 0, pool: [], wm: {}, anim: [], machines: [] };

function part(g, m, sx, sy, sz, x, y, z, parent) {
  const o = new THREE.Mesh(g, m);
  o.scale.set(sx, sy, sz); o.position.set(x, y, z);
  parent.add(o);
  return o;
}

function initGL() {
  if (GL.r) return true;
  if (typeof THREE === 'undefined') { $('canvasStatus').textContent = '3D library failed to load. Check your connection and refresh.'; return false; }
  GL.cv = $('factoryFloor');
  GL.r = new THREE.WebGLRenderer({ canvas: GL.cv, antialias: true });
  GL.r.setPixelRatio(Math.min(window.devicePixelRatio || 1, 1.5));
  GL.sc = new THREE.Scene();
  GL.sc.background = new THREE.Color(0x0a0d12);
  GL.cam = new THREE.PerspectiveCamera(45, 1, 0.1, 2000);
  GL.sc.add(new THREE.HemisphereLight(0xdde6ff, 0x1a222c, 0.95));
  const sun = new THREE.DirectionalLight(0xffffff, 0.55);
  sun.position.set(25, 60, 30);
  GL.sc.add(sun);
  GL.grp = new THREE.Group();
  GL.sc.add(GL.grp);
  GL.ray = new THREE.Raycaster();
  GL.plane = new THREE.Plane(new THREE.Vector3(0, 1, 0), 0);
  GL.target = new THREE.Vector3();
  GL.hover = new THREE.Mesh(BOX, mat(0x00e5ff, { transparent: true, opacity: 0.35 }));
  GL.hover.scale.set(TILE_M, 0.12, TILE_M);
  GL.hover.visible = false;
  GL.sc.add(GL.hover);

  let down = null; // drag rotates the camera, a plain click builds
  GL.cv.addEventListener('pointerdown', (e) => { down = { x: e.clientX, y: e.clientY, moved: false, pan: e.button !== 0 || e.shiftKey }; GL.cv.setPointerCapture(e.pointerId); });
  GL.cv.addEventListener('pointermove', (e) => {
    if (down) {
      if (!down.moved && Math.hypot(e.clientX - down.x, e.clientY - down.y) > 5) down.moved = true;
      if (down.moved && down.pan) {
        panBy(e.movementX || 0, e.movementY || 0);
        GL.hover.visible = false;
      } else if (down.moved) {
        GL.az -= (e.movementX || 0) * 0.008;
        GL.el = Math.min(1.5, Math.max(0.25, GL.el + (e.movementY || 0) * 0.006));
        GL.hover.visible = false;
      }
    } else {
      const k = pickTile(e);
      GL.hover.visible = !!k;
      if (k) { const [x, y] = k.split(',').map(Number); GL.hover.position.set((x + 0.5) * TILE_M, 0.1, -(y + 0.5) * TILE_M); }
    }
  });
  GL.cv.addEventListener('pointerup', (e) => { if (down && !down.moved && !down.pan) onFloorClick(pickTile(e)); down = null; });
  GL.cv.addEventListener('contextmenu', (e) => e.preventDefault());
  GL.cv.addEventListener('wheel', (e) => {
    e.preventDefault();
    GL.dist = Math.min(300, Math.max(8, GL.dist * (1 + Math.sign(e.deltaY) * 0.1)));
  }, { passive: false });
  if (typeof IntersectionObserver !== 'undefined') new IntersectionObserver(([en]) => { GL.onscreen = en.isIntersecting; }).observe(GL.cv);
  requestAnimationFrame(loop);
  return true;
}

function panBy(dx, dy) { // slide the view across the floor (right-drag, middle-drag or Shift+drag)
  const k = GL.dist * 0.0016;
  const rx = Math.cos(GL.az), rz = -Math.sin(GL.az), fx = -Math.sin(GL.az), fz = -Math.cos(GL.az); // screen-right / away-from-camera on the floor
  GL.target.x += (-rx * dx + fx * dy) * k;
  GL.target.z += (-rz * dx + fz * dy) * k;
}

function pickTile(e) {
  const r = GL.cv.getBoundingClientRect();
  GL.ray.setFromCamera(new THREE.Vector2(((e.clientX - r.left) / r.width) * 2 - 1, -((e.clientY - r.top) / r.height) * 2 + 1), GL.cam);
  const hit = GL.ray.intersectObjects(GL.machines, true)[0]; // tall machines first, so clicking one selects it
  if (hit) { let o = hit.object; while (o && !o.userData.key) o = o.parent; if (o) return o.userData.key; }
  const p = new THREE.Vector3();
  if (!GL.ray.ray.intersectPlane(GL.plane, p)) return null;
  const k = Math.floor(p.x / TILE_M) + ',' + Math.floor(-p.z / TILE_M);
  return GL.tiles && GL.tiles.has(k) ? k : null;
}

function modelOf(t, key) { // machines are built from simple solids; a = parts that animate
  const [x, y] = key.split(',').map(Number), g = new THREE.Group(), a = { key, t, ang: 0 };
  g.position.set((x + 0.5) * TILE_M, 0, -(y + 0.5) * TILE_M);
  g.userData.key = key;
  part(BOX, mat(0x37474f), 1.8, 0.3, 1.8, 0, 0.15, 0, g); // base plate
  if (t === 'E') {
    part(BOX, mat(0xffa726), 1.0, 1.7, 1.0, 0, 1.15, 0, g);
    part(BOX, mat(0xffcc80), 1.4, 0.25, 1.4, 0, 2.1, 0, g);
    a.spin = new THREE.Group();
    a.spin.position.set(0.55, 0.85, 0.55);
    g.add(a.spin);
    part(CONE, mat(0xb0bec5), 0.3, 1.0, 0.3, 0, 0, 0, a.spin).rotation.x = Math.PI; // drill bit, tip down
    part(BOX, mat(0x90a4ae), 0.9, 0.08, 0.12, 0, 0.5, 0, a.spin);                   // blade, so the spin is visible
  } else if (t === 'S') {
    part(BOX, mat(0xb71c1c), 1.5, 1.4, 1.5, 0, 1.0, 0, g);
    part(CYL, mat(0x424242), 0.22, 1.3, 0.22, 0.5, 2.3, 0.5, g); // chimney
    a.glow = new THREE.MeshLambertMaterial({ color: 0x3e2723, emissive: 0xff6d00, emissiveIntensity: 0.1 });
    part(BOX, a.glow, 1.1, 0.15, 1.1, 0, 1.75, 0, g);
  } else {
    part(BOX, mat(0x8d6e63), 1.6, 0.9, 1.6, 0, 0.75, 0, g);
    part(BOX, mat(0x6d4c41), 1.75, 0.1, 1.75, 0, 1.25, 0, g);
    a.fill = part(BOX, mat(0xffd54f), 1.3, 1, 1.3, 0, 1.3, 0, g); // grows with stock
  }
  if (t !== 'C') a.bar = part(BOX, mat(0x76ff03), 0.18, 1, 0.18, -0.8, 0.5, 0.8, g); // output level
  GL.anim.push(a);
  return g;
}

function buildScene() {
  if (!initGL()) return;
  while (GL.grp.children.length) GL.grp.remove(GL.grp.children[0]);
  GL.machines = []; GL.anim = []; GL.wm = {}; GL.tiles = null;
  GL.pool.forEach((o) => { o.visible = false; });
  const b = buildings[sel];
  if (!b) return;

  const outer = b.m[0];
  const xs = outer.map((p) => p[0]), ys = outer.map((p) => p[1]);
  const minX = Math.min(...xs), maxX = Math.max(...xs), minY = Math.min(...ys), maxY = Math.max(...ys);

  const shape = new THREE.Shape(outer.map(([x, y]) => new THREE.Vector2(x, y)));
  b.m.slice(1).forEach((h) => shape.holes.push(new THREE.Path(h.map(([x, y]) => new THREE.Vector2(x, y)))));
  if (GL.floorGeo) GL.floorGeo.dispose();
  GL.floorGeo = new THREE.ShapeGeometry(shape);
  const floor = new THREE.Mesh(GL.floorGeo, mat(0x15181d, { side: THREE.DoubleSide }));
  floor.rotation.x = -Math.PI / 2; // shape x,y -> world x,-z (north is up)
  GL.grp.add(floor);

  const keys = [];
  for (let tx = Math.floor(minX / TILE_M); tx < Math.ceil(maxX / TILE_M); tx++) {
    for (let ty = Math.floor(minY / TILE_M); ty < Math.ceil(maxY / TILE_M); ty++) {
      if (pointInBuilding((tx + 0.5) * TILE_M, (ty + 0.5) * TILE_M, b.m)) keys.push(tx + ',' + ty);
    }
  }
  GL.tiles = new Set(keys);
  const im = new THREE.InstancedMesh(BOX, mat(0x262b33), Math.max(1, keys.length));
  const mtx = new THREE.Matrix4(), q = new THREE.Quaternion();
  keys.forEach((k, i) => {
    const [x, y] = k.split(',').map(Number);
    mtx.compose(new THREE.Vector3((x + 0.5) * TILE_M, 0.02, -(y + 0.5) * TILE_M), q, new THREE.Vector3(TILE_M * 0.94, 0.04, TILE_M * 0.94));
    im.setMatrixAt(i, mtx);
  });
  im.count = keys.length;
  GL.grp.add(im);

  b.m.forEach((ring) => { // low glass walls along the real outline
    for (let i = 0; i < ring.length - 1; i++) {
      const [x1, y1] = ring[i], [x2, y2] = ring[i + 1], len = Math.hypot(x2 - x1, y2 - y1);
      if (len < 0.01) continue;
      const w = part(BOX, mat(0x00bcd4, { transparent: true, opacity: 0.3 }), len, 1.4, 0.25, (x1 + x2) / 2, 0.7, -(y1 + y2) / 2, GL.grp);
      w.rotation.y = -Math.atan2(-(y2 - y1), x2 - x1);
    }
  });

  if (GL.key !== b.osmId) { // frame the camera on a newly selected building
    GL.key = b.osmId;
    GL.target.set((minX + maxX) / 2, 0, -(minY + maxY) / 2);
    GL.dist = Math.max(maxX - minX, maxY - minY) * 1.3 + 14;
    GL.az = 0; GL.el = 1.05; // start square-on so the grid reads cleanly
  }

  const L = facOf(b.osmId, true);
  for (const key in L.m) { const g = modelOf(L.m[key].t, key); GL.grp.add(g); GL.machines.push(g); }

  L.routes.filter((r) => r.mode === 'b').forEach((r) => { // belt bodies
    const p = pathOf(r.from, r.to);
    for (let i = 0; i < p.length - 1; i++) {
      const [x1, y1] = p[i], [x2, y2] = p[i + 1];
      part(BOX, mat(0x263238), (x2 !== x1 ? 1.02 : 0.55) * TILE_M, 0.14, (y2 !== y1 ? 1.02 : 0.55) * TILE_M,
        (x1 + x2 + 1) / 2 * TILE_M, 0.1, -(y1 + y2 + 1) / 2 * TILE_M, GL.grp);
    }
  });

  L.workers.forEach((w, i) => {
    const g = new THREE.Group();
    part(CYL, mat([0x42a5f5, 0xab47bc, 0x26a69a, 0xef5350][i % 4]), 0.3, 1.0, 0.3, 0, 0.5, 0, g);
    part(SPH, mat(0xffccbc), 0.24, 0.24, 0.24, 0, 1.2, 0, g);
    g.userData.box = part(BOX, mat(0xffd54f), 0.45, 0.45, 0.45, 0, 1.75, 0, g);
    GL.grp.add(g);
    GL.wm[w.id] = g;
  });
}

function animate(t, dt) { // per-frame visuals only; the simulation runs on its own timer
  const b = buildings[sel];
  if (!b || !GL.tiles) return;
  const L = facOf(b.osmId, true), st = save.stock[b.osmId] || { ore: 0, metal: 0 };
  GL.anim.forEach((a) => {
    const m = L.m[a.key];
    if (!m) return;
    if (a.bar) { const h = Math.max(0.02, m.out / 10 * 1.6); a.bar.scale.y = h; a.bar.position.y = 0.3 + h / 2; }
    if (a.spin) { if (m.out < 10) a.ang += dt * 6; a.spin.rotation.y = a.ang; }
    if (a.glow) a.glow.emissiveIntensity = m.in >= 2 && m.out < 10 ? 1 : 0.1;
    if (a.fill) { const h = 0.02 + Math.min(1, (st.ore + st.metal) / 60) * 0.8; a.fill.scale.y = h; a.fill.position.y = 1.3 + h / 2; }
  });
  L.workers.forEach((w) => {
    const g = GL.wm[w.id];
    if (!g) return;
    g.position.set(w.x * TILE_M, 0, -w.y * TILE_M);
    g.userData.box.visible = !!w.carry;
    if (w.carry) g.userData.box.material = mat(ITEM_COLOR[w.carry.item]);
  });
  let n = 0;
  L.routes.forEach((r) => { // items riding the belts
    if (r.mode !== 'b' || !r.items) return;
    const p = pathOf(r.from, r.to);
    r.items.forEach((d) => {
      const i = Math.min(Math.floor(d), p.length - 2), f = d - i, A = p[i], B = p[i + 1];
      let o = GL.pool[n++];
      if (!o) { o = new THREE.Mesh(BOX, mat(0xcfa36b)); o.scale.set(0.5, 0.5, 0.5); GL.sc.add(o); GL.pool.push(o); }
      o.material = mat(ITEM_COLOR[r.item]);
      o.visible = true;
      o.position.set((A[0] + (B[0] - A[0]) * f + 0.5) * TILE_M, 0.45, -(A[1] + (B[1] - A[1]) * f + 0.5) * TILE_M);
    });
  });
  for (; n < GL.pool.length; n++) GL.pool[n].visible = false;
}

let lastT = 0;
function loop(ms) {
  requestAnimationFrame(loop);
  const t = ms / 1000, dt = Math.min(0.1, t - lastT);
  lastT = t;
  const empty = !buildings[sel];
  if (GL.onscreen === false || (empty && GL.cleared)) return; // nothing to show: skip the GPU work
  const w = GL.cv.clientWidth, h = GL.cv.clientHeight;
  if (w && h && (w !== GL.w || h !== GL.h)) {
    GL.w = w; GL.h = h;
    GL.r.setSize(w, h, false);
    GL.cam.aspect = w / h;
    GL.cam.updateProjectionMatrix();
  }
  animate(t, dt);
  const c = Math.cos(GL.el);
  GL.cam.position.set(GL.target.x + GL.dist * Math.sin(GL.az) * c, GL.target.y + GL.dist * Math.sin(GL.el), GL.target.z + GL.dist * Math.cos(GL.az) * c);
  GL.cam.lookAt(GL.target);
  GL.r.render(GL.sc, GL.cam);
  GL.cleared = empty;
}

// ---------- Building, routes, hiring ----------
function drawInterior() { buildScene(); updateStatus(); renderLogistics(); renderStock(); }

function updateStatus() {
  const b = buildings[sel], st = $('canvasStatus');
  if (!b) { st.textContent = 'Awaiting building selection...'; return; }
  const L = facOf(b.osmId, true);
  st.textContent = `${GL.tiles ? GL.tiles.size : 0} tiles, ${Object.keys(L.m).length} machines, ${L.workers.length} workers. ` +
    (save.owned[b.osmId] ? 'Click tiles to build. Drag to rotate, right-drag to pan, wheel to zoom.' : 'Buy this property to build here.');
}

function onFloorClick(key) {
  const b = buildings[sel];
  if (!b || !key || !save.owned[b.osmId]) return;
  const L = facOf(b.osmId), cur = L.m[key];
  if (tool === 'W' || tool === 'B') return pickRoute(L, key, cur);
  pending = null;
  if (tool === 'X') {
    if (!cur) return;
    save.cash += MACH[cur.t].cost / 2; // 50% refund
    delete L.m[key];
    L.routes = L.routes.filter((r) => r.from !== key && r.to !== key);
  } else if (!cur && save.cash >= MACH[tool].cost) {
    save.cash -= MACH[tool].cost;
    L.m[key] = { t: tool, out: 0, in: 0, p: 0 };
  } else return;
  persist(); renderInfo(); drawInterior();
}

function pickRoute(L, key, cur) {
  const st = $('canvasStatus');
  if (!cur) { pending = null; st.textContent = 'Click a machine.'; return; }
  if (!pending) {
    if (!OUTPUT[cur.t]) { st.textContent = `${MACH[cur.t].name} has nothing to carry away.`; return; }
    pending = key;
    st.textContent = `Picking up ${OUTPUT[cur.t]} from the ${MACH[cur.t].name}. Now click where it should go.`;
    return;
  }
  const from = pending, item = OUTPUT[L.m[from].t], belt = tool === 'B';
  pending = null;
  if (from === key || !(ACCEPTS[cur.t] || []).includes(item)) { st.textContent = `A ${MACH[cur.t].name} can't take ${item}.`; return; }
  if (L.routes.some((r) => r.from === from && r.to === key && (r.mode === 'b') === belt)) { st.textContent = 'That route already exists.'; return; }
  const r = { from, to: key, item, mode: belt ? 'b' : 'w' };
  if (belt) {
    r.len = pathOf(from, key).length - 1; r.items = []; r.cool = 0;
    if (save.cash < BELT_COST * r.len) { st.textContent = `A ${r.len}-tile belt costs ${money(BELT_COST * r.len)}.`; return; }
    save.cash -= BELT_COST * r.len;
  } else {
    r.w = Number($('workerSel').value);
    if (!L.workers.some((w) => w.id === r.w)) { st.textContent = 'Hire a worker first.'; return; }
  }
  L.routes.push(r);
  persist(); renderInfo(); drawInterior();
}

function renderLogistics() {
  const b = buildings[sel], el = $('logistics'), pick = $('workerSel');
  if (!b || !save.owned[b.osmId]) { el.textContent = ''; pick.innerHTML = ''; return; }
  const L = facOf(b.osmId, true), keep = pick.value;
  pick.innerHTML = L.workers.map((w) => `<option value="${w.id}">${w.name}</option>`).join('');
  if (keep) pick.value = keep;
  const nm = (k) => (L.m[k] ? `${MACH[L.m[k].t].name} (${k})` : k);
  el.innerHTML = `<b>Crew</b> (wage ${WAGE.toFixed(2)} $/s each)<br>` +
    (L.workers.map((w) => `${w.name} (${L.routes.filter((r) => r.w === w.id).length} routes${w.paid === false ? ', unpaid' : ''}) <button data-act="fire" data-id="${w.id}">Fire</button>`).join('<br>') || 'No workers hired.') +
    (L.workers.length > 1 ? '<br><button data-act="fireall">Fire everyone</button>' : '') +
    '<br><b>Routes</b><br>' +
    (L.routes.length ? L.routes.map((r, i) =>
      `${r.mode === 'b' ? 'Belt' : (L.workers.find((w) => w.id === r.w) || {}).name} &middot; ${r.item}: ${nm(r.from)} &rarr; ${nm(r.to)} <button data-act="del" data-i="${i}">x</button>`).join('<br>')
      : 'None yet. Choose Worker route or Belt, click the machine to take from, then the machine to bring it to.');
}

function renderStock() {
  const b = buildings[sel], s = (b && save.stock[b.osmId]) || { ore: 0, metal: 0 };
  $('stock').textContent = b && save.owned[b.osmId] ? `Stock: ${s.ore} ore, ${s.metal} metal` : 'Stock: -';
  $('sellBtn').disabled = !(s.ore || s.metal);
}

$('logistics').addEventListener('click', (e) => {
  const act = e.target.dataset.act, b = buildings[sel];
  if (!act || !b) return;
  const L = facOf(b.osmId), id = Number(e.target.dataset.id);
  if (act === 'fire') {
    const w = L.workers.find((x) => x.id === id), n = L.routes.filter((r) => r.w === id).length;
    if (!w || !confirm(`Fire ${w.name}? Their ${n} route(s) will be deleted. Belts are not affected.`)) return;
    L.workers = L.workers.filter((x) => x.id !== id);
    L.routes = L.routes.filter((r) => r.w !== id);
  }
  if (act === 'fireall') {
    if (!confirm(`Fire all ${L.workers.length} workers? Every worker route will be deleted. Belts are not affected.`)) return;
    L.workers = [];
    L.routes = L.routes.filter((r) => r.mode === 'b');
  }
  if (act === 'del') L.routes.splice(Number(e.target.dataset.i), 1);
  persist(); drawInterior();
});

$('hireBtn').addEventListener('click', () => {
  const b = buildings[sel];
  if (!b || !save.owned[b.osmId] || save.cash < HIRE_COST || !GL.tiles || !GL.tiles.size) return;
  const L = facOf(b.osmId), [tx, ty] = GL.tiles.values().next().value.split(',').map(Number);
  save.cash -= HIRE_COST;
  const id = L.nid++;
  L.workers.push({ id, name: 'Worker ' + id, x: tx + 0.5, y: ty + 0.5, s: 'p', i: 0, carry: null, paid: true });
  persist(); renderInfo(); drawInterior();
});

$('sellBtn').addEventListener('click', () => {
  const b = buildings[sel], s = b && save.stock[b.osmId];
  if (!s) return;
  save.cash += s.ore * PRICES.ore + s.metal * PRICES.metal;
  s.ore = s.metal = 0;
  persist(); renderInfo(); renderStock();
});

document.querySelectorAll('#palette button[data-tool]').forEach((btn) => btn.addEventListener('click', () => {
  tool = btn.dataset.tool; pending = null;
  document.querySelectorAll('#palette button[data-tool]').forEach((x) => x.classList.toggle('active', x === btn));
}));

// Simulation clock: uses real elapsed time, so it keeps up even when the tab is in the background
let lastMs = performance.now(), ticks = 0;
setInterval(() => {
  const now = performance.now();
  let dt = Math.min(5, (now - lastMs) / 1000);
  lastMs = now;
  while (dt > 0) { const s = Math.min(0.1, dt); stepFactory(save, s); dt -= s; }
  if (++ticks % 10 === 0) { persist(); renderStock(); renderInfo(); }
}, 100);

// ---------- Traffic: real road network, signals, stop signs, cars and pedestrians ----------
// class -> [width m, free speed m/s, cars per km at peak, people per km at peak]
const ROAD = {
  motorway: [14, 29, 16, 0], trunk: [12, 25, 14, 0], primary: [11, 20, 12, 0.5], secondary: [9, 16, 8, 1],
  tertiary: [8, 14, 5, 1.5], unclassified: [7, 13, 3, 1], residential: [7, 11, 2, 2], living_street: [5, 5, 0.5, 4],
  service: [4, 6, 1, 0.5], motorway_link: [7, 18, 6, 0], trunk_link: [7, 16, 5, 0], primary_link: [7, 14, 4, 0],
  secondary_link: [7, 12, 3, 0], tertiary_link: [7, 11, 2, 0],
  footway: [1.5, 0, 0, 5], path: [1.5, 0, 0, 2], pedestrian: [4, 0, 0, 8], steps: [1.5, 0, 0, 1], cycleway: [2, 0, 0, 1]
};
const SIG = { g: '#00e676', y: '#ffd600', r: '#ff1744' };
const CAR_COLORS = ['#e0e0e0', '#9e9e9e', '#212121', '#c62828', '#1565c0', '#f9a825', '#2e7d32', '#6d4c41'];
const KX = 111320 * Math.cos(CENTER[1] * Math.PI / 180), KY = 110540;
const STOP_D = 6.5; // metres from the junction to the stop line
const TR = { G: null, cars: [], peds: [], clock: 0, manualHour: null, on: true };

const toXY = (c) => [(c[0] - CENTER[0]) * KX, (c[1] - CENTER[1]) * KY];
const toLL = (x, y) => [CENTER[0] + x / KX, CENTER[1] + y / KY];
const hash = (str) => { let h = 7; for (let i = 0; i < str.length; i++) h = (h * 31 + str.charCodeAt(i)) >>> 0; return h; };
const pick = (a) => a[Math.floor(Math.random() * a.length)];

// More cars at the morning and evening rush, more walkers around lunch and after work. Night is quiet.
const carFactor = (h) => Math.min(1, 0.05 + 0.9 * Math.exp(-((h - 8) ** 2) / 3) + Math.exp(-((h - 17) ** 2) / 4) + 0.5 * Math.exp(-((h - 12.5) ** 2) / 6));
const pedFactor = (h) => Math.min(1, 0.03 + 0.8 * Math.exp(-((h - 12.5) ** 2) / 10) + 0.6 * Math.exp(-((h - 17.5) ** 2) / 6) + 0.4 * Math.exp(-((h - 8) ** 2) / 3));
function trafficHour() {
  if (TR.manualHour !== null) return TR.manualHour;
  const d = new Date();
  return d.getHours() + d.getMinutes() / 60;
}

function maxspeed(tag, fallback) {
  const n = parseFloat(tag);
  if (!n) return fallback;
  return /mph/i.test(String(tag)) ? n * 0.447 : n * 0.2778;
}

function buildGraph(roads, ctls) {
  const nodes = new Map(), edges = [];
  const node = (c) => {
    const k = c[0] + ',' + c[1];
    let n = nodes.get(k);
    if (!n) { n = { k, p: toXY(c), out: [], inc: [], wout: [], nb: new Set(), ctl: null, apps: [], stopE: new Set(), deg: 0, ph: hash(k) % 42 }; nodes.set(k, n); }
    return n;
  };
  const add = (a, b, hw, v, oneway, drive) => {
    const dx = b.p[0] - a.p[0], dy = b.p[1] - a.p[1], len = Math.hypot(dx, dy);
    if (len < 0.5) return;
    const R = ROAD[hw];
    const e = { a, b, len, ux: dx / len, uy: dy / len, hw, v, w: R[0], oneway, drive: drive && R[1] > 0, cars: [] };
    edges.push(e);
    if (e.drive) a.out.push(e);
    if (R[3] > 0) a.wout.push(e);
  };
  for (const f of roads) {
    const p = f.properties, hw = p.highway, R = ROAD[hw];
    if (!R) continue;
    const co = f.geometry.coordinates, v = maxspeed(p.maxspeed, R[1]);
    const ow = p.oneway === 'yes' || p.oneway === '1' || p.junction === 'roundabout', rev = p.oneway === '-1';
    for (let i = 0; i < co.length - 1; i++) {
      const A = node(co[i]), B = node(co[i + 1]);
      if (rev) { add(B, A, hw, v, true, true); add(A, B, hw, v, true, false); }
      else { add(A, B, hw, v, ow, true); add(B, A, hw, v, ow, !ow); } // one-way roads stay walkable both ways
    }
  }
  for (const e of edges) if (e.drive) { e.a.nb.add(e.b.k); e.b.nb.add(e.a.k); e.b.inc.push(e); }
  for (const n of nodes.values()) n.deg = n.nb.size;
  const marks = [];
  for (const f of ctls) {
    const k = f.properties.highway, c = f.geometry.coordinates, n = nodes.get(c[0] + ',' + c[1]);
    if (n && k === 'traffic_signals') n.ctl = 'sig';
    else if (n && k === 'stop') n.ctl = 'stop';
    marks.push({ f, n });
  }
  for (const n of nodes.values()) { // which approaches are controlled
    if (n.ctl === 'sig') n.apps = n.inc;
    else if (n.ctl === 'stop') { // a stop sign at a junction goes on the slowest (minor) road(s); equal roads get an all-way stop
      const slow = Math.min(...n.inc.map((e) => ROAD[e.hw][1]));
      n.apps = n.inc.filter((e) => ROAD[e.hw][1] <= slow + 0.5);
    }
    n.stopE = new Set(n.apps);
  }
  const table = (list, col) => {
    const acc = [];
    let s = 0;
    list.forEach((e) => { s += e.len / 1000 * ROAD[e.hw][col]; acc.push(s); });
    return { list, acc, sum: s };
  };
  return { nodes, edges, marks, dT: table(edges.filter((e) => e.drive), 2), pT: table(edges.filter((e) => ROAD[e.hw][3] > 0), 3) };
}

function pickW(t) { // random edge, weighted by length x density
  if (!t.list.length || t.sum <= 0) return null;
  const r = Math.random() * t.sum;
  let lo = 0, hi = t.acc.length - 1;
  while (lo < hi) { const m = (lo + hi) >> 1; if (t.acc[m] < r) lo = m + 1; else hi = m; }
  return t.list[lo];
}

function sigState(n, e) { // two-phase fixed-time signal; each signal has its own offset
  const g = Math.abs(e.ux) > Math.abs(e.uy) ? 1 : 0, t = (TR.clock + n.ph) % 42;
  if (g === 0) return t < 18 ? 'g' : t < 21 ? 'y' : 'r';
  return t < 21 ? 'r' : t < 39 ? 'g' : 'y';
}

function chooseNext(e) {
  const outs = e.b.out;
  if (!outs.length) return null;
  const fwd = outs.filter((o) => o.b !== e.a);
  return pick(fwd.length ? fwd : outs); // U-turn only at dead ends
}

function spawnCar() {
  const e = pickW(TR.G.dT);
  if (!e) return false;
  const s = Math.random() * e.len;
  if (e.cars.some((o) => Math.abs(o.s - s) < 9)) return false;
  const type = pick(['sedan', 'sedan', 'sedan', 'suv', 'suv', 'pickup']);
  const c = { e, s, v: e.v * 0.5, type, len: CAR_T[type].len, col: pick(CAR_COLORS), next: null, hold: 0, cleared: null };
  e.cars.push(c); TR.cars.push(c);
  return true;
}

function dropCar(c) {
  const i = c.e.cars.indexOf(c);
  if (i >= 0) c.e.cars.splice(i, 1);
}

function stepTraffic(dt) {
  const G = TR.G;
  if (!G) return;
  TR.clock += dt;
  const h = trafficHour();
  const wantC = Math.min(450, Math.round(G.dT.sum * carFactor(h))), wantP = Math.min(250, Math.round(G.pT.sum * pedFactor(h)));
  for (let i = 0; i < 4 && TR.cars.length < wantC; i++) spawnCar();
  if (TR.cars.length > wantC && Math.random() < 0.3) dropCar(TR.cars.pop());
  for (let i = 0; i < 4 && TR.peds.length < wantP; i++) {
    const e = pickW(G.pT);
    if (e) TR.peds.push({ e, s: Math.random() * e.len, v: 1.1 + Math.random() * 0.5, side: Math.random() < 0.5 ? 1 : -1, col: pick(['#ef5350', '#42a5f5', '#ffee58', '#66bb6a', '#ab47bc', '#eceff1']) });
  }
  if (TR.peds.length > wantP && Math.random() < 0.3) TR.peds.pop();

  const dead = new Set();
  for (const c of TR.cars) {
    const e = c.e, toEnd = e.len - c.s;
    if (!c.next) c.next = chooseNext(e);
    if (!c.next) { dead.add(c); continue; } // one-way dead end: car leaves the map
    let gap = Infinity; // free space to the car in front, on this road or the start of the next one
    for (const o of e.cars) if (o !== c && o.s > c.s) gap = Math.min(gap, o.s - o.len - c.s);
    if (gap === Infinity && toEnd < 40) for (const o of c.next.cars) gap = Math.min(gap, toEnd + o.s - o.len);
    let line = Infinity; // distance to a stop line, if this car has to stop
    const n = e.b;
    if (n.stopE.has(e) && c.cleared !== e) {
      const need = n.ctl === 'stop' || ((st) => st === 'r' || (st === 'y' && toEnd - STOP_D > c.v * c.v / 8 + 1))(sigState(n, e));
      if (need) line = toEnd - STOP_D;
      if (line < -0.5) line = Infinity; // already past the line: keep going
      if (n.ctl === 'stop' && line < 1.5 && c.v < 0.3) { c.hold += dt; if (c.hold > 1.5) { c.cleared = e; c.hold = 0; } } else if (n.ctl === 'stop') c.hold = 0;
    }
    const room = Math.max(0, Math.min(gap - 2, line));
    const want = Math.min(e.v, Math.sqrt(2 * 3 * room));
    c.v = c.v < want ? Math.min(want, c.v + 2.5 * dt) : Math.max(want, c.v - 6 * dt);
    c.s += c.v * dt;
    if (c.s >= e.len) {
      const i = e.cars.indexOf(c);
      if (i >= 0) e.cars.splice(i, 1);
      c.s -= e.len; c.e = c.next; c.next = null; c.cleared = null;
      c.e.cars.push(c);
    }
  }
  if (dead.size) { dead.forEach((c) => dropCar(c)); TR.cars = TR.cars.filter((c) => !dead.has(c)); }

  const gone = new Set();
  for (const p of TR.peds) {
    p.s += p.v * dt;
    if (p.s < p.e.len) continue;
    const outs = p.e.b.wout, fwd = outs.filter((o) => o.b !== p.e.a), list = fwd.length ? fwd : outs;
    if (!list.length) { gone.add(p); continue; }
    p.s -= p.e.len; p.e = pick(list);
  }
  if (gone.size) TR.peds = TR.peds.filter((p) => !gone.has(p));
}

const quad = (x, y, ux, uy, hl, hw) => [ // rectangle centred on x,y: hl along (ux,uy), hw across it
  toLL(x + ux * hl + uy * hw, y + uy * hl - ux * hw), toLL(x + ux * hl - uy * hw, y + uy * hl + ux * hw),
  toLL(x - ux * hl - uy * hw, y - uy * hl + ux * hw), toLL(x - ux * hl + uy * hw, y - uy * hl - ux * hw)
];
const poly = (ring, color) => ({ type: 'Feature', properties: { c: color, b: 0, h: 0 }, geometry: { type: 'Polygon', coordinates: [[...ring, ring[0]]] } });
const box3 = (x, y, ux, uy, hl, hw, b, h, c) => { const f = poly(quad(x, y, ux, uy, hl, hw), c); f.properties.b = b; f.properties.h = h; return f; };

// Vehicle shapes: length, width, body top, glass top, roof top, cabin [length share, forward shift]
const CAR_T = {
  sedan: { len: 4.6, wid: 1.85, body: 0.95, glass: 1.3, roof: 1.42, cab: [0.52, -0.03] },
  suv: { len: 4.8, wid: 1.95, body: 1.1, glass: 1.55, roof: 1.75, cab: [0.66, -0.06] },
  pickup: { len: 5.4, wid: 2.0, body: 1.1, glass: 1.55, roof: 1.75, cab: [0.36, 0.14] }
};

// ---------- GPU-instanced traffic: every car and pedestrian part is drawn in one draw call, moved by matrices ----------
const MAX_PARTS = 6400;
const RGB = {};
const rgb = (hex) => RGB[hex] || (RGB[hex] = (() => { const c = new THREE.Color(hex); return [c.r, c.g, c.b]; })());

function partsOf(T) { // [forward shift, right shift, half length, half width, bottom, top, colour ('car' = body colour)]
  const hl = T.len / 2, hw = T.wid / 2, cl = T.cab[0] * hl, co = T.cab[1] * T.len;
  const p = [[0, 0, hl, hw, 0.3, T.body, 'car'], [co, 0, cl, hw * 0.88, T.body, T.glass, '#37474f'], [co, 0, cl * 0.92, hw * 0.82, T.glass, T.roof, 'car']];
  for (const dl of [0.32 * T.len, -0.32 * T.len]) for (const s of [1, -1]) p.push([dl, s * (hw - 0.05), 0.36, 0.14, 0, 0.55, '#151515']); // wheels
  for (const s of [0.6, -0.6]) {
    p.push([hl - 0.05, s * hw, 0.07, 0.2, 0.55, 0.78, '#fff59d']); // headlights
    p.push([-hl + 0.05, s * hw, 0.07, 0.2, 0.6, 0.78, '#e53935']); // tail lights
  }
  return p;
}
const CAR_PARTS = {};
for (const k in CAR_T) CAR_PARTS[k] = partsOf(CAR_T[k]);
const PED_PARTS = [[0, 0, 0.2, 0.16, 0, 1.3, 'car'], [0, 0, 0.1, 0.1, 1.3, 1.65, '#ffccbc']];

// Writes one 4x4 matrix + colour per part straight into the GPU buffers (no objects created per frame).
// Scene axes: x = east, y = up, z = south, so north-up metres (x, y) become (x, -y).
function writeParts(arr, col, i, x, y, ux, uy, parts, hex) {
  const fx = ux, fz = -uy, rx = uy, rz = ux; // forward and right-hand directions on the ground
  for (let j = 0; j < parts.length; j++) {
    const q = parts[j], o = i * 16, sl = q[2] * 2, sw = q[3] * 2, sh = q[5] - q[4], c = rgb(q[6] === 'car' ? hex : q[6]);
    arr[o] = fx * sl; arr[o + 1] = 0; arr[o + 2] = fz * sl; arr[o + 3] = 0;
    arr[o + 4] = 0; arr[o + 5] = sh; arr[o + 6] = 0; arr[o + 7] = 0;
    arr[o + 8] = rx * sw; arr[o + 9] = 0; arr[o + 10] = rz * sw; arr[o + 11] = 0;
    arr[o + 12] = x + fx * q[0] + rx * q[1]; arr[o + 13] = q[4] + sh / 2; arr[o + 14] = -y + fz * q[0] + rz * q[1]; arr[o + 15] = 1;
    col[i * 3] = c[0]; col[i * 3 + 1] = c[1]; col[i * 3 + 2] = c[2];
    i++;
  }
  return i;
}

function trafficLayer() { // a Three.js layer living inside the map's own WebGL context
  const o = maplibregl.MercatorCoordinate.fromLngLat(CENTER, 0), sc = (o.meterInMercatorCoordinateUnits || o.meterInMercatorUnits || (() => 1 / (40075016.686 * Math.cos(CENTER[1] * Math.PI / 180)))).call(o); // map units per metre
  const flip = new THREE.Matrix4().makeRotationX(Math.PI / 2), L = new THREE.Matrix4(), S = new THREE.Vector3(sc, -sc, sc);
  return {
    id: 'traffic3d', type: 'custom', renderingMode: '3d', last: 0, failed: false,
    onAdd(map, gl) {
      this.map = map;
      this.camera = new THREE.Camera();
      this.scene = new THREE.Scene();
      this.scene.add(new THREE.HemisphereLight(0xe8eeff, 0x556070, 0.9));
      const sun = new THREE.DirectionalLight(0xffffff, 0.6);
      sun.position.set(40, 80, 30);
      this.scene.add(sun);
      this.renderer = new THREE.WebGLRenderer({ canvas: map.getCanvas(), context: gl, antialias: true });
      this.renderer.autoClear = false;
      this.mesh = new THREE.InstancedMesh(new THREE.BoxGeometry(1, 1, 1), new THREE.MeshLambertMaterial({ color: 0xffffff }), MAX_PARTS);
      this.mesh.setColorAt(0, new THREE.Color(0xffffff)); // allocates the per-instance colour buffer
      this.mesh.frustumCulled = false;
      this.mesh.count = 0;
      this.scene.add(this.mesh);
      this.last = performance.now();
      this.acc = 0;
    },
    render(gl, matrix) {
      const now = performance.now(), dt = Math.min(0.1, (now - this.last) / 1000);
      this.last = now;
      const live = TR.G && TR.on && !this.failed;
      if (live) { // the simulation ticks 30 times a second; drawing extrapolates between ticks so motion stays smooth
        this.acc += dt;
        try { for (let k = 0; this.acc >= 1 / 30 && k < 3; k++) { stepTraffic(1 / 30); this.acc -= 1 / 30; } }
        catch (err) { this.failed = true; console.error('Traffic sim stopped:', err); }
        if (this.acc > 0.1) this.acc = 0;
      }
      const arr = this.mesh.instanceMatrix.array, col = this.mesh.instanceColor.array;
      let i = 0;
      if (live) {
        for (const c of TR.cars) {
          if (i + 11 > MAX_PARTS) break;
          const e = c.e, off = e.oneway ? 0 : e.w * 0.25, d = c.s + c.v * this.acc - c.len / 2; // drive on the right
          i = writeParts(arr, col, i, e.a.p[0] + e.ux * d + e.uy * off, e.a.p[1] + e.uy * d - e.ux * off, e.ux, e.uy, CAR_PARTS[c.type], c.col);
        }
        for (const p of TR.peds) {
          if (i + 2 > MAX_PARTS) break;
          const e = p.e, off = (ROAD[e.hw][1] > 0 ? e.w / 2 + 1.5 : 0) * p.side;
          i = writeParts(arr, col, i, e.a.p[0] + e.ux * (p.s + p.v * this.acc) + e.uy * off, e.a.p[1] + e.uy * (p.s + p.v * this.acc) - e.ux * off, e.ux, e.uy, PED_PARTS, p.col);
        }
      }
      this.mesh.count = i;
      this.mesh.instanceMatrix.needsUpdate = true;
      this.mesh.instanceColor.needsUpdate = true;
      L.makeTranslation(o.x, o.y, o.z).scale(S).multiply(flip);
      this.camera.projectionMatrix.fromArray(matrix).multiply(L);
      const cv = this.map.getCanvas();
      this.renderer.setViewport(0, 0, cv.width, cv.height);
      if (this.renderer.resetState) this.renderer.resetState(); else this.renderer.state.reset();
      this.renderer.render(this.scene, this.camera);
      if (live) this.map.triggerRepaint(); // keep animating while traffic runs
    }
  };
}

function renderTraffic() { if (map.triggerRepaint) map.triggerRepaint(); } // wake the traffic layer after a change

function propFeatures() { // signal poles with mast arms and lamps, stop signs on posts
  const out = [];
  for (const n of TR.G.nodes.values()) {
    for (const e of n.apps) {
      const ux = e.ux, uy = e.uy, rx = uy, ry = -ux, w = e.w, off = e.oneway ? 0 : w * 0.25;
      if (n.ctl === 'sig') {
        const px = n.p[0] - ux * 2 + rx * (w / 2 + 1.1), py = n.p[1] - uy * 2 + ry * (w / 2 + 1.1); // pole just beyond the kerb
        const hx = n.p[0] - ux * 2 + rx * off, hy = n.p[1] - uy * 2 + ry * off;                      // signal head hangs over the lane
        const L = Math.hypot(hx - px, hy - py) || 1, dx = (hx - px) / L, dy = (hy - py) / L;
        out.push(box3(px, py, ux, uy, 0.15, 0.15, 0, 6, '#9e9e9e'));
        out.push(box3((px + hx) / 2, (py + hy) / 2, dx, dy, L / 2, 0.09, 5.6, 5.85, '#9e9e9e'));
        out.push(box3(hx, hy, ux, uy, 0.25, 0.25, 4.85, 5.6, '#212121'));
        const st = sigState(n, e);
        [['r', 5.35], ['y', 5.12], ['g', 4.9]].forEach(([k, b]) => out.push(box3(hx - ux * 0.02, hy - uy * 0.02, ux, uy, 0.28, 0.18, b, b + 0.2, st === k ? SIG[k] : '#3a3a3a')));
      } else {
        const sx = n.p[0] - ux * (STOP_D - 0.3) + rx * (w / 2 + 0.9), sy = n.p[1] - uy * (STOP_D - 0.3) + ry * (w / 2 + 0.9);
        out.push(box3(sx, sy, ux, uy, 0.05, 0.05, 0, 2.2, '#9e9e9e'));                                  // post
        out.push(box3(sx - ux * 0.07, sy - uy * 0.07, ux, uy, 0.03, 0.42, 1.9, 2.75, '#d32f2f'));       // red face
        out.push(box3(sx - ux * 0.11, sy - uy * 0.11, ux, uy, 0.03, 0.3, 2.2, 2.4, '#fafafa'));          // white band
      }
    }
  }
  return out;
}

function renderControls() {
  if (!TR.G || !map.getSource('props')) return;
  let sig = '';
  for (const n of TR.sigNodes) for (const e of n.apps) sig += sigState(n, e);
  if (sig === TR.lastSig) return; // no lamp changed this second
  TR.lastSig = sig;
  map.getSource('props').setData({ type: 'FeatureCollection', features: propFeatures() });
}

function buildPaint(G) { // lane lines, crosswalks and stop lines
  const lines = [], fills = [];
  const seg = (ax, ay, bx, by, k) => lines.push({ type: 'Feature', properties: { k }, geometry: { type: 'LineString', coordinates: [toLL(ax, ay), toLL(bx, by)] } });
  for (const e of G.edges) {
    if (!e.drive || (!e.oneway && e.a.k > e.b.k) || e.w < 7) continue; // one set of lines per road segment
    const t0 = e.a.deg >= 3 ? 6.5 : 0, t1 = e.b.deg >= 3 ? 6.5 : 0; // paint stops short of junctions
    if (e.len - t0 - t1 < 3) continue;
    const ax = e.a.p[0] + e.ux * t0, ay = e.a.p[1] + e.uy * t0, bx = e.b.p[0] - e.ux * t1, by = e.b.p[1] - e.uy * t1;
    if (!e.oneway) seg(ax, ay, bx, by, ROAD[e.hw][2] >= 5 ? 'solid' : 'dash'); // yellow centre line: solid on busier roads
    if (e.w >= 8) for (const s of [1, -1]) { const d = s * (e.w / 2 - 0.5); seg(ax + e.uy * d, ay - e.ux * d, bx + e.uy * d, by - e.ux * d, 'edge'); }
  }
  const bar = (x, y, ux, uy, hl, hw) => fills.push(poly(quad(x, y, ux, uy, hl, hw), '#ececec'));
  const zebra = (x, y, ux, uy, w) => { for (let o = -w / 2 + 0.7; o < w / 2 - 0.5; o += 1.0) bar(x + uy * o, y - ux * o, ux, uy, 1.5, 0.25); };
  for (const n of G.nodes.values()) {
    for (const e of n.apps) { // stop line across the approaching lane
      const off = e.oneway ? 0 : e.w * 0.25, hw = (e.oneway ? e.w / 2 : e.w * 0.25) - 0.35;
      bar(n.p[0] - e.ux * (STOP_D - 0.25) + e.uy * off, n.p[1] - e.uy * (STOP_D - 0.25) - e.ux * off, e.ux, e.uy, 0.25, hw);
    }
    if (n.ctl === 'sig') for (const e of n.inc) zebra(n.p[0] - e.ux * 3.5, n.p[1] - e.uy * 3.5, e.ux, e.uy, e.w); // signals get a crosswalk on every leg
  }
  for (const { f, n } of G.marks) { // crossings tagged in OpenStreetMap
    if (f.properties.highway !== 'crossing' || !n || n.ctl === 'sig') continue;
    const e = n.out[0] || n.inc[0];
    if (e) zebra(n.p[0], n.p[1], e.ux, e.uy, e.w);
  }
  return { lines: { type: 'FeatureCollection', features: lines }, fills: { type: 'FeatureCollection', features: fills } };
}

function startTraffic(roads, ctls) {
  TR.cars = []; TR.peds = []; TR.clock = Math.random() * 42;
  TR.G = buildGraph(roads, ctls);
  const all = [...TR.G.nodes.values()];
  TR.sigNodes = all.filter((n) => n.ctl === 'sig'); TR.nSig = TR.sigNodes.length; TR.nStop = all.filter((n) => n.ctl === 'stop').length; TR.lastSig = null;
  const P = buildPaint(TR.G);
  if (map.getSource('paint')) { map.getSource('paint').setData(P.lines); map.getSource('paintfill').setData(P.fills); }
  for (let i = 0; i < 40; i++) stepTraffic(0.1); // fill the streets right away
  renderControls(); renderTraffic(); renderTrafficInfo();
}

function renderTrafficInfo() {
  if (!TR.G) return;
  const sigs = TR.nSig, stops = TR.nStop;
  const hr = trafficHour(), hh = Math.floor(hr), mm = Math.floor((hr - hh) * 60);
  $('hourLbl').textContent = (TR.manualHour === null ? 'now ' : '') + String(hh).padStart(2, '0') + ':' + (TR.manualHour === null ? String(mm).padStart(2, '0') : '00');
  $('trafficInfo').textContent = `${TR.cars.length} cars, ${TR.peds.length} people, ${sigs} signals, ${stops} stop signs` +
    (sigs + stops === 0 ? ' (none in this data: re-export it with the link below to get them)' : '');
}

$('trafficOn').addEventListener('change', (e) => { TR.on = e.target.checked; renderTraffic(); });
$('hour').addEventListener('input', (e) => { TR.manualHour = Number(e.target.value); renderTrafficInfo(); });
$('hourNow').addEventListener('click', () => { TR.manualHour = null; renderTrafficInfo(); });

setInterval(() => { if (TR.G) { renderControls(); renderTrafficInfo(); } }, 1000); // lamps and the counter only need a slow clock

renderInfo();