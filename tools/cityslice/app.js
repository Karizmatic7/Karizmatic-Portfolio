import * as THREE from 'three';
import { OrbitControls } from 'three/addons/controls/OrbitControls.js';

/* ---------- small helpers ---------- */
const $ = id => document.getElementById(id);
const say = (m, bad) => { const s = $('status'); s.textContent = m; s.className = bad ? 'err' : ''; };
const esc = s => String(s).replace(/[&<>"]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));
const r7 = v => Math.round(v * 1e7) / 1e7, r1 = v => Math.round(v * 10) / 10;
const inBox = (b, p) => p[0] >= b.w && p[0] <= b.e && p[1] >= b.s && p[1] <= b.n;
const same = (a, b) => Math.abs(a[0] - b[0]) < 1e-9 && Math.abs(a[1] - b[1]) < 1e-9;
const ll = a => (a || []).map(p => [p.lon, p.lat]);
const num = v => { const m = String(v ?? '').match(/^\s*(-?[\d.]+)\s*(ft|feet|')?/i); return m ? parseFloat(m[1]) * (m[2] ? 0.3048 : 1) : NaN; };

// Local metric projection around the city centre (x = east, z = south, in metres)
function makeProj(lat0, lon0) {
  const p = lat0 * Math.PI / 180;
  const mLat = 111132.92 - 559.82 * Math.cos(2 * p) + 1.175 * Math.cos(4 * p);
  const mLon = 111412.84 * Math.cos(p) - 93.5 * Math.cos(3 * p);
  return { mLat, mLon, x: lon => (lon - lon0) * mLon, z: lat => -(lat - lat0) * mLat, lon: x => lon0 + x / mLon, lat: z => lat0 - z / mLat };
}

/* ---------- 1. geocode (OpenStreetMap Nominatim) ---------- */
async function geocode(q) {
  if (picked && picked.display_name === q.trim()) return picked;
  const m = q.match(/^\s*(-?\d+(?:\.\d+)?)\s*[, ]\s*(-?\d+(?:\.\d+)?)\s*$/);
  if (m) return { lat: +m[1], lon: +m[2], display_name: `${m[1]}, ${m[2]}` };
  const r = await fetch('https://nominatim.openstreetmap.org/search?format=jsonv2&limit=1&q=' + encodeURIComponent(q));
  if (!r.ok) throw new Error('Place search failed (HTTP ' + r.status + ').');
  const j = await r.json();
  if (!j.length) throw new Error(`No place found for “${q}”. Try adding the country.`);
  return { lat: +j[0].lat, lon: +j[0].lon, display_name: j[0].display_name };
}

/* ---------- 2. OpenStreetMap features (Overpass API) ---------- */
const OVERPASS = ['https://overpass-api.de/api/interpreter', 'https://overpass.kumi.systems/api/interpreter', 'https://overpass.private.coffee/api/interpreter'];
async function overpass(b, foot) {
  const bb = `${b.s},${b.w},${b.n},${b.e}`;
  const hw = foot ? '' : '["highway"!~"^(footway|path|cycleway|steps|pedestrian|bridleway|corridor|proposed|construction)$"]';
  const q = `[out:json][timeout:90];(
    way["building"](${bb}); relation["building"]["type"="multipolygon"](${bb});
    way["highway"]${hw}(${bb});
    way["waterway"~"^(river|stream|canal|riverbank)$"](${bb});
    way["natural"~"^(water|coastline|wood)$"](${bb}); relation["natural"="water"](${bb});
    way["leisure"~"^(park|garden|pitch)$"](${bb}); way["landuse"~"^(forest|grass|meadow|cemetery)$"](${bb});
    node["highway"~"^(traffic_signals|stop|give_way|mini_roundabout|turning_circle)$"](${bb});
    node["name"][~"^(shop|amenity|tourism|office)$"~"."](${bb});
  );out geom;`;
  let err;
  for (const ep of OVERPASS) {
    try {
      const r = await fetch(ep, { method: 'POST', body: 'data=' + encodeURIComponent(q), headers: { 'Content-Type': 'application/x-www-form-urlencoded' } });
      if (!r.ok) throw new Error('HTTP ' + r.status);
      const rd = r.body.getReader(), chunks = []; let got = 0;
      for (;;) { const { done, value } = await rd.read(); if (done) break; chunks.push(value); got += value.length; say(`Downloading OpenStreetMap data… ${(got / 1e6).toFixed(1)} MB`); }
      const j = JSON.parse(await new Blob(chunks).text());
      if (j.remark && /error|timed out/i.test(j.remark)) throw new Error(j.remark);
      return j.elements;
    } catch (e) { err = e; say('An OpenStreetMap server is busy, trying another…'); }
  }
  throw new Error('OpenStreetMap download failed (' + err.message + '). Try a smaller radius or wait a minute.');
}

/* ---------- 3. elevation (Terrarium tiles: elevation = R*256 + G + B/256 - 32768) ---------- */
async function loadElevation(b) {
  const z = 15, n = 2 ** z;
  const tx = lon => (lon + 180) / 360 * n;
  const ty = lat => { const r = lat * Math.PI / 180; return (1 - Math.log(Math.tan(r) + 1 / Math.cos(r)) / Math.PI) / 2 * n; };
  const x0 = Math.floor(tx(b.w)), x1 = Math.floor(tx(b.e)), y0 = Math.floor(ty(b.n)), y1 = Math.floor(ty(b.s));
  const W = (x1 - x0 + 1) * 256, H = (y1 - y0 + 1) * 256, data = new Float32Array(W * H);
  let ok = 0, total = 0;
  const jobs = [];
  for (let Ty = y0; Ty <= y1; Ty++) for (let Tx = x0; Tx <= x1; Tx++) {
    total++;
    jobs.push((async () => {
      try {
        const r = await fetch(`https://s3.amazonaws.com/elevation-tiles-prod/terrarium/${z}/${Tx}/${Ty}.png`);
        if (!r.ok) throw 0;
        const bmp = await createImageBitmap(await r.blob(), { colorSpaceConversion: 'none' });
        const c = document.createElement('canvas'); c.width = c.height = 256;
        const g = c.getContext('2d', { willReadFrequently: true }); g.drawImage(bmp, 0, 0);
        const d = g.getImageData(0, 0, 256, 256).data;
        for (let j = 0; j < 256; j++) for (let i = 0; i < 256; i++) {
          const k = (j * 256 + i) * 4;
          data[((Ty - y0) * 256 + j) * W + (Tx - x0) * 256 + i] = d[k] * 256 + d[k + 1] + d[k + 2] / 256 - 32768;
        }
        ok++;
      } catch { /* leave zeros */ }
    })());
  }
  await Promise.all(jobs);
  const at = (lon, lat) => {
    if (!ok) return 0;
    let px = (tx(lon) - x0) * 256 - 0.5, py = (ty(lat) - y0) * 256 - 0.5;
    px = Math.min(Math.max(px, 0), W - 1.001); py = Math.min(Math.max(py, 0), H - 1.001);
    const i = px | 0, j = py | 0, fx = px - i, fy = py - j, k = j * W + i;
    return (data[k] * (1 - fx) + data[k + 1] * fx) * (1 - fy) + (data[k + W] * (1 - fx) + data[k + W + 1] * fx) * fy;
  };
  return { at, ok, total };
}

/* ---------- 4. geometry helpers ---------- */
function pip(p, ring) {
  let c = false;
  for (let i = 0, j = ring.length - 1; i < ring.length; j = i++) {
    const a = ring[i], b = ring[j];
    if ((a[1] > p[1]) !== (b[1] > p[1]) && p[0] < (b[0] - a[0]) * (p[1] - a[1]) / (b[1] - a[1]) + a[0]) c = !c;
  }
  return c;
}
// Join member ways of a multipolygon into closed rings
function rings(ways) {
  const K = p => p[0].toFixed(7) + ',' + p[1].toFixed(7), out = [], open = [];
  for (const w of ways) { if (w.length > 3 && K(w[0]) === K(w[w.length - 1])) out.push(w); else if (w.length > 1) open.push(w); }
  while (open.length) {
    let c = open.pop();
    while (K(c[0]) !== K(c[c.length - 1])) {
      const cs = K(c[0]), ce = K(c[c.length - 1]);
      const i = open.findIndex(s => [K(s[0]), K(s[s.length - 1])].some(k => k === cs || k === ce));
      if (i < 0) break;
      const s = open.splice(i, 1)[0];
      if (K(s[0]) === ce) c = c.concat(s.slice(1));
      else if (K(s[s.length - 1]) === ce) c = c.concat(s.slice(0, -1).reverse());
      else if (K(s[s.length - 1]) === cs) c = s.concat(c.slice(1));
      else c = s.slice().reverse().concat(c.slice(1));
    }
    if (c.length > 3 && K(c[0]) === K(c[c.length - 1])) out.push(c);
  }
  return out;
}
// OSM way/relation -> array of polygons, each [outerRing, ...holes] in [lon, lat]
function polysOf(el) {
  if (el.type === 'way') { const r = ll(el.geometry); return r.length > 3 && same(r[0], r[r.length - 1]) ? [[r]] : []; }
  const o = [], i = [];
  for (const m of el.members || []) if (m.type === 'way' && m.geometry) (m.role === 'inner' ? i : o).push(ll(m.geometry));
  const I = rings(i);
  return rings(o).map(r => [r, ...I.filter(h => pip(h[0], r))]);
}
function clipRing(pts, b) { // Sutherland–Hodgman against the bounding box (open ring in)
  const edge = (P, inside, hit) => P.reduce((o, c, i) => {
    const p = P[(i + P.length - 1) % P.length];
    if (inside(c)) { if (!inside(p)) o.push(hit(p, c)); o.push(c); } else if (inside(p)) o.push(hit(p, c));
    return o;
  }, []);
  const X = x => (a, c) => [x, a[1] + (x - a[0]) / (c[0] - a[0]) * (c[1] - a[1])];
  const Y = y => (a, c) => [a[0] + (y - a[1]) / (c[1] - a[1]) * (c[0] - a[0]), y];
  let o = edge(pts, p => p[0] >= b.w, X(b.w));
  o = edge(o, p => p[0] <= b.e, X(b.e));
  o = edge(o, p => p[1] >= b.s, Y(b.s));
  return edge(o, p => p[1] <= b.n, Y(b.n));
}
function clipPolys(polys, b) {
  const out = [];
  for (const p of polys) {
    const o = clipRing(p[0].slice(0, -1), b);
    if (o.length < 3) continue;
    const holes = p.slice(1).map(h => clipRing(h.slice(0, -1), b)).filter(h => h.length >= 3);
    out.push([o, ...holes].map(r => [...r, r[0]]));
  }
  return out;
}
function clipSeg(a, c, b) { // Liang–Barsky
  let t0 = 0, t1 = 1;
  const dx = c[0] - a[0], dy = c[1] - a[1], p = [-dx, dx, -dy, dy], q = [a[0] - b.w, b.e - a[0], a[1] - b.s, b.n - a[1]];
  for (let i = 0; i < 4; i++) {
    if (p[i] === 0) { if (q[i] < 0) return null; continue; }
    const r = q[i] / p[i];
    if (p[i] < 0) { if (r > t1) return null; if (r > t0) t0 = r; } else { if (r < t0) return null; if (r < t1) t1 = r; }
  }
  return [[a[0] + t0 * dx, a[1] + t0 * dy], [a[0] + t1 * dx, a[1] + t1 * dy]];
}
function clipLine(pts, b) {
  const out = []; let cur = null;
  for (let i = 0; i < pts.length - 1; i++) {
    const s = clipSeg(pts[i], pts[i + 1], b);
    if (!s) { if (cur && cur.length > 1) out.push(cur); cur = null; continue; }
    if (cur && same(cur[cur.length - 1], s[0])) cur.push(s[1]);
    else { if (cur && cur.length > 1) out.push(cur); cur = [s[0], s[1]]; }
  }
  if (cur && cur.length > 1) out.push(cur);
  return out;
}
const ringArea = (r, P) => { let a = 0; for (let i = 0; i < r.length - 1; i++) a += P.x(r[i][0]) * P.z(r[i + 1][1]) - P.x(r[i + 1][0]) * P.z(r[i][1]); return a / 2; };
function obb(ring, P) { // minimum-area oriented bounding rectangle
  const pts = ring.map(p => [P.x(p[0]), P.z(p[1])]); let best = null;
  for (let i = 0; i < pts.length - 1; i++) {
    const dx = pts[i + 1][0] - pts[i][0], dy = pts[i + 1][1] - pts[i][1], L = Math.hypot(dx, dy);
    if (!L) continue;
    const ux = dx / L, uy = dy / L; let a = 1e9, b = -1e9, c = 1e9, d = -1e9;
    for (const p of pts) { const s = p[0] * ux + p[1] * uy, t = -p[0] * uy + p[1] * ux; a = Math.min(a, s); b = Math.max(b, s); c = Math.min(c, t); d = Math.max(d, t); }
    const w = b - a, h = d - c;
    if (!best || w * h < best.w * best.h) best = { w, h, ang: Math.atan2(uy, ux) };
  }
  return best || { w: 0, h: 0, ang: 0 };
}

/* ---------- 5. OSM elements -> GeoJSON layers ---------- */
const TYPE_H = { house: 7, detached: 7, residential: 9, apartments: 15, dormitory: 12, hotel: 20, commercial: 12, office: 18, retail: 6, industrial: 9, warehouse: 8, church: 14, cathedral: 35, school: 10, university: 14, hospital: 18, civic: 12, garage: 3, garages: 3, shed: 3, hut: 3, roof: 4, carport: 3, barn: 7 };
const RANK = { motorway: 0, trunk: 1, primary: 2, secondary: 3, tertiary: 4, unclassified: 5, residential: 5, living_street: 6, service: 7 };
const WIDTH = { motorway: 12, trunk: 11, primary: 10, secondary: 9, tertiary: 8, unclassified: 6.5, residential: 6.5, living_street: 5, service: 4, pedestrian: 5, track: 3 };
const RNAME = ['motorway', 'trunk', 'primary', 'secondary', 'tertiary', 'residential/unclassified', 'living_street', 'service', 'other', 'other'];
const DRIVE = new Set(Object.keys(RANK).flatMap(k => [k, k + '_link']));
const ATTR = '© OpenStreetMap contributors (ODbL); elevation: Mapzen Terrain Tiles';
const SKIP_POI = new Set(['parking', 'parking_entrance', 'parking_space', 'bicycle_parking', 'bench', 'waste_basket', 'shelter', 'toilets', 'vending_machine', 'post_box']);

function buildGeo(els, b, P, E) {
  const F = { buildings: [], roads: [], intersections: [], water: [], green: [], pois: [], terrain: [] };
  const nodeTags = new Map(), ni = new Map();
  let coast = false;
  const dist = (p, q) => Math.hypot(P.x(p[0]) - P.x(q[0]), P.z(p[1]) - P.z(q[1]));
  const geom = polys => polys.length === 1 ? { type: 'Polygon', coordinates: polys[0] } : { type: 'MultiPolygon', coordinates: polys };
  const rnd = polys => polys.map(p => p.map(r => r.map(q => [r7(q[0]), r7(q[1])])));
  const lineZ = (pc, flat) => {
    let z = pc.map(p => E.at(p[0], p[1]));
    if (flat) { // bridges and tunnels: straight ramp between the end points
      const acc = [0]; for (let i = 1; i < pc.length; i++) acc.push(acc[i - 1] + dist(pc[i - 1], pc[i]));
      const L = acc[acc.length - 1] || 1; z = acc.map(a => z[0] + (z[z.length - 1] - z[0]) * a / L);
    }
    return { z, coords: pc.map((p, i) => [r7(p[0]), r7(p[1]), r1(z[i])]) };
  };

  for (const el of els) {
    const t = el.tags || {};
    if (el.type === 'node') {
      nodeTags.set(el.id, t);
      if (t.name && !t.highway && !SKIP_POI.has(t.amenity) && inBox(b, [el.lon, el.lat])) F.pois.push({ type: 'Feature',
        geometry: { type: 'Point', coordinates: [r7(el.lon), r7(el.lat), r1(E.at(el.lon, el.lat))] },
        properties: { id: 'n' + el.id, name: t.name, category: t.shop || t.amenity || t.tourism || t.office, brand: t.brand, cuisine: t.cuisine,
          opening_hours: t.opening_hours, website: t.website || t['contact:website'], phone: t.phone || t['contact:phone'] } });
      continue;
    }
    if (t.natural === 'coastline') { coast = true; continue; }

    if (t.building) {
      const polys = polysOf(el); if (!polys.length) continue;
      const o = polys[0][0], c = [o.reduce((s, p) => s + p[0], 0) / o.length, o.reduce((s, p) => s + p[1], 0) / o.length];
      if (!inBox(b, c)) continue;
      const area = polys.reduce((s, p) => s + Math.abs(ringArea(p[0], P)) - p.slice(1).reduce((q, h) => q + Math.abs(ringArea(h, P)), 0), 0);
      let h = num(t.height ?? t['building:height']), src = 'height tag';
      if (isNaN(h)) {
        const lv = parseFloat(t['building:levels']);
        if (!isNaN(lv)) { h = lv * 3.2 + (parseFloat(t['roof:levels']) || 0) * 1.5; src = 'levels'; }
        else { h = TYPE_H[t.building] ?? (area < 60 ? 4 : area < 150 ? 6.5 : area < 600 ? 9 : 12); src = 'estimated'; }
      }
      let mh = num(t.min_height); if (isNaN(mh)) mh = (parseFloat(t['building:min_level']) || 0) * 3.2;
      const ground = o.reduce((m, p) => Math.min(m, E.at(p[0], p[1])), 1e9), d = obb(o, P);
      F.buildings.push({ type: 'Feature', geometry: geom(rnd(polys)), properties: {
        id: el.type[0] + el.id, name: t.name, building: t.building, levels: t['building:levels'] ? +t['building:levels'] : undefined,
        height_m: r1(h), height_source: src, min_height_m: r1(mh), footprint_area_m2: Math.round(area),
        length_m: r1(Math.max(d.w, d.h)), width_m: r1(Math.min(d.w, d.h)), orientation_deg: Math.round(d.ang * 180 / Math.PI),
        volume_m3: Math.round(area * Math.max(h - mh, 0)), ground_elevation_m: r1(ground), top_elevation_m: r1(ground + h),
        use: t.shop || t.amenity || t.office || t.tourism || undefined,
        address: [t['addr:housenumber'], t['addr:street']].filter(Boolean).join(' ') || undefined } });
    } else if (t.highway && el.type === 'way' && el.geometry) {
      const hw = t.highway, base = hw.replace('_link', ''), g = ll(el.geometry);
      if (DRIVE.has(hw)) g.forEach((p, i) => {
        const k = el.nodes ? el.nodes[i] : p.join();
        let n = ni.get(k); if (!n) ni.set(k, n = { p, edges: 0, ways: new Set(), names: new Set(), rank: 9, round: false });
        n.edges += (i > 0) + (i < g.length - 1); n.ways.add(el.id);
        if (t.name || t.ref) n.names.add(t.name || t.ref);
        n.rank = Math.min(n.rank, RANK[base] ?? 8); if (t.junction === 'roundabout') n.round = true;
      });
      const tun = t.tunnel && t.tunnel !== 'no', brg = t.bridge && t.bridge !== 'no';
      const width = num(t.width) || (+t.lanes ? +t.lanes * 3.3 : 0) || WIDTH[base] || 2;
      for (const pc of clipLine(g, b)) {
        const { z, coords } = lineZ(pc, tun || brg);
        let len = 0; for (let i = 1; i < pc.length; i++) len += dist(pc[i - 1], pc[i]);
        F.roads.push({ type: 'Feature', geometry: { type: 'LineString', coordinates: coords }, properties: {
          id: 'w' + el.id, name: t.name, ref: t.ref, highway: hw, rank: RANK[base] ?? 8, lanes: +t.lanes || undefined, maxspeed: t.maxspeed,
          oneway: t.oneway, surface: t.surface, bridge: brg ? t.bridge : undefined, tunnel: tun ? t.tunnel : undefined,
          width_m: r1(width), length_m: Math.round(len), grade_pct: len ? r1(Math.abs(z[z.length - 1] - z[0]) / len * 100) : 0,
          elevation_min_m: r1(Math.min(...z)), elevation_max_m: r1(Math.max(...z)) } });
      }
    } else if (t.natural === 'water' || t.waterway === 'riverbank') {
      const polys = clipPolys(polysOf(el), b); if (!polys.length) continue;
      F.water.push({ type: 'Feature', geometry: geom(rnd(polys)), properties: { kind: t.water || 'water', name: t.name, elevation_m: r1(E.at(polys[0][0][0][0], polys[0][0][0][1])) } });
    } else if (t.waterway && el.type === 'way' && el.geometry) {
      const tun = t.tunnel || t.culvert;
      for (const pc of clipLine(ll(el.geometry), b)) {
        F.water.push({ type: 'Feature', geometry: { type: 'LineString', coordinates: lineZ(pc, false).coords },
          properties: { kind: 'waterway', waterway: t.waterway, name: t.name, width_m: num(t.width) || undefined, tunnel: tun || undefined } });
      }
    } else if (t.leisure || t.landuse || t.natural) {
      const polys = clipPolys(polysOf(el), b); if (!polys.length) continue;
      F.green.push({ type: 'Feature', geometry: geom(rnd(polys)), properties: { kind: t.leisure || t.landuse || t.natural, name: t.name } });
    }
  }

  // Intersections: nodes where drivable roads meet or end
  for (const [k, n] of ni) {
    if (!inBox(b, n.p)) continue;
    const tg = nodeTags.get(k) || {}, d = n.edges;
    const type = d === 1 ? (tg.highway === 'turning_circle' ? 'cul_de_sac' : 'dead_end')
      : n.round && d >= 3 ? 'roundabout_junction' : tg.highway === 'mini_roundabout' ? 'mini_roundabout'
      : d === 3 ? 'T_junction' : d === 4 ? 'crossroads' : d > 4 ? 'multi_way'
      : n.ways.size > 1 && tg.highway ? 'controlled_continuation' : null;
    if (!type) continue;
    F.intersections.push({ type: 'Feature', geometry: { type: 'Point', coordinates: [r7(n.p[0]), r7(n.p[1]), r1(E.at(n.p[0], n.p[1]))] }, properties: {
      id: String(k), type, degree: d, road_count: n.ways.size, roads: [...n.names].join(' / ') || undefined, highest_class: RNAME[n.rank],
      control: tg.highway === 'traffic_signals' ? 'traffic_signals' : tg.highway === 'stop' ? 'stop_sign' : tg.highway === 'give_way' ? 'give_way' : 'none' } });
  }

  // Elevation grid (41 x 41 points)
  for (let j = 0; j <= 40; j++) for (let i = 0; i <= 40; i++) {
    const lon = b.w + (b.e - b.w) * i / 40, lat = b.n - (b.n - b.s) * j / 40;
    F.terrain.push({ type: 'Feature', properties: { elevation_m: r1(E.at(lon, lat)) }, geometry: { type: 'Point', coordinates: [r7(lon), r7(lat)] } });
  }
  const out = { coast };
  for (const k in F) out[k] = { type: 'FeatureCollection', name: k, attribution: ATTR, features: F[k] };
  return out;
}

/* ---------- 6. 3D viewer ---------- */
const view = $('view');
let dirty = true; // render only when something changed
const renderer = new THREE.WebGLRenderer({ antialias: true, powerPreference: 'high-performance' });
renderer.setPixelRatio(Math.min(devicePixelRatio, 1.5));
renderer.shadowMap.enabled = true; renderer.shadowMap.autoUpdate = false; // shadows are computed once per city
view.appendChild(renderer.domElement);
const scene = new THREE.Scene(); scene.background = new THREE.Color(0xcfe3f2);
const camera = new THREE.PerspectiveCamera(50, 1, 1, 40000);
const controls = new OrbitControls(camera, renderer.domElement);
controls.enableDamping = true; controls.maxPolarAngle = Math.PI * 0.495;
scene.add(new THREE.HemisphereLight(0xffffff, 0x8a8f99, 1.7));
const sun = new THREE.DirectionalLight(0xfff3df, 2.4); sun.castShadow = true; scene.add(sun, sun.target);
const resize = () => { const w = view.clientWidth, h = view.clientHeight; renderer.setSize(w, h); camera.aspect = w / h; camera.updateProjectionMatrix(); dirty = true; };
addEventListener('resize', resize); resize();
renderer.setAnimationLoop(() => {
  if (controls.update() || dirty) { renderer.render(scene, camera); placeLabels(); dirty = false; }
});

let group = null, cur = null;
const lo = new THREE.Color('#e9e3d6'), hi = new THREE.Color('#36548f'), tmp = new THREE.Color();

// Flat map texture draped over the terrain: land use, water, roads
function paint(F, P, R, els, N) {
  const S = Math.min(4096, renderer.capabilities.maxTextureSize), k = S / (2 * R);
  const c = document.createElement('canvas'); c.width = c.height = S;
  const g = c.getContext('2d');
  const X = q => (P.x(q[0]) + R) * k, Y = q => (P.z(q[1]) + R) * k;
  g.fillStyle = '#ebe8df'; g.fillRect(0, 0, S, S);
  if (F.coast) { // sea = terrain at or below sea level
    const t = document.createElement('canvas'); t.width = t.height = N + 1;
    const tg = t.getContext('2d'), im = tg.createImageData(N + 1, N + 1);
    els.forEach((e, i) => im.data.set(e <= 0.3 ? [155, 203, 234, 255] : [235, 232, 223, 255], i * 4));
    tg.putImageData(im, 0, 0); g.imageSmoothingEnabled = true; g.drawImage(t, 0, 0, S, S);
  }
  g.lineJoin = g.lineCap = 'round';
  const fill = (feats, col) => {
    g.fillStyle = col;
    for (const f of feats) {
      const cs = f.geometry.type === 'Polygon' ? [f.geometry.coordinates] : f.geometry.coordinates;
      for (const p of cs) { g.beginPath(); for (const r of p) { r.forEach((q, i) => i ? g.lineTo(X(q), Y(q)) : g.moveTo(X(q), Y(q))); g.closePath(); } g.fill('evenodd'); }
    }
  };
  const stroke = (feats, col, w) => {
    for (const f of feats) {
      g.strokeStyle = typeof col === 'function' ? col(f.properties) : col; g.lineWidth = w(f.properties) * k; g.beginPath();
      f.geometry.coordinates.forEach((q, i) => i ? g.lineTo(X(q), Y(q)) : g.moveTo(X(q), Y(q))); g.stroke();
    }
  };
  fill(F.green.features, '#cfe3b4');
  fill(F.water.features.filter(f => f.geometry.type !== 'LineString'), '#9bcbea');
  stroke(F.water.features.filter(f => f.geometry.type === 'LineString' && !f.properties.tunnel), '#9bcbea',
    p => p.width_m || (p.waterway === 'river' ? 14 : p.waterway === 'canal' ? 9 : 3));
  const rd = F.roads.features.filter(f => !f.properties.tunnel).sort((a, b) => b.properties.rank - a.properties.rank);
  stroke(rd, '#b9b4a8', p => p.width_m + 1.6);
  stroke(rd, p => p.rank <= 1 ? '#f4a259' : p.rank <= 3 ? '#fbd88c' : p.rank >= 8 ? '#d9c7b0' : '#ffffff', p => p.width_m);
  return c;
}

function show3D(F, P, R, E) {
  if (group) { scene.remove(group); group.traverse(o => { o.geometry?.dispose(); if (o.material) { o.material.map?.dispose(); o.material.dispose(); } }); }
  group = new THREE.Group(); scene.add(group);

  // Terrain grid
  const N = 200, size = 2 * R, els = [];
  for (let j = 0; j <= N; j++) for (let i = 0; i <= N; i++) {
    const e = E.at(P.lon(-R + size * i / N), P.lat(-R + size * j / N)); els.push(F.coast ? Math.max(e, 0) : e);
  }
  const emin = els.reduce((a, v) => Math.min(a, v), 1e9), emax = els.reduce((a, v) => Math.max(a, v), -1e9);
  const pos = new Float32Array(els.length * 3), uvs = new Float32Array(els.length * 2);
  for (let j = 0, k = 0; j <= N; j++) for (let i = 0; i <= N; i++, k++) {
    pos.set([-R + size * i / N, els[k] - emin, -R + size * j / N], k * 3); uvs.set([i / N, 1 - j / N], k * 2);
  }
  const ind = [];
  for (let j = 0; j < N; j++) for (let i = 0; i < N; i++) { const a = j * (N + 1) + i, d = a + N + 1; ind.push(a, d, a + 1, d, d + 1, a + 1); }
  const tg = new THREE.BufferGeometry();
  tg.setAttribute('position', new THREE.BufferAttribute(pos, 3)); tg.setAttribute('uv', new THREE.BufferAttribute(uvs, 2));
  tg.setIndex(ind); tg.computeVertexNormals();
  const tex = new THREE.CanvasTexture(paint(F, P, R, els, N));
  tex.colorSpace = THREE.SRGBColorSpace; tex.anisotropy = renderer.capabilities.getMaxAnisotropy();
  const terrain = new THREE.Mesh(tg, new THREE.MeshStandardMaterial({ map: tex, roughness: 1 }));
  terrain.receiveShadow = true; group.add(terrain);

  // Side walls so the section reads as a solid block
  const per = [];
  for (let i = 0; i < N; i++) per.push(i);
  for (let j = 0; j < N; j++) per.push(j * (N + 1) + N);
  for (let i = N; i > 0; i--) per.push(N * (N + 1) + i);
  for (let j = N; j > 0; j--) per.push(j * (N + 1));
  const sp = [], si = [];
  per.forEach((v, k) => {
    const w = per[(k + 1) % per.length], o = sp.length / 3;
    sp.push(pos[v * 3], pos[v * 3 + 1], pos[v * 3 + 2], pos[w * 3], pos[w * 3 + 1], pos[w * 3 + 2], pos[v * 3], -8, pos[v * 3 + 2], pos[w * 3], -8, pos[w * 3 + 2]);
    si.push(o, o + 2, o + 1, o + 1, o + 2, o + 3);
  });
  const sg = new THREE.BufferGeometry(); sg.setAttribute('position', new THREE.Float32BufferAttribute(sp, 3)); sg.setIndex(si); sg.computeVertexNormals();
  group.add(new THREE.Mesh(sg, new THREE.MeshStandardMaterial({ color: '#5b5346', side: THREE.DoubleSide, roughness: 1 })));

  // Extruded buildings, merged into one mesh
  const feats = F.buildings.features, parts = [];
  feats.forEach((f, fi) => {
    const pr = f.properties, mh = pr.min_height_m || 0, y0 = pr.ground_elevation_m - emin + mh - 1;
    const polys = f.geometry.type === 'Polygon' ? [f.geometry.coordinates] : f.geometry.coordinates;
    for (const p of polys) {
      try {
        const mk = r => r.slice(0, -1).map(q => new THREE.Vector2(P.x(q[0]), -P.z(q[1])));
        const s = new THREE.Shape(mk(p[0])); s.holes = p.slice(1).map(h => new THREE.Path(mk(h)));
        let g = new THREE.ExtrudeGeometry(s, { depth: Math.max(pr.height_m - mh, 1) + 1, bevelEnabled: false });
        g.rotateX(-Math.PI / 2); g.translate(0, y0, 0);
        if (g.index) g = g.toNonIndexed();
        parts.push({ g, fi });
      } catch { /* skip malformed footprint */ }
    }
  });
  const nv = parts.reduce((s, p) => s + p.g.attributes.position.count, 0);
  const bp = new Float32Array(nv * 3), bn = new Float32Array(nv * 3), bc = new Float32Array(nv * 3), map = [];
  let o = 0;
  for (const p of parts) {
    const n = p.g.attributes.position.count;
    bp.set(p.g.attributes.position.array, o * 3); bn.set(p.g.attributes.normal.array, o * 3);
    tmp.copy(lo).lerp(hi, Math.min(feats[p.fi].properties.height_m / 120, 1));
    for (let v = o; v < o + n; v++) { bc[v * 3] = tmp.r; bc[v * 3 + 1] = tmp.g; bc[v * 3 + 2] = tmp.b; }
    map.push([o, p.fi]); o += n; p.g.dispose();
  }
  const bg = new THREE.BufferGeometry();
  bg.setAttribute('position', new THREE.BufferAttribute(bp, 3)); bg.setAttribute('normal', new THREE.BufferAttribute(bn, 3)); bg.setAttribute('color', new THREE.BufferAttribute(bc, 3));
  const bm = new THREE.Mesh(bg, new THREE.MeshStandardMaterial({ vertexColors: true, roughness: 0.9 }));
  bm.castShadow = bm.receiveShadow = true; group.add(bm);

  // Camera, sun, fog
  const relief = emax - emin;
  camera.near = Math.max(1, R / 200); camera.far = R * 20; camera.updateProjectionMatrix();
  camera.position.set(R * 0.9, relief + R * 0.8, R * 1.1); controls.target.set(0, relief / 2, 0); controls.maxDistance = R * 6;
  sun.position.set(R * 0.8, R * 1.2 + relief, R * 0.5); sun.target.position.set(0, 0, 0);
  const sc = sun.shadow.camera; sc.left = sc.bottom = -R * 1.3; sc.right = sc.top = R * 1.3; sc.near = 1; sc.far = R * 6 + relief; sc.updateProjectionMatrix();
  sun.shadow.mapSize.set(2048, 2048); sun.shadow.bias = -0.0005; sun.shadow.normalBias = 0.4;
  scene.fog = new THREE.Fog(0xcfe3f2, R * 3, R * 9);
  controls.update();
  cur = { F, P, emin, R, b: bm, t: terrain, map };
  makeLabels(F, P, emin);
  renderer.shadowMap.needsUpdate = true; dirty = true;
  return { emin, emax };
}

/* ---------- street and business labels (HTML overlay, decluttered on screen) ---------- */
const labelBox = document.createElement('div'); labelBox.id = 'labels'; view.appendChild(labelBox);
const want = { street: true, poi: true };
let labels = [];
$('t-street').onchange = e => { want.street = e.target.checked; dirty = true; };
$('t-poi').onchange = e => { want.poi = e.target.checked; dirty = true; };
function makeLabels(F, P, emin) {
  labelBox.innerHTML = ''; labels = [];
  const add = (kind, text, v, d, pri) => {
    const el = document.createElement('div'); el.className = 'lb ' + kind; el.textContent = text; labelBox.append(el);
    labels.push({ kind, el, v, d, pri, w: text.length * 6.5 + 8, dist: 0 });
  };
  const V = (c, up) => new THREE.Vector3(P.x(c[0]), c[2] - emin + up, P.z(c[1]));
  const best = new Map(); // one label per street name, on its longest piece
  for (const f of F.roads.features) { const p = f.properties; if (p.name && p.rank < 8 && (!best.has(p.name) || best.get(p.name).properties.length_m < p.length_m)) best.set(p.name, f); }
  [...best.values()].sort((a, b) => a.properties.rank - b.properties.rank || b.properties.length_m - a.properties.length_m).slice(0, 80).forEach(f => {
    const c = f.geometry.coordinates, m = c.length >> 1;
    add('street', f.properties.name, V(c[m], 3), V(c[m + 1] || c[m - 1], 3), f.properties.rank);
  });
  F.pois.features.slice(0, 250).forEach(f => add('poi', f.properties.name, V(f.geometry.coordinates, 7), null, 0));
  for (const f of F.buildings.features) {
    const p = f.properties; if (!p.name) continue;
    const r = f.geometry.type === 'Polygon' ? f.geometry.coordinates[0] : f.geometry.coordinates[0][0];
    const cx = r.reduce((s, q) => s + q[0], 0) / r.length, cy = r.reduce((s, q) => s + q[1], 0) / r.length;
    add('poi', p.name, new THREE.Vector3(P.x(cx), p.top_elevation_m - emin + 3, P.z(cy)), null, 0);
  }
}
function placeLabels() {
  if (!labels.length || !cur) return;
  const w = view.clientWidth, h = view.clientHeight, used = [], R = cur.R;
  for (const L of labels) L.dist = camera.position.distanceTo(L.v);
  labels.sort((a, b) => a.kind !== b.kind ? (a.kind === 'street' ? -1 : 1) : a.kind === 'street' ? a.pri - b.pri : a.dist - b.dist);
  for (const L of labels) {
    L.el.style.display = 'none';
    if (!want[L.kind] || L.dist > (L.kind === 'poi' ? R * 1.4 : R * 4)) continue;
    const p = L.v.clone().project(camera);
    if (p.z > 1) continue;
    const x = (p.x + 1) / 2 * w, y = (1 - p.y) / 2 * h;
    if (x < 0 || x > w || y < 0 || y > h) continue;
    const x0 = x - L.w / 2, y0 = y - 8;
    if (used.some(u => x0 < u[0] + u[2] && x0 + L.w > u[0] && y0 < u[1] + 16 && y0 + 16 > u[1])) continue;
    used.push([x0, y0, L.w]);
    let rot = 0;
    if (L.d) { // turn street names to follow the road, keeping text upright
      const q = L.d.clone().project(camera);
      rot = Math.atan2(-(q.y - p.y) * h, (q.x - p.x) * w);
      if (rot > Math.PI / 2) rot -= Math.PI; else if (rot < -Math.PI / 2) rot += Math.PI;
    }
    L.el.style.display = 'block';
    L.el.style.transform = `translate(${x}px, ${y}px) translate(-50%, -50%) rotate(${rot}rad)`;
  }
}

/* ---------- click to inspect ---------- */
const ray = new THREE.Raycaster();
let down = null;
const show = (title, o) => {
  $('info').innerHTML = `<b>${esc(title)}</b><table>${Object.entries(o).filter(([, v]) => v != null && v !== '')
    .map(([k, v]) => `<tr><td>${esc(k.replace(/_/g, ' '))}</td><td>${esc(v)}</td></tr>`).join('')}</table>`;
};
function segDist(px, pz, a, b) {
  const dx = b[0] - a[0], dz = b[1] - a[1], L = dx * dx + dz * dz;
  const t = L ? Math.max(0, Math.min(1, ((px - a[0]) * dx + (pz - a[1]) * dz) / L)) : 0;
  return Math.hypot(px - a[0] - t * dx, pz - a[1] - t * dz);
}
renderer.domElement.addEventListener('pointerdown', e => { down = [e.clientX, e.clientY]; });
renderer.domElement.addEventListener('pointerup', e => {
  if (!down || !cur || Math.hypot(e.clientX - down[0], e.clientY - down[1]) > 5) return;
  const r = renderer.domElement.getBoundingClientRect();
  ray.setFromCamera(new THREE.Vector2((e.clientX - r.left) / r.width * 2 - 1, -(e.clientY - r.top) / r.height * 2 + 1), camera);
  const hit = ray.intersectObjects([cur.b, cur.t])[0]; if (!hit) return;
  const { F, P, map } = cur;
  if (hit.object === cur.b) {
    const v = hit.faceIndex * 3; let a = 0, z = map.length - 1;
    while (a < z) { const m = (a + z + 1) >> 1; if (map[m][0] <= v) a = m; else z = m - 1; }
    return show('Building', F.buildings.features[map[a][1]].properties);
  }
  const x = hit.point.x, zz = hit.point.z; let best = null, bd = 15;
  for (const f of F.intersections.features) { const c = f.geometry.coordinates, d = Math.hypot(P.x(c[0]) - x, P.z(c[1]) - zz); if (d < bd) { bd = d; best = ['Intersection', f.properties]; } }
  if (!best) {
    bd = 12;
    for (const f of F.roads.features) {
      const c = f.geometry.coordinates;
      for (let i = 0; i < c.length - 1; i++) {
        const d = segDist(x, zz, [P.x(c[i][0]), P.z(c[i][1])], [P.x(c[i + 1][0]), P.z(c[i + 1][1])]);
        if (d < bd) { bd = d; best = ['Road', f.properties]; }
      }
    }
  }
  if (best) return show(best[0], best[1]);
  show('Ground', { elevation_m: r1(hit.point.y + cur.emin), latitude: r7(P.lat(zz)), longitude: r7(P.lon(x)) });
});

/* ---------- 7. downloads and main flow ---------- */
function offer(F, slug) {
  const dl = $('dl'); dl.innerHTML = '';
  const names = ['buildings', 'roads', 'intersections', 'water', 'green', 'pois', 'terrain'];
  const add = (name, fc) => {
    const a = document.createElement('a');
    a.textContent = `${name.replace('_', ' ')}.geojson (${fc.features.length.toLocaleString()})`;
    a.download = `${slug}_${name}.geojson`;
    a.href = URL.createObjectURL(new Blob([JSON.stringify(fc)], { type: 'application/geo+json' }));
    dl.append(a);
  };
  names.forEach(n => add(n, F[n]));
  add('all_layers', { type: 'FeatureCollection', attribution: ATTR,
    features: names.flatMap(n => F[n].features.map(f => ({ ...f, properties: { ...f.properties, layer: n } }))) });
}

/* ---------- city autocomplete (Photon, built for search-as-you-type) ---------- */
let picked = null, sugTimer = 0;
const sug = $('sug');
$('q').addEventListener('input', () => {
  picked = null; clearTimeout(sugTimer);
  const q = $('q').value.trim();
  if (q.length < 3 || /^-?\d/.test(q)) { sug.hidden = true; return; }
  sugTimer = setTimeout(async () => {
    try {
      const j = await (await fetch('https://photon.komoot.io/api/?limit=7&lang=en&q=' + encodeURIComponent(q))).json();
      if ($('q').value.trim() !== q) return;
      const seen = new Set(), items = [];
      for (const f of j.features) {
        const p = f.properties, label = [p.name, p.county !== p.name && p.county, p.state, p.country].filter(Boolean).join(', ');
        if (seen.has(label)) continue; seen.add(label);
        items.push({ label, lat: f.geometry.coordinates[1], lon: f.geometry.coordinates[0] });
      }
      sug.replaceChildren(...items.map(i => {
        const li = document.createElement('li'); li.textContent = i.label;
        li.onmousedown = e => { e.preventDefault(); picked = { lat: i.lat, lon: i.lon, display_name: i.label }; $('q').value = i.label; sug.hidden = true; };
        return li;
      }));
      sug.hidden = !items.length;
    } catch { sug.hidden = true; }
  }, 300);
});
$('q').addEventListener('blur', () => { sug.hidden = true; });

$('r').oninput = () => { $('rv').textContent = $('r').value; };
document.querySelectorAll('[data-q]').forEach(btn => { btn.onclick = () => { $('q').value = btn.dataset.q; $('f').requestSubmit(); }; });
$('f').onsubmit = async e => {
  e.preventDefault(); $('go').disabled = true; $('dl').innerHTML = ''; sug.hidden = true;
  const bar = $('bar'); bar.hidden = false; bar.value = 3;
  const creep = setInterval(() => { if (bar.value < 70) bar.value += (70 - bar.value) * 0.03; }, 300);
  try {
    say('Finding the place…');
    const pl = await geocode($('q').value); bar.value = 8;
    const R = +$('r').value, P = makeProj(pl.lat, pl.lon);
    const b = { s: pl.lat - R / P.mLat, n: pl.lat + R / P.mLat, w: pl.lon - R / P.mLon, e: pl.lon + R / P.mLon };
    say(`Downloading map data and terrain for ${pl.display_name}…`);
    const [els, E] = await Promise.all([overpass(b, $('foot').checked), loadElevation(b)]);
    clearInterval(creep); bar.value = 75; say('Building GeoJSON…'); await new Promise(r => setTimeout(r));
    const F = buildGeo(els, b, P, E);
    bar.value = 88; say('Building the 3D model…'); await new Promise(r => setTimeout(r));
    const { emin, emax } = show3D(F, P, R, E); bar.value = 100;
    offer(F, pl.display_name.split(',')[0].trim().toLowerCase().replace(/[^a-z0-9]+/g, '_').replace(/^_|_$/g, '') || 'city');
    $('info').innerHTML = '<small>Click a building, street or intersection to read its data.</small>';
    const missing = E.ok < E.total ? (E.ok ? ' Some terrain tiles failed, so parts of the ground are flat.' : ' Terrain tiles failed to load, so the ground is flat.') : '';
    say(`${pl.display_name}: ${F.buildings.features.length.toLocaleString()} buildings, ${F.roads.features.length.toLocaleString()} road segments, ${F.intersections.features.length.toLocaleString()} intersections. Ground ${Math.round(emin)}–${Math.round(emax)} m above sea level.${missing}`, !!missing);
  } catch (err) { say(err.message || String(err), true); bar.hidden = true; }
  clearInterval(creep); $('go').disabled = false; setTimeout(() => { if (bar.value === 100) bar.hidden = true; }, 1500);
};