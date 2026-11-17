'use strict';
/*
 * Moje Drogi — nagrywanie przejechanych dróg i statystyki ulic w miejscowościach.
 * Dane: IndexedDB w przeglądarce (trasy, cache geokodowania, liczba ulic w miejscowościach).
 * Mapa: OpenStreetMap. Nazwy ulic/miejscowości: Nominatim. Liczba wszystkich ulic: Overpass API.
 */

const KRAKOW = [50.0614, 19.9366];
const RADIUS_KM = 120;          // obszar, po którym jeździsz
const SAMPLE_M = 200;           // co ile metrów trasy pytamy o nazwę ulicy
const MIN_STEP_M = 8;           // pomijamy punkty bliżej niż 8 m od poprzedniego
const MAX_ACCURACY_M = 35;      // pomijamy niedokładne odczyty GPS
const NO_STREET = '(droga bez nazwy)';
const NO_TOWN = 'Poza miejscowością';
const NO_DISTRICT = 'Bez podziału na osiedla';
const TRIP_V = 2;               // wersja rozpoznawania ulic (2 = z osiedlami)
const GREEN = '#16A34A';        // kolor przejechanych dróg na mapie

const $ = (s) => document.querySelector(s);
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
const nf1 = new Intl.NumberFormat('pl-PL', { maximumFractionDigits: 1 });
const nf0 = new Intl.NumberFormat('pl-PL', { maximumFractionDigits: 0 });
const fmtKm = (m) => (m < 10000 ? nf1 : nf0).format(m / 1000) + ' km';
const fmtDate = (t) => new Date(t).toLocaleDateString('pl-PL', { day: 'numeric', month: 'short', year: 'numeric' });
const fmtDur = (ms) => {
  const s = Math.max(0, Math.round(ms / 1000));
  const h = Math.floor(s / 3600), m = Math.floor((s % 3600) / 60), sec = s % 60;
  return (h ? h + ':' : '') + String(m).padStart(h ? 2 : 1, '0') + ':' + String(sec).padStart(2, '0');
};
function plural(n, one, few, many) {
  if (n === 1) return one;
  const d = n % 10, dd = n % 100;
  return d >= 2 && d <= 4 && (dd < 12 || dd > 14) ? few : many;
}
function el(tag, attrs = {}, ...kids) {
  const e = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs)) {
    if (k === 'class') e.className = v;
    else if (k.startsWith('on')) e.addEventListener(k.slice(2), v);
    else if (k === 'style') e.style.cssText = v;
    else e.setAttribute(k, v);
  }
  for (const k of kids) if (k != null) e.append(k);
  return e;
}
function dist(a, b) {
  const R = 6371000, r = Math.PI / 180;
  const dLat = (b[0] - a[0]) * r, dLon = (b[1] - a[1]) * r;
  const x = Math.sin(dLat / 2) ** 2 + Math.cos(a[0] * r) * Math.cos(b[0] * r) * Math.sin(dLon / 2) ** 2;
  return 2 * R * Math.asin(Math.sqrt(x));
}
function trackLen(p) { let s = 0; for (let i = 1; i < p.length; i++) s += dist(p[i - 1], p[i]); return s; }

/* ---------------- IndexedDB ---------------- */
let idb;
function openDb() {
  return new Promise((res, rej) => {
    const r = indexedDB.open('moje-drogi', 1);
    r.onupgradeneeded = () => {
      const d = r.result;
      d.createObjectStore('trips', { keyPath: 'id' });
      d.createObjectStore('geo', { keyPath: 'k' });
      d.createObjectStore('towns', { keyPath: 'name' });
    };
    r.onsuccess = () => res(r.result);
    r.onerror = () => rej(r.error);
  });
}
function req(store, mode, fn) {
  return new Promise((res, rej) => {
    const t = idb.transaction(store, mode);
    const r = fn(t.objectStore(store));
    t.oncomplete = () => res(r ? r.result : undefined);
    t.onerror = () => rej(t.error);
    t.onabort = () => rej(t.error);
  });
}
const dbAll = (s) => req(s, 'readonly', (o) => o.getAll());
const dbGet = (s, k) => req(s, 'readonly', (o) => o.get(k));
const dbPut = (s, v) => req(s, 'readwrite', (o) => o.put(v));
const dbDel = (s, k) => req(s, 'readwrite', (o) => o.delete(k));

/* ---------------- Stan ---------------- */
const state = {
  trips: [],
  townMeta: {},       // name -> { total, names[], areaName }
  agg: {},            // name -> { name, m, streets: {name: {m, n}}, trips: [], last, pt }
  rec: null,          // nagrywana trasa
  selected: null,     // wybrana miejscowość
  showVisited: true,
  follow: true,
  sort: 'last',
  detailTab: 'streets',
  focus: null,        // miejscowość wybrana w wyszukiwarce: { name, lat, lon }
  filter: '',         // filtr listy miejscowości
  streetFilter: '',   // filtr zbiorczej listy ulic
};

// porównywanie nazw bez wielkości liter i polskich znaków („lodz” znajdzie „Łódź”)
const norm = (s) => s.toLowerCase().replace(/ł/g, 'l').normalize('NFD').replace(/[̀-ͯ]/g, '').trim();

function setStatus(msg) { $('#status').textContent = msg || ''; }

/* ---------------- Mapa ---------------- */
let map, visitedLayer, recLine, posMarker, accCircle;
function initMap() {
  map = L.map('map', { preferCanvas: true, zoomControl: false, attributionControl: true }).setView(KRAKOW, 9);
  L.tileLayer('https://tile.openstreetmap.org/{z}/{x}/{y}.png', {
    maxZoom: 19,
    attribution: '&copy; <a href="https://www.openstreetmap.org/copyright">OpenStreetMap</a>',
  }).addTo(map);
  L.circle(KRAKOW, { radius: RADIUS_KM * 1000, color: '#64748B', weight: 1.5, dashArray: '6 8', fill: false, interactive: false }).addTo(map);
  visitedLayer = L.layerGroup().addTo(map);
  recLine = L.polyline([], { color: '#EA580C', weight: 6, opacity: 0.95 }).addTo(map);
  map.on('dragstart', () => setFollow(false));
}
function drawTrips() {
  visitedLayer.clearLayers();
  for (const t of state.trips) {
    if (t.recording || t.points.length < 2) continue;
    L.polyline(t.points.map((p) => [p[0], p[1]]), { color: GREEN, weight: 5, opacity: 0.85, interactive: false }).addTo(visitedLayer);
  }
}
function showPos(lat, lon, acc) {
  if (!posMarker) {
    posMarker = L.marker([lat, lon], { icon: L.divIcon({ className: '', html: '<div class="pos-dot"></div>', iconSize: [18, 18], iconAnchor: [9, 9] }), interactive: false, keyboard: false }).addTo(map);
    accCircle = L.circle([lat, lon], { radius: acc, color: '#EA580C', weight: 1, fillOpacity: 0.08, interactive: false }).addTo(map);
  } else {
    posMarker.setLatLng([lat, lon]);
    accCircle.setLatLng([lat, lon]).setRadius(acc);
  }
  if (state.follow) map.setView([lat, lon], Math.max(map.getZoom(), 16), { animate: true });
}
function setFollow(on) {
  state.follow = on;
  $('#btn-follow').classList.toggle('on', on);
  $('#btn-follow').setAttribute('aria-pressed', String(on));
}
function fitTown(name) {
  const T = state.agg[name];
  if (!T) return;
  const pts = [];
  for (const t of T.trips) for (const p of t.points) pts.push([p[0], p[1]]);
  if (!pts.length) return;
  setFollow(false);
  showView('view-map');
  map.fitBounds(L.latLngBounds(pts), { padding: [30, 30], maxZoom: 16 });
}

/* ---------------- Nagrywanie GPS ---------------- */
let watchId = null, wakeLock = null, recTimer = null, lastSave = 0;

async function requestWake() {
  try { if ('wakeLock' in navigator) wakeLock = await navigator.wakeLock.request('screen'); } catch { wakeLock = null; }
}
document.addEventListener('visibilitychange', () => {
  if (document.visibilityState === 'visible' && state.rec && !wakeLock) requestWake();
  if (document.visibilityState === 'hidden' && state.rec) dbPut('trips', state.rec).catch(() => {});
});

async function startRec() {
  if (!('geolocation' in navigator)) { setStatus('Ta przeglądarka nie udostępnia GPS.'); return; }
  if (!window.isSecureContext) { setStatus('GPS działa tylko pod adresem https://. Otwórz aplikację z bezpiecznego adresu.'); return; }
  const trip = { id: 't' + Date.now(), start: Date.now(), end: null, points: [], recording: true, processed: false, source: 'gps' };
  state.rec = trip;
  recLine.setLatLngs([]);
  setFollow(true);
  watchId = navigator.geolocation.watchPosition(onPos, onPosErr, { enableHighAccuracy: true, maximumAge: 0, timeout: 30000 });
  requestWake();
  recTimer = setInterval(updateRecUi, 1000);
  updateRecUi();
  setStatus('Szukam sygnału GPS…');
  await dbPut('trips', trip);
}

function onPos(pos) {
  const { latitude: lat, longitude: lon, accuracy } = pos.coords;
  showPos(lat, lon, accuracy);
  const tr = state.rec;
  if (!tr) return;
  if (accuracy > MAX_ACCURACY_M) { setStatus(`Słaby sygnał GPS (±${Math.round(accuracy)} m), czekam…`); return; }
  const p = [+lat.toFixed(6), +lon.toFixed(6), pos.timestamp];
  const last = tr.points[tr.points.length - 1];
  if (last) {
    const d = dist(last, p);
    if (d < MIN_STEP_M) return;
    const dt = (p[2] - last[2]) / 1000;
    if (dt > 0 && d / dt > 70) return; // skok > 250 km/h — błąd GPS
  }
  tr.points.push(p);
  recLine.addLatLng([p[0], p[1]]);
  setStatus('Nagrywam. Trzymaj aplikację otwartą na ekranie.');
  if (Date.now() - lastSave > 15000) { lastSave = Date.now(); dbPut('trips', tr).catch(() => {}); }
}

function onPosErr(err) {
  if (err.code === 1) {
    setStatus('Brak zgody na lokalizację. Włącz ją w ustawieniach przeglądarki dla tej strony.');
    stopRec();
  } else {
    setStatus('Chwilowo brak sygnału GPS, próbuję dalej…');
  }
}

async function stopRec() {
  const tr = state.rec;
  if (watchId != null) navigator.geolocation.clearWatch(watchId);
  watchId = null;
  clearInterval(recTimer);
  try { await wakeLock?.release(); } catch {}
  wakeLock = null;
  state.rec = null;
  updateRecUi();
  if (!tr) return;
  tr.recording = false;
  tr.end = Date.now();
  tr.km = trackLen(tr.points);
  recLine.setLatLngs([]);
  if (tr.points.length < 3) {
    await dbDel('trips', tr.id);
    setStatus('Trasa była za krótka, nie zapisałem jej.');
    return;
  }
  await dbPut('trips', tr);
  state.trips.push(tr);
  drawTrips();
  setStatus(`Zapisano trasę: ${fmtKm(tr.km)}. Rozpoznaję ulice…`);
  processPending();
}

function updateRecUi() {
  const on = !!state.rec;
  $('#btn-rec').classList.toggle('on', on);
  $('#rec-label').textContent = on
    ? `Zatrzymaj · ${fmtDur(Date.now() - state.rec.start)} · ${fmtKm(trackLen(state.rec.points))}`
    : 'Rozpocznij nagrywanie trasy';
}

/* ---------------- Rozpoznawanie ulic (Nominatim) ---------------- */
let lastNominatim = 0, processing = false;

async function reverse(p) {
  const k = p[0].toFixed(4) + ',' + p[1].toFixed(4);
  const cached = await dbGet('geo', k);
  if (cached && 'district' in cached) return cached;
  const wait = lastNominatim + 1100 - Date.now();   // limit Nominatim: 1 zapytanie na sekundę
  if (wait > 0) await sleep(wait);
  lastNominatim = Date.now();
  const url = `https://nominatim.openstreetmap.org/reverse?format=jsonv2&lat=${p[0]}&lon=${p[1]}&zoom=17&addressdetails=1&accept-language=pl`;
  const r = await fetch(url);
  if (!r.ok) throw new Error('nominatim ' + r.status);
  const j = await r.json();
  const a = j.address || {};
  const v = {
    k,
    road: a.road || a.pedestrian || a.footway || null,
    town: a.city || a.town || a.village || a.hamlet || a.municipality || null,
    district: a.suburb || a.city_district || a.quarter || null,
  };
  await dbPut('geo', v);
  return v;
}

async function processTrip(t) {
  const pts = t.points;
  const samples = [{ p: pts[0], d: 0 }];
  let since = 0;
  for (let i = 1; i < pts.length; i++) {
    since += dist(pts[i - 1], pts[i]);
    if (since >= SAMPLE_M) { samples.push({ p: pts[i], d: since }); since = 0; }
  }
  if (since > 0) samples.push({ p: pts[pts.length - 1], d: since });

  const streets = {}, dstreets = {}, townPts = {};
  for (let i = 0; i < samples.length; i++) {
    setStatus(`Rozpoznaję ulice: ${i + 1} z ${samples.length}`);
    const g = await reverse(samples[i].p);
    const town = g.town || NO_TOWN;
    const street = g.road || NO_STREET;
    streets[town] ??= {};
    streets[town][street] = (streets[town][street] || 0) + samples[i].d;
    const district = g.district || NO_DISTRICT;
    dstreets[town] ??= {};
    dstreets[town][district] ??= {};
    dstreets[town][district][street] = (dstreets[town][district][street] || 0) + samples[i].d;
    townPts[town] ??= [samples[i].p[0], samples[i].p[1]];
  }
  t.streets = streets;
  t.dstreets = dstreets;
  t.townPts = townPts;
  t.v = TRIP_V;
  t.km = trackLen(pts);
  t.processed = true;
  await dbPut('trips', t);
}

async function processPending() {
  if (processing) return;
  processing = true;
  try {
    for (const t of state.trips.filter((x) => !x.processed && !x.recording)) {
      await processTrip(t);
      rebuild();
    }
    if (!state.rec) setStatus('');
  } catch (e) {
    console.warn(e);
    if (!state.rec) setStatus('Nie mogę teraz rozpoznać ulic (brak internetu?). Spróbuję ponownie później.');
  } finally {
    processing = false;
  }
}
window.addEventListener('online', processPending);

/* ---------------- Wszystkie ulice w miejscowości (Overpass) ---------------- */
const OVERPASS = [
  'https://overpass-api.de/api/interpreter',
  'https://maps.mail.ru/osm/tools/overpass/api/interpreter',
  'https://overpass.kumi.systems/api/interpreter',
];
async function overpass(q) {
  let lastErr;
  for (const url of OVERPASS) {   // publiczne serwery bywają przeciążone — próbujemy po kolei
    try {
      const r = await fetch(url, {
        method: 'POST',
        headers: { 'Content-Type': 'application/x-www-form-urlencoded' },
        body: 'data=' + encodeURIComponent(q),
      });
      if (!r.ok) throw new Error('overpass ' + r.status);
      return await r.json();
    } catch (e) { lastErr = e; }
  }
  throw lastErr;
}

/* ---------------- Osiedla: przypisanie każdej ulicy do osiedla ---------------- */
// Najpierw granica osiedla (jeśli jest w OpenStreetMap), inaczej najbliższy punkt osiedla do 2,5 km.
const DISTRICT_RANK = { suburb: 0, city_district: 1, borough: 1, quarter: 2 };
function ringSegments(e) {
  const segs = [];
  const add = (g) => { for (let i = 1; i < g.length; i++) segs.push([g[i - 1].lat, g[i - 1].lon, g[i].lat, g[i].lon]); };
  if (e.type === 'way' && e.geometry) add(e.geometry);
  if (e.type === 'relation') for (const m of e.members || []) if (m.type === 'way' && m.geometry && m.role !== 'label' && m.role !== 'admin_centre') add(m.geometry);
  return segs;
}
// reguła parzystości: działa na pierścieniach złożonych z wielu odcinków i uwzględnia „dziury”
function insideSegments(lat, lon, segs) {
  let inside = false;
  for (const [y1, x1, y2, x2] of segs) {
    if ((y1 > lat) !== (y2 > lat) && lon < x1 + ((lat - y1) * (x2 - x1)) / (y2 - y1)) inside = !inside;
  }
  return inside;
}
function assignDistricts(els, ways) {
  const polys = els
    .filter((e) => (e.type === 'relation' || e.type === 'way') && !e.tags?.highway && e.tags?.name)
    .map((e) => {
      const segs = ringSegments(e);
      const lats = segs.flatMap((x) => [x[0], x[2]]), lons = segs.flatMap((x) => [x[1], x[3]]);
      const rank = e.tags.place ? DISTRICT_RANK[e.tags.place] ?? 3 : 1;
      return { name: e.tags.name, rank, segs, box: [Math.min(...lats), Math.max(...lats), Math.min(...lons), Math.max(...lons)] };
    })
    .filter((p) => p.segs.length >= 3)
    .sort((a, b) => a.rank - b.rank);
  const nodes = els.filter((e) => e.type === 'node' && e.tags?.name && e.lat != null);
  if (!polys.length && !nodes.length) return null;
  const out = {};
  for (const w of ways) {
    const c = w.center;
    let d = null;
    if (c) {
      const p = polys.find((p) => c.lat >= p.box[0] && c.lat <= p.box[1] && c.lon >= p.box[2] && c.lon <= p.box[3] && insideSegments(c.lat, c.lon, p.segs));
      if (p) d = p.name;
      else {
        let best = 2500;
        for (const n of nodes) { const m = dist([c.lat, c.lon], [n.lat, n.lon]); if (m < best) { best = m; d = n.tags.name; } }
      }
    }
    (out[d || NO_DISTRICT] ??= new Set()).add(w.tags.name);
  }
  const res = {};
  for (const [d, set] of Object.entries(out)) res[d] = [...set].sort((a, b) => a.localeCompare(b, 'pl'));
  return res;
}

/** Procent przejechanych ulic w każdym osiedlu. */
function districtProgress(T, meta) {
  if (!T || !meta?.districts) return null;
  const streetDs = {};
  for (const [d, names] of Object.entries(meta.districts)) for (const s of names) (streetDs[s] ??= new Set()).add(d);
  const seenIn = {};
  for (const D of Object.values(T.districts)) for (const s of Object.keys(D.streets)) (seenIn[s] ??= new Set()).add(D.name);
  return Object.entries(meta.districts).map(([d, names]) => {
    // ulica tylko w jednym osiedlu liczy się zawsze; ulica przez kilka osiedli — tam, gdzie nią jechałeś
    const visited = names.filter((s) => T.streets[s] && (streetDs[s].size === 1 || seenIn[s]?.has(d)));
    const vs = new Set(visited);
    return { name: d, total: names.length, hit: visited.length, pct: Math.round((visited.length / names.length) * 100), visited, missing: names.filter((s) => !vs.has(s)) };
  }).sort((a, b) => (a.name === NO_DISTRICT) - (b.name === NO_DISTRICT) || b.pct - a.pct || a.name.localeCompare(b.name, 'pl'));
}

async function countStreets(name) {
  const T = state.agg[name];
  if (!T?.pt) throw new Error('brak punktu');
  const [lat, lon] = T.pt;
  const areas = await overpass(
    `[out:json][timeout:60];is_in(${lat},${lon})->.a;area.a[boundary=administrative][admin_level~"^(7|8|9|10)$"];out tags;`
  );
  const list = (areas.elements || []).filter((e) => e.tags?.name);
  if (!list.length) throw new Error('brak granic');
  const lc = name.toLowerCase();
  const byLevel = (a, b) => (+b.tags.admin_level) - (+a.tags.admin_level);
  const area =
    list.filter((e) => e.tags.name.toLowerCase() === lc).sort(byLevel)[0] ||
    list.filter((e) => e.tags.name.toLowerCase().includes(lc)).sort(byLevel)[0] ||
    list.sort(byLevel)[0];
  // ulice (ze środkiem odcinka) + osiedla: granice (out geom) i punkty
  const res = await overpass(
    `[out:json][timeout:180];area(id:${area.id})->.t;` +
    `way(area.t)[highway~"^(motorway|trunk|primary|secondary|tertiary|unclassified|residential|living_street|road)$"][name];out tags center;` +
    `(relation(area.t)[boundary=administrative][admin_level~"^(9|10|11)$"][name];` +
    `relation(area.t)[place~"^(suburb|quarter|city_district|borough)$"][name];` +
    `way(area.t)[place~"^(suburb|quarter|city_district|borough)$"][name];);out geom;` +
    `node(area.t)[place~"^(suburb|quarter|city_district|borough)$"][name];out;`
  );
  const els = res.elements || [];
  const ways = els.filter((e) => e.type === 'way' && e.tags?.highway && e.tags?.name);
  const names = [...new Set(ways.map((w) => w.tags.name))].sort((a, b) => a.localeCompare(b, 'pl'));
  const meta = { name, total: names.length, names, areaName: area.tags.name, checked: Date.now(), districts: assignDistricts(els, ways) };
  await dbPut('towns', meta);
  state.townMeta[name] = meta;
}

/* ---------------- Agregacja ---------------- */
function rebuild() {
  const agg = {};
  for (const t of state.trips) {
    if (!t.streets) continue;
    for (const [town, sts] of Object.entries(t.streets)) {
      const T = (agg[town] ??= { name: town, m: 0, streets: {}, districts: {}, trips: [], last: 0, pt: null });
      T.trips.push(t);
      T.last = Math.max(T.last, t.start);
      T.pt ??= t.townPts?.[town] || null;
      for (const [s, m] of Object.entries(sts)) {
        T.m += m;
        const S = (T.streets[s] ??= { m: 0, n: 0 });
        S.m += m;
        S.n += 1;
      }
      // osiedla (trasy rozpoznane przed wersją 2 trafiają do „bez podziału”, dopóki się nie przeliczą)
      const byDistrict = t.dstreets?.[town] || { [NO_DISTRICT]: sts };
      for (const [d, dsts] of Object.entries(byDistrict)) {
        const D = (T.districts[d] ??= { name: d, m: 0, streets: {} });
        for (const [s, m] of Object.entries(dsts)) {
          D.m += m;
          const S = (D.streets[s] ??= { m: 0, n: 0, last: 0 });
          S.m += m;
          S.n += 1;
          S.last = Math.max(S.last, t.start);
        }
      }
    }
  }
  state.agg = agg;
  drawTrips();
  renderAll();
}

const namedCount = (T) => Object.keys(T.streets).filter((s) => s !== NO_STREET).length;
function progress(T) {
  const meta = state.townMeta[T.name];
  if (!meta || !meta.total) return null;
  const set = new Set(meta.names);
  const hit = Object.keys(T.streets).filter((s) => set.has(s)).length;
  return { hit, total: meta.total, pct: Math.round((hit / meta.total) * 100) };
}
function townsSorted() {
  const arr = Object.values(state.agg).filter((T) => T.name !== NO_TOWN);
  if (state.sort === 'name') arr.sort((a, b) => a.name.localeCompare(b.name, 'pl'));
  else if (state.sort === 'streets') arr.sort((a, b) => namedCount(b) - namedCount(a));
  else arr.sort((a, b) => b.last - a.last);
  return arr;
}

/* ---------------- Widoki ---------------- */
function renderAll() { renderSheet(); renderTowns(); renderTown(); renderStreets(); }

function sheetTown() {
  if (state.focus) return state.agg[state.focus.name] || null;
  return [...townsSorted()].sort((a, b) => b.last - a.last)[0] || null;
}

function renderSheet() {
  const towns = townsSorted();
  const recent = sheetTown();
  const total = state.trips.reduce((s, t) => s + (t.km || 0), 0);
  $('#st-towns').textContent = towns.length;
  $('#st-total').textContent = fmtKm(total);
  if (state.focus && !recent) {
    $('#sheet-label').textContent = `${state.focus.name} · wyszukana`;
    $('#sheet-big').textContent = '0 ulic';
    $('#st-km').textContent = '0 km';
    return;
  }
  if (!recent) {
    $('#sheet-label').textContent = 'Jeszcze brak przejazdów';
    $('#sheet-big').textContent = '0 ulic';
    $('#st-km').textContent = '0 km';
    return;
  }
  const pr = progress(recent);
  const n = namedCount(recent);
  $('#sheet-label').textContent = `${recent.name} · ${state.focus ? 'wyszukana' : 'ostatnio odwiedzona'}`;
  $('#sheet-big').textContent = pr ? `${pr.pct}% ulic` : `${n} ${plural(n, 'ulica', 'ulice', 'ulic')}`;
  $('#st-km').textContent = fmtKm(recent.m);
}

function renderTowns() {
  const towns = townsSorted();
  const allStreets = towns.reduce((s, T) => s + namedCount(T), 0);
  $('#t-towns').textContent = towns.length;
  $('#t-km').textContent = fmtKm(state.trips.reduce((s, t) => s + (t.km || 0), 0));
  $('#t-streets').textContent = allStreets;
  $('#towns-empty').hidden = towns.length > 0;
  const f = norm(state.filter);
  const shown = f ? towns.filter((T) => norm(T.name).includes(f)) : towns;
  $('#towns-nomatch').hidden = !(towns.length && !shown.length);
  const ul = $('#town-list');
  ul.replaceChildren();
  for (const T of shown) {
    const pr = progress(T);
    const n = namedCount(T);
    const bar = el('i');
    if (pr) { bar.style.width = pr.pct + '%'; if (pr.pct >= 100) bar.className = 'full'; }
    else bar.style.width = '0%';
    const meta = pr
      ? `${pr.hit} z ${pr.total} ulic · ${fmtKm(T.m)} · ${fmtDate(T.last)}`
      : `${n} ${plural(n, 'ulica', 'ulice', 'ulic')} · ${fmtKm(T.m)} · ${fmtDate(T.last)}`;
    ul.append(el('li', {},
      el('button', { class: 'town', type: 'button', onclick: () => openTown(T.name) },
        el('span', { class: 'town-top' },
          el('span', { class: 'town-name' }, T.name),
          el('span', { class: 'town-val' }, pr ? pr.pct + '%' : String(n))),
        el('span', { class: 'bar' }, bar),
        el('span', { class: 'town-meta' }, meta))));
  }
}

function openTown(name) { state.selected = name; renderTown(); showView('view-town'); }

function renderTown() {
  const towns = townsSorted();
  if (!state.selected || !state.agg[state.selected]) state.selected = towns[0]?.name || null;
  const T = state.agg[state.selected];
  const list = $('#d-list');
  list.replaceChildren();
  $('#btn-count').disabled = !T;
  $('#btn-show').disabled = !T;
  if (!T) {
    $('#d-name').textContent = 'Brak danych';
    $('#d-sub').textContent = 'Nagraj pierwszą trasę';
    $('#d-area').textContent = '';
    return;
  }
  const pr = progress(T);
  const meta = state.townMeta[T.name];
  const n = namedCount(T);
  const first = Math.min(...T.trips.map((t) => t.start));
  $('#d-name').textContent = T.name;
  $('#d-sub').textContent = `pierwszy przejazd ${fmtDate(first)} · ${T.trips.length} ${plural(T.trips.length, 'przejazd', 'przejazdy', 'przejazdów')}`;
  $('#d-streets').textContent = pr ? pr.hit : n;
  $('#d-total').textContent = meta ? meta.total : '?';
  $('#d-km').textContent = fmtKm(T.m);
  $('#d-trips').textContent = T.trips.length;
  const pct = pr ? pr.pct : 0;
  $('#d-ring-fg').setAttribute('stroke-dasharray', `${(pct / 100) * 251.3} 251.3`);
  $('#d-ring-txt').textContent = pr ? pct + '%' : '?';
  $('#d-ring').setAttribute('aria-label', pr ? `Przejechane ${pct}% ulic` : 'Postęp nieznany — policz wszystkie ulice');
  $('#btn-count').textContent = meta ? 'Policz ulice ponownie' : 'Policz wszystkie ulice';
  $('#d-area').textContent = meta
    ? `Ulice liczone w granicach: ${meta.areaName} (OpenStreetMap, ${fmtDate(meta.checked)}).` +
      (meta.districts === undefined ? ' Policz ponownie, żeby zobaczyć procent dla każdego osiedla.'
        : meta.districts === null ? ' OpenStreetMap nie dzieli tej miejscowości na osiedla.' : '')
    : 'Kliknij „Policz wszystkie ulice”, żeby zobaczyć, jaki procent miejscowości już przejechałeś.';

  $('#tab-streets').setAttribute('aria-selected', String(state.detailTab === 'streets'));
  $('#tab-trips').setAttribute('aria-selected', String(state.detailTab === 'trips'));

  const dp = districtProgress(T, meta);
  if (state.detailTab === 'streets' && dp) {
    // tryb z procentami osiedli: każde osiedle z paskiem, przejechane i jeszcze nie
    const inAny = new Set(Object.values(meta.districts).flat());
    for (const D of dp) {
      list.append(districtHead(D));
      for (const s of D.visited) {
        const v = T.streets[s];
        list.append(el('li', {}, el('span', { class: 'd' }), el('span', { class: 'n' }, s), el('span', { class: 'm' }, `${v.n}× · ${fmtKm(v.m)}`)));
      }
      for (const s of D.missing) {
        list.append(el('li', {}, el('span', { class: 'd no' }), el('span', { class: 'n' }, s), el('span', { class: 'm' }, 'jeszcze nie')));
      }
    }
    const other = Object.entries(T.streets).filter(([s]) => !inAny.has(s)).sort((a, b) => b[1].m - a[1].m);
    if (other.length) list.append(groupHead('Inne przejechane drogi', other.length, other.reduce((x, [, v]) => x + v.m, 0)));
    for (const [s, v] of other) {
      list.append(el('li', {}, el('span', { class: 'd' }), el('span', { class: 'n' }, s), el('span', { class: 'm' }, `${v.n}× · ${fmtKm(v.m)}`)));
    }
  } else if (state.detailTab === 'streets') {
    const districts = districtsSorted(T);
    const showHeads = !(districts.length === 1 && districts[0].name === NO_DISTRICT);
    for (const D of districts) {
      const streets = Object.entries(D.streets).sort((a, b) => b[1].m - a[1].m);
      if (showHeads) list.append(groupHead(D.name, streets.filter(([s]) => s !== NO_STREET).length, D.m));
      for (const [s, v] of streets) {
        list.append(el('li', {}, el('span', { class: 'd' }), el('span', { class: 'n' }, s),
          el('span', { class: 'm' }, `${v.n}× · ${fmtKm(v.m)}`)));
      }
    }
    if (meta) {
      const missing = meta.names.filter((s) => !T.streets[s]);
      if (missing.length) list.append(groupHead('Jeszcze nie przejechane', missing.length, null));
      for (const s of missing) {
        list.append(el('li', {}, el('span', { class: 'd no' }), el('span', { class: 'n' }, s), el('span', { class: 'm' }, 'jeszcze nie')));
      }
    }
  } else {
    const trips = [...T.trips].sort((a, b) => b.start - a.start);
    for (const t of trips) {
      const d = new Date(t.start);
      const inTown = Object.values(t.streets[T.name] || {}).reduce((s, m) => s + m, 0);
      const nSt = Object.keys(t.streets[T.name] || {}).filter((s) => s !== NO_STREET).length;
      let armed = false;
      const del = el('button', { class: 'del', type: 'button' }, 'Usuń');
      del.addEventListener('click', async () => {
        if (!armed) { armed = true; del.textContent = 'Na pewno?'; setTimeout(() => { armed = false; del.textContent = 'Usuń'; }, 3000); return; }
        await dbDel('trips', t.id);
        state.trips = state.trips.filter((x) => x.id !== t.id);
        rebuild();
      });
      list.append(el('li', {},
        el('span', { class: 'date' }, el('b', {}, String(d.getDate())), el('span', {}, d.toLocaleDateString('pl-PL', { month: 'short' }))),
        el('span', { class: 'n' }, `${fmtKm(inTown)} w miejscowości, ${nSt} ${plural(nSt, 'ulica', 'ulice', 'ulic')}`,
          el('br'), el('span', { class: 'm' }, `cała trasa ${fmtKm(t.km || 0)}${t.end ? ' · ' + fmtDur(t.end - t.start) : ''}${t.source === 'gpx' ? ' · GPX' : ''}`)),
        del));
    }
  }
}

function districtsSorted(T) {
  return Object.values(T.districts).sort((a, b) =>
    (a.name === NO_DISTRICT) - (b.name === NO_DISTRICT) || b.m - a.m);
}
function districtHead(D) {
  const bar = el('i');
  bar.style.width = D.pct + '%';
  if (D.pct >= 100) bar.className = 'full';
  return el('li', { class: 'group district' },
    el('span', { class: 'dh-top' },
      el('span', { class: 'n' }, D.name),
      el('span', { class: 'dh-pct' }, D.pct + '%')),
    el('span', { class: 'bar' }, bar),
    el('span', { class: 'm' }, `${D.hit} z ${D.total} ${plural(D.total, 'ulicy', 'ulic', 'ulic')}`));
}
function groupHead(name, n, m) {
  return el('li', { class: 'group' },
    el('span', { class: 'n' }, name),
    el('span', { class: 'm' }, `${n} ${plural(n, 'ulica', 'ulice', 'ulic')}${m != null ? ' · ' + fmtKm(m) : ''}`));
}

/* ---------------- Wszystkie ulice w jednym miejscu ---------------- */
function allStreetRows() {
  const rows = [];
  for (const T of Object.values(state.agg)) {
    if (T.name === NO_TOWN) continue;
    for (const D of Object.values(T.districts)) {
      for (const [s, v] of Object.entries(D.streets)) {
        if (s === NO_STREET) continue;
        rows.push({ town: T.name, district: D.name, street: s, n: v.n, m: v.m, last: v.last });
      }
    }
  }
  return rows;
}

function renderStreets() {
  const rows = allStreetRows();
  const f = norm(state.streetFilter || '');
  const shown = f ? rows.filter((r) => norm(`${r.street} ${r.district} ${r.town}`).includes(f)) : rows;
  const uniq = new Set(rows.map((r) => r.town + '|' + r.street)).size;
  $('#s-count').textContent = uniq;
  $('#s-towns').textContent = new Set(rows.map((r) => r.town)).size;
  $('#s-districts').textContent = new Set(rows.filter((r) => r.district !== NO_DISTRICT).map((r) => r.town + '|' + r.district)).size;
  $('#streets-empty').hidden = rows.length > 0;
  $('#streets-nomatch').hidden = !(rows.length && !shown.length);
  $('#btn-csv').disabled = !rows.length;

  const box = $('#all-streets');
  box.replaceChildren();
  const byTown = new Map();
  for (const r of shown) {
    if (!byTown.has(r.town)) byTown.set(r.town, new Map());
    const dm = byTown.get(r.town);
    if (!dm.has(r.district)) dm.set(r.district, []);
    dm.get(r.district).push(r);
  }
  const towns = [...byTown.keys()].sort((a, b) => a.localeCompare(b, 'pl'));
  for (const town of towns) {
    const dm = byTown.get(town);
    const count = [...dm.values()].reduce((x, a) => x + a.length, 0);
    const ul = el('ul', { class: 'card list' });
    const ds = [...dm.keys()].sort((a, b) => (a === NO_DISTRICT) - (b === NO_DISTRICT) || a.localeCompare(b, 'pl'));
    const showHeads = !(ds.length === 1 && ds[0] === NO_DISTRICT);
    for (const d of ds) {
      const items = dm.get(d).sort((a, b) => a.street.localeCompare(b.street, 'pl'));
      const dpd = districtProgress(state.agg[town], state.townMeta[town])?.find((x) => x.name === d);
      if (showHeads) ul.append(dpd ? districtHead(dpd) : groupHead(d, items.length, items.reduce((x, r) => x + r.m, 0)));
      for (const r of items) {
        ul.append(el('li', {}, el('span', { class: 'd' }), el('span', { class: 'n' }, r.street),
          el('span', { class: 'm' }, `${r.n}× · ${fmtDate(r.last)}`)));
      }
    }
    const head = el('button', { class: 'town-link', type: 'button', onclick: () => openTown(town) },
      el('span', {}, town), el('span', { class: 'm' }, `${count} ${plural(count, 'ulica', 'ulice', 'ulic')} ›`));
    box.append(el('section', { class: 'street-town' }, head, ul));
  }
}

function exportCsv() {
  const rows = allStreetRows().sort((a, b) =>
    a.town.localeCompare(b.town, 'pl') || a.district.localeCompare(b.district, 'pl') || a.street.localeCompare(b.street, 'pl'));
  const q = (v) => '"' + String(v).replace(/"/g, '""') + '"';
  const lines = [['Miejscowość', 'Osiedle', 'Ulica', 'Liczba przejazdów', 'Km', 'Ostatni przejazd'].map(q).join(';')];
  for (const r of rows) {
    lines.push([r.town, r.district === NO_DISTRICT ? '' : r.district, r.street, r.n,
      (r.m / 1000).toFixed(2).replace('.', ','), new Date(r.last).toISOString().slice(0, 10)].map(q).join(';'));
  }
  // BOM, żeby Excel poprawnie pokazał polskie znaki
  const blob = new Blob(['\ufeff' + lines.join('\r\n')], { type: 'text/csv;charset=utf-8' });
  const a = el('a', { href: URL.createObjectURL(blob), download: `moje-drogi-ulice-${new Date().toISOString().slice(0, 10)}.csv` });
  document.body.append(a);
  a.click();
  a.remove();
  setTimeout(() => URL.revokeObjectURL(a.href), 5000);
}

function showView(id) {
  document.querySelectorAll('.view').forEach((v) => v.classList.toggle('active', v.id === id));
  document.querySelectorAll('.tabbar button').forEach((b) => b.classList.toggle('on', b.dataset.view === id));
  if (id === 'view-map') setTimeout(() => map.invalidateSize(), 0);
}

/* ---------------- Import / eksport ---------------- */
async function importGpx(files) {
  let added = 0;
  for (const f of files) {
    const doc = new DOMParser().parseFromString(await f.text(), 'application/xml');
    const raw = [...doc.querySelectorAll('trkpt, rtept')].map((e) => [
      +e.getAttribute('lat'), +e.getAttribute('lon'),
      Date.parse(e.querySelector('time')?.textContent || '') || 0,
    ]).filter((p) => Number.isFinite(p[0]) && Number.isFinite(p[1]));
    const pts = [];
    for (const p of raw) if (!pts.length || dist(pts[pts.length - 1], p) >= MIN_STEP_M) pts.push(p);
    if (pts.length < 2) continue;
    const start = pts[0][2] || f.lastModified;
    const end = pts[pts.length - 1][2] || null;
    const t = { id: 'g' + start + '-' + Math.random().toString(36).slice(2, 7), start, end, points: pts, recording: false, processed: false, source: 'gpx', km: trackLen(pts) };
    await dbPut('trips', t);
    state.trips.push(t);
    added++;
  }
  drawTrips();
  setStatus(added ? `Zaimportowano ${added} ${plural(added, 'trasę', 'trasy', 'tras')}. Rozpoznaję ulice…` : 'W pliku nie znalazłem trasy.');
  showView('view-map');
  processPending();
}

async function exportBackup() {
  const data = { app: 'moje-drogi', v: 1, saved: new Date().toISOString(), trips: state.trips, towns: Object.values(state.townMeta) };
  const blob = new Blob([JSON.stringify(data)], { type: 'application/json' });
  const a = el('a', { href: URL.createObjectURL(blob), download: `moje-drogi-${new Date().toISOString().slice(0, 10)}.json` });
  document.body.append(a);
  a.click();
  a.remove();
  setTimeout(() => URL.revokeObjectURL(a.href), 5000);
}

async function importBackup(file) {
  try {
    const data = JSON.parse(await file.text());
    if (data.app !== 'moje-drogi') throw new Error('zły plik');
    const have = new Set(state.trips.map((t) => t.id));
    let added = 0;
    for (const t of data.trips || []) if (!have.has(t.id)) { t.recording = false; await dbPut('trips', t); state.trips.push(t); added++; }
    for (const m of data.towns || []) { await dbPut('towns', m); state.townMeta[m.name] = m; }
    rebuild();
    setStatus(`Wczytano kopię: ${added} nowych tras.`);
    processPending();
  } catch {
    setStatus('To nie jest kopia zapasowa Moich Dróg.');
  }
}

/* ---------------- Start ---------------- */
async function init() {
  initMap();
  try { idb = await openDb(); }
  catch { setStatus('Przeglądarka nie pozwala zapisywać danych (tryb prywatny?).'); return; }

  state.trips = await dbAll('trips');
  for (const m of await dbAll('towns')) state.townMeta[m.name] = m;
  // trasa przerwana zamknięciem aplikacji: zapisz ją jako zakończoną
  for (const t of state.trips.filter((x) => x.recording)) {
    t.recording = false;
    t.end = t.points.length ? t.points[t.points.length - 1][2] : t.start;
    t.km = trackLen(t.points);
    if (t.points.length < 3) { await dbDel('trips', t.id); } else await dbPut('trips', t);
  }
  state.trips = state.trips.filter((t) => t.points.length >= 3 || t.source === 'gpx');
  // trasy rozpoznane starszą wersją przeliczamy jeszcze raz, żeby dostały podział na osiedla
  for (const t of state.trips) if (t.processed && t.v !== TRIP_V) t.processed = false;
  rebuild();
  const all = state.trips.flatMap((t) => t.points.map((p) => [p[0], p[1]]));
  if (all.length) map.fitBounds(L.latLngBounds(all), { padding: [30, 30], maxZoom: 15 });
  setFollow(false);
  processPending();

  // pokaż pozycję bez nagrywania (jednorazowo)
  if (navigator.geolocation && window.isSecureContext) {
    navigator.geolocation.getCurrentPosition((p) => showPos(p.coords.latitude, p.coords.longitude, p.coords.accuracy), () => {}, { enableHighAccuracy: true, timeout: 15000 });
  }
}

$('#btn-rec').addEventListener('click', () => (state.rec ? stopRec() : startRec()));
$('#btn-layer').addEventListener('click', () => {
  state.showVisited = !state.showVisited;
  $('#btn-layer').classList.toggle('on', state.showVisited);
  $('#btn-layer').setAttribute('aria-pressed', String(state.showVisited));
  if (state.showVisited) visitedLayer.addTo(map); else visitedLayer.remove();
});
$('#btn-follow').addEventListener('click', () => {
  setFollow(!state.follow);
  if (state.follow && posMarker) map.setView(posMarker.getLatLng(), Math.max(map.getZoom(), 16));
});
$('#sheet-details').addEventListener('click', () => {
  const T = sheetTown();
  if (T) openTown(T.name);
  else if (state.focus) setStatus(`W miejscowości ${state.focus.name} jeszcze nie jeździłeś.`);
  else showView('view-town');
});

/* ---------------- Wyszukiwanie miejscowości ---------------- */
// Własne miejscowości podpowiadamy od razu; pozostałe szukamy w Nominatim dopiero po Enter
// (zasady Nominatim nie pozwalają na zapytania przy każdym naciśnięciu klawisza).
let focusMarker = null, searchCtl = null;
const qInput = $('#q'), resultsEl = $('#results');

function closeResults() { resultsEl.hidden = true; resultsEl.replaceChildren(); }

function resultButton(name, sub, tag, onPick) {
  const b = el('button', { type: 'button' },
    el('span', {}, el('span', { class: 'r-name' }, name), sub ? el('span', { class: 'r-sub' }, sub) : null),
    tag ? el('span', { class: 'r-tag' }, tag) : null);
  b.addEventListener('click', onPick);
  return el('li', {}, b);
}

function localMatches(q) {
  const f = norm(q);
  if (!f) return [];
  return Object.values(state.agg)
    .filter((T) => T.name !== NO_TOWN && norm(T.name).includes(f))
    .sort((a, b) => (norm(a.name).startsWith(f) ? 0 : 1) - (norm(b.name).startsWith(f) ? 0 : 1) || b.last - a.last)
    .slice(0, 6);
}

function renderResults(q, remote, info) {
  resultsEl.replaceChildren();
  const local = localMatches(q);
  const localNames = new Set(local.map((T) => T.name));
  for (const T of local) {
    const n = namedCount(T);
    resultsEl.append(resultButton(T.name, `${n} ${plural(n, 'ulica', 'ulice', 'ulic')} · ${fmtKm(T.m)}`, 'Twoja', () => pickLocal(T)));
  }
  for (const r of remote || []) {
    if (localNames.has(r.name)) continue;
    resultsEl.append(resultButton(r.name, r.sub, null, () => pickRemote(r)));
  }
  if (info) resultsEl.append(el('li', { class: 'r-info' }, info));
  else if (!local.length && !remote) resultsEl.append(el('li', { class: 'r-info' }, 'Naciśnij Enter, żeby wyszukać w promieniu 120 km.'));
  resultsEl.hidden = !resultsEl.children.length;
}

async function searchRemote(q) {
  searchCtl?.abort();
  searchCtl = new AbortController();
  renderResults(q, null, 'Szukam…');
  const dLat = RADIUS_KM / 111, dLon = RADIUS_KM / (111 * Math.cos(KRAKOW[0] * Math.PI / 180));
  const viewbox = [KRAKOW[1] - dLon, KRAKOW[0] + dLat, KRAKOW[1] + dLon, KRAKOW[0] - dLat].map((v) => v.toFixed(4)).join(',');
  const url = `https://nominatim.openstreetmap.org/search?format=jsonv2&addressdetails=1&limit=8&countrycodes=pl&featureType=settlement&accept-language=pl&bounded=1&viewbox=${viewbox}&q=${encodeURIComponent(q)}`;
  try {
    const r = await fetch(url, { signal: searchCtl.signal });
    if (!r.ok) throw new Error('nominatim ' + r.status);
    const list = (await r.json())
      .map((x) => {
        const a = x.address || {};
        const name = a.city || a.town || a.village || a.hamlet || x.name;
        const lat = +x.lat, lon = +x.lon;
        const km = Math.round(dist(KRAKOW, [lat, lon]) / 1000);
        return { name, lat, lon, bbox: x.boundingbox?.map(Number), sub: [a.municipality, a.county, `${km} km od Krakowa`].filter(Boolean).join(' · ') };
      })
      .filter((x) => x.name && !/^(gmina|powiat|województwo)\s/i.test(x.name) && dist(KRAKOW, [x.lat, x.lon]) <= RADIUS_KM * 1000);
    const seen = new Set();
    const uniq = list.filter((x) => { const k = x.name + x.sub; if (seen.has(k)) return false; seen.add(k); return true; });
    renderResults(q, uniq, uniq.length || localMatches(q).length ? null : 'Nie znalazłem takiej miejscowości w promieniu 120 km.');
  } catch (e) {
    if (e.name === 'AbortError') return;
    renderResults(q, [], 'Wyszukiwanie nie działa bez internetu.');
  }
}

function focusOn(name, lat, lon, bbox) {
  state.focus = { name, lat, lon };
  qInput.value = name;
  $('#q-clear').hidden = false;
  closeResults();
  qInput.blur();
  setFollow(false);
  if (!focusMarker) {
    focusMarker = L.circleMarker([lat, lon], { radius: 9, color: '#fff', weight: 3, fillColor: '#1D4ED8', fillOpacity: 1 }).addTo(map);
  } else focusMarker.setLatLng([lat, lon]);
  focusMarker.bindTooltip(name, { permanent: true, direction: 'top', offset: [0, -10] }).openTooltip();
  if (bbox && bbox.length === 4) map.fitBounds([[bbox[0], bbox[2]], [bbox[1], bbox[3]]], { padding: [30, 30], maxZoom: 15 });
  else map.setView([lat, lon], 14);
  renderSheet();
  if (!state.agg[name]) setStatus(`W miejscowości ${name} jeszcze nie jeździłeś.`);
  else setStatus('');
}

function pickLocal(T) {
  const pts = T.trips.flatMap((t) => t.points.map((p) => [p[0], p[1]]));
  const c = T.pt || pts[0];
  showView('view-map');
  focusOn(T.name, c[0], c[1], null);
  if (pts.length) map.fitBounds(L.latLngBounds(pts), { padding: [30, 30], maxZoom: 15 });
}
function pickRemote(r) { focusOn(r.name, r.lat, r.lon, r.bbox); }

function clearSearch() {
  searchCtl?.abort();
  state.focus = null;
  qInput.value = '';
  $('#q-clear').hidden = true;
  closeResults();
  if (focusMarker) { focusMarker.remove(); focusMarker = null; }
  setStatus('');
  renderSheet();
}

qInput.addEventListener('input', () => {
  $('#q-clear').hidden = !qInput.value;
  if (!qInput.value.trim()) { closeResults(); return; }
  renderResults(qInput.value, null, null);
});
qInput.addEventListener('focus', () => { if (qInput.value.trim() && !state.focus) renderResults(qInput.value, null, null); });
$('#search-form').addEventListener('submit', (e) => {
  e.preventDefault();
  const q = qInput.value.trim();
  if (q.length >= 2) searchRemote(q);
});
$('#q-clear').addEventListener('click', () => { clearSearch(); qInput.focus(); });
qInput.addEventListener('keydown', (e) => { if (e.key === 'Escape') closeResults(); });
document.addEventListener('pointerdown', (e) => { if (!e.target.closest('.search-wrap')) closeResults(); });
$('#town-filter').addEventListener('input', (e) => { state.filter = e.target.value; renderTowns(); });
$('#street-filter').addEventListener('input', (e) => { state.streetFilter = e.target.value; renderStreets(); });
$('#btn-csv').addEventListener('click', exportCsv);
document.querySelectorAll('.tabbar button').forEach((b) => b.addEventListener('click', () => showView(b.dataset.view)));
document.querySelectorAll('.pill').forEach((b) => b.addEventListener('click', () => {
  state.sort = b.dataset.sort;
  document.querySelectorAll('.pill').forEach((x) => x.classList.toggle('on', x === b));
  renderTowns();
}));
$('#btn-back').addEventListener('click', () => showView('view-towns'));
$('#tab-streets').addEventListener('click', () => { state.detailTab = 'streets'; renderTown(); });
$('#tab-trips').addEventListener('click', () => { state.detailTab = 'trips'; renderTown(); });
$('#btn-show').addEventListener('click', () => fitTown(state.selected));
$('#btn-count').addEventListener('click', async () => {
  const btn = $('#btn-count');
  btn.disabled = true;
  btn.textContent = 'Liczę ulice…';
  try { await countStreets(state.selected); renderAll(); }
  catch (e) { console.warn(e); $('#d-area').textContent = 'Nie udało się pobrać listy ulic. Sprawdź internet i spróbuj za chwilę.'; btn.disabled = false; btn.textContent = 'Policz wszystkie ulice'; }
});
$('#in-gpx').addEventListener('change', (e) => { if (e.target.files.length) importGpx([...e.target.files]); e.target.value = ''; });
$('#in-backup').addEventListener('change', (e) => { if (e.target.files[0]) importBackup(e.target.files[0]); e.target.value = ''; });
$('#btn-export').addEventListener('click', exportBackup);
window.addEventListener('beforeunload', () => { if (state.rec) dbPut('trips', state.rec); });

if ('serviceWorker' in navigator && window.isSecureContext) navigator.serviceWorker.register('sw.js').catch(() => {});
init();
