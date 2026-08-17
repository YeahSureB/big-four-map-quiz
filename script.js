// Pro Sports Stadium Quiz — Game Script
// Adapted from US Politics Geography Quiz script.js

let map;
let currentTarget;
let allFranchises = [];
let currentMode = '';
let streak = 0;
let highScore = 0;
let lastGuessSuccessful = false;
let userMarker = null;
let actualMarker = null;
let connectionLine = null;
let highlightedPolygon = null;
let hasGuessed = false;
let statesLayer = null;
let statesData = null;

// --- Timer and Run Variables ---
let runTimer = null;
let runStartTime = 0;
let isRunActive = false;
let finalRunTime = 0;

const CANADIAN_PROVINCES = new Set([
    'Alberta',
    'British Columbia',
    'Manitoba',
    'Ontario',
    'Quebec'
]);

// How close a click needs to be to the actual stadium to count as correct.
// Starting small per playtesting plan — tweak this single constant to retune.
const STADIUM_HIT_RADIUS_MILES = 5;

// --- Bayesian Knowledge Tracing (BKT) ---
// g = guess rate: probability of landing within the hit radius by chance.
//     Lower than the old state-polygon guess rate — a 5-mile bullseye
//     anywhere on the map is much harder to hit by luck than a whole state.
// s = slip rate: probability of missing the radius despite actually knowing
//     the stadium's location (fat-fingering the click, map lag, etc).
const BKT_G = 0.02;
const BKT_S = 0.10;
const BKT_L_INIT = 0.50;
const BKT_MASTERY_THRESHOLD = 0.95;
const COOLDOWN_ROUNDS = 8;           // an item can't reappear within this many rounds
const MASTERED_REVIEW_CHANCE = 0.10; // 10% of rounds resurface a mastered item, for retention
let knowledgeState = {}; // key: "Team|State" -> L (probability of true knowledge)
let recentlyShown = []; // queue of the last COOLDOWN_ROUNDS target keys served

function getTargetKey(target) {
    return `${target.team}|${target.state}`;
}

function saveKnowledgeState() {
    // Mastery is transient per-run — intentionally not persisted to localStorage.
}

function loadKnowledgeState(mode, targets) {
    let restored = {};
    targets.forEach(t => {
        restored[getTargetKey(t)] = BKT_L_INIT;
    });
    return restored;
}

// P(C) = L(1 - s) + (1 - L)g — exposed for potential future use (e.g. UI display)
function probabilityCorrect(L) {
    return (L * (1 - BKT_S)) + ((1 - L) * BKT_G);
}

// Bayesian update of L given an observed answer
function updateKnowledge(target, wasCorrect) {
    const key = getTargetKey(target);
    const L = knowledgeState[key] ?? BKT_L_INIT;
    let L_new;
    if (wasCorrect) {
        L_new = 1.0; // Instantly master on a direct hit
    } else {
        L_new = (L * BKT_S) / ((L * BKT_S) + ((1 - L) * (1 - BKT_G)));
    }
    knowledgeState[key] = L_new;
    return L_new;
}

// Turn a team name into an image-filename slug: "Boston Celtics" -> "boston-celtics"
function slugify(str) {
    return str
        .toLowerCase()
        .trim()
        .replace(/[^a-z0-9\s-]/g, '')
        .replace(/\s+/g, '-');
}

// Returns the pool of franchises for a given mode — filtered by league,
// or the full pool for the "all" mode (config.league === null).
function getModeData(mode) {
    const config = MODE_CONFIG[mode];
    if (!config) {
        console.error(`Unknown mode: ${mode}`);
        return [];
    }
    if (config.league === null) return allFranchises;
    return allFranchises.filter(f => f.league === config.league);
}

// Mode configuration — mirrors original MODE_CONFIG structure
const MODE_CONFIG = {
    'nfl': { league: 'NFL', label: 'NFL', nextBtnText: 'Next Stadium' },
    'nba': { league: 'NBA', label: 'NBA', nextBtnText: 'Next Arena' },
    'mlb': { league: 'MLB', label: 'MLB', nextBtnText: 'Next Ballpark' },
    'nhl': { league: 'NHL', label: 'NHL', nextBtnText: 'Next Arena' },
    'all': { league: null, label: 'All Leagues', nextBtnText: 'Next Venue' }
};

// DOM elements
const resultTeam = document.getElementById('result-team');
const resultVenue = document.getElementById('result-venue');
const resultCityState = document.getElementById('result-city-state');
const resultDivision = document.getElementById('result-division');
const resultFact = document.getElementById('result-fact');
const resultWikiLink = document.getElementById('result-wiki-link');
const nextBtn = document.getElementById('btn-next');
const modeSelection = document.getElementById('mode-selection');
const targetTeamName = document.getElementById('target-team-name');
const resultPanel = document.getElementById('result-panel');
const resultMessage = document.getElementById('result-message');
const resultDistance = document.getElementById('result-distance');
const changeModeBtn = document.getElementById('change-mode-btn');
const streakNumberEl = document.getElementById('streak-number');
const highScoreEl = document.getElementById('high-score');
const masteryPercentEl = document.getElementById('mastery-percent');
const masteryProgressFill = document.getElementById('mastery-progress-fill');
const resultConfidence = document.getElementById('result-confidence');

// --- Timer & Leaderboard DOM Elements ---
const timerDisplay = document.getElementById('timer-display');
const postGameScreen = document.getElementById('post-game-screen');
const finalTimeDisplay = document.getElementById('final-time-display');
const leaderboardBody = document.getElementById('leaderboard-body');
const initialsEntry = document.getElementById('initials-entry');
const playerInitials = document.getElementById('player-initials');
const submitScoreBtn = document.getElementById('submit-score-btn');
const playAgainBtn = document.getElementById('play-again-btn');

const MAP_CENTER = [39.5, -98.35];
const MAP_ZOOM = 4;

// Initialize the game
async function init() {
    // Load all data before initializing the map
    await loadFranchiseData();
    await loadBordersData();

    // Initialize map so it shows under the mode selection overlay
    initMap();

    // Draw state/province outlines — always visible; used for the
    // consolation "right state/province" check on each guess.
    drawStatesLayer();

    // Load saved preferences from localStorage
    loadPreferences();

    // Set up event listeners — one per mode button, keyed off data-league
    document.querySelectorAll('.mode-btn[data-league]').forEach(btn => {
        const mode = btn.id.replace('-btn', '');
        btn.addEventListener('click', () => startGame(mode));
    });
    nextBtn.addEventListener('click', nextRound);
    changeModeBtn.addEventListener('click', changeMode);

    // --- Leaderboard & Run Event Listeners ---
    playAgainBtn.addEventListener('click', changeMode); // changeMode handles returning to title
    submitScoreBtn.addEventListener('click', submitLeaderboardScore);
    window.addEventListener('beforeunload', handleBeforeUnload);

    // Input sanitization for initials field
    playerInitials.addEventListener('input', (e) => {
        e.target.value = e.target.value.toUpperCase();
    });
}

// Load saved preferences from localStorage
function loadPreferences() {
    const savedHighScore = localStorage.getItem('sportsHighScore');
    if (savedHighScore) {
        highScore = parseInt(savedHighScore);
        highScoreEl.textContent = highScore;
    }

    const lastMode = localStorage.getItem('sportsLastMode');
    if (lastMode) {
        console.log(`Last played mode: ${lastMode}`);
    }
}

// Load franchise JSON data and normalize field names
async function loadFranchiseData() {
    try {
        const response = await fetch('franchises.json');
        const rawData = await response.json();

        allFranchises = rawData.map(f => ({
            league: f.league,
            conference: f.conference,
            division: f.division,
            team: f.team,
            city: f.city,
            venue: f.venue,
            capacity: f.capacity,
            lat: f.lat,
            lng: f.lon,           // normalize "lon" -> "lng" to match Leaflet's LatLng convention
            funFact: f['fun-fact'],
            nickname: f.nickname,
            state: f['state-province']
        }));

        console.log(`Loaded ${allFranchises.length} franchises from franchises.json`);
    } catch (error) {
        console.error('Error loading franchise data:', error);
        alert('Error loading franchise data. Please ensure franchises.json is in the same directory.');
    }
}

// Load state/province boundary GeoJSON — used only for the consolation check.
// Expects a "state-province" property on each feature (e.g. {"state-province": "Delaware"}),
// matching the "state-province" field in franchises.json.
async function loadBordersData() {
    try {
        const response = await fetch('borders.geojson');
        const geoJsonData = await response.json();
        statesData = geoJsonData;
        console.log(`Loaded ${statesData.features.length} region features from borders.geojson`);

        // Build a lookup map from state/province name to feature for fast joining
        const stateFeatureMap = {};
        statesData.features.forEach(feature => {
            stateFeatureMap[feature.properties['state-province']] = feature;
        });

        joinGeometryToData(allFranchises, stateFeatureMap);

    } catch (error) {
        console.error('Error loading border boundary data:', error);
        alert('Error loading borders.geojson. Please ensure it is in the same directory.');
    }
}

// Attach polygon geometry from a GeoJSON feature lookup to each franchise,
// keyed by franchise.state. Franchise lat/lng comes straight from
// franchises.json, so no centroid computation is needed here (unlike the
// politics version, where the "target" WAS the state centroid).
function joinGeometryToData(franchises, stateFeatureMap) {
    const missing = [];
    franchises.forEach(franchise => {
        const feature = stateFeatureMap[franchise.state];
        if (feature) {
            franchise.geometry = feature.geometry;
        } else {
            missing.push(`${franchise.team} (${franchise.state})`);
        }
    });
    if (missing.length > 0) {
        console.warn(
            `No matching border feature for ${missing.length} franchise${missing.length === 1 ? '' : 's'} — ` +
            `the consolation "right state/province" check will be skipped for these. ` +
            `Check state-province spelling against borders.geojson:`,
            missing
        );
    }
}

// Initialize Leaflet map
function initMap() {
    map = L.map('map', {
        center: MAP_CENTER,
        zoom: MAP_ZOOM,
        minZoom: 3,
        maxZoom: 10,
        zoomControl: false
    });

    L.control.zoom({ position: 'topright' }).addTo(map);

    L.tileLayer('https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}', {
        attribution: 'Tiles &copy; Esri &mdash; Source: Esri, i-cubed, USDA, USGS, AEX, GeoEye, Getmapping, Aerogrid, IGN, IGP, UPR-EGP, and the GIS User Community',
        maxZoom: 18
    }).addTo(map);

    map.on('click', handleMapClick);
}

// Draw the state/province outline layer — reference layer only; it plays no
// role in scoring beyond the consolation message.
function drawStatesLayer() {
    if (!statesData || statesLayer) return;
    statesLayer = L.geoJSON(statesData, {
        style: {
            color: '#ffffff',
            weight: 1.5,
            opacity: 0.6,
            fillOpacity: 0
        },
        interactive: false
    }).addTo(map);
    console.log('Region outlines drawn');
}

// Start game with selected mode
function startGame(mode) {
    currentMode = mode;
    streak = 0;

    const modeBestStreak = parseInt(localStorage.getItem(`best-streak-${mode}`)) || 0;
    highScore = modeBestStreak;

    updateStreakDisplay();

    const config = MODE_CONFIG[mode];
    if (!config) {
        console.error(`Unknown mode: ${mode}`);
        return;
    }

    localStorage.setItem('sportsLastMode', mode);
    document.title = `${config.label} Stadium Quiz`;

    const sourceData = getModeData(mode);

    knowledgeState = loadKnowledgeState(mode, sourceData);
    recentlyShown = [];
    updateMasteryUI();

    console.log(`Starting ${mode} mode with ${sourceData.length} targets`);

    modeSelection.classList.add('hidden');
    postGameScreen.classList.add('hidden');

    // --- Timer Start Logic ---
    isRunActive = true;
    runStartTime = Date.now();
    if (runTimer) clearInterval(runTimer);
    runTimer = setInterval(updateTimerTick, 30);

    startRound();
}

// Live updating the active timer
function updateTimerTick() {
    if (!isRunActive) return;
    const elapsed = Date.now() - runStartTime;
    timerDisplay.textContent = formatTime(elapsed);
}

// Format MS into MM:SS.mmm
function formatTime(ms) {
    const totalSeconds = Math.floor(ms / 1000);
    const m = Math.floor(totalSeconds / 60).toString().padStart(2, '0');
    const s = (totalSeconds % 60).toString().padStart(2, '0');
    const mss = (ms % 1000).toString().padStart(3, '0');
    return `${m}:${s}.${mss}`;
}

// Start a new round — adaptive selection
function startRound() {
    hasGuessed = false;
    clearMarkers();
    resultPanel.classList.add('hidden');
    resultConfidence.textContent = '';

    currentTarget = selectNextTarget();

    targetTeamName.textContent = currentTarget.nickname;

    console.log(`Streak ${streak}: Find ${currentTarget.team} → ${currentTarget.venue}`);
}

// Weighted-random adaptive selection: more uncertain items are MORE LIKELY
// to appear, not guaranteed to appear. A short cooldown keeps any item from
// repeating too soon, and mastered items occasionally resurface for
// spaced-repetition-style retention.
function selectNextTarget() {
    const allTargets = getModeData(currentMode);

    const isOnCooldown = t => recentlyShown.includes(getTargetKey(t));

    const unmastered = allTargets.filter(
        t => (knowledgeState[getTargetKey(t)] ?? BKT_L_INIT) < BKT_MASTERY_THRESHOLD
    );
    const mastered = allTargets.filter(
        t => (knowledgeState[getTargetKey(t)] ?? BKT_L_INIT) >= BKT_MASTERY_THRESHOLD
    );

    if (mastered.length > 0 && Math.random() < MASTERED_REVIEW_CHANCE) {
        const eligible = mastered.filter(t => !isOnCooldown(t));
        if (eligible.length > 0) {
            return pickAndRemember(eligible[Math.floor(Math.random() * eligible.length)]);
        }
    }

    let pool = unmastered.filter(t => !isOnCooldown(t));
    if (pool.length === 0) pool = unmastered;
    if (pool.length === 0) pool = allTargets;

    const weights = pool.map(t => {
        const L = knowledgeState[getTargetKey(t)] ?? BKT_L_INIT;
        return Math.max(0.05, 1 - Math.abs(L - 0.5) * 2);
    });

    const totalWeight = weights.reduce((a, b) => a + b, 0);
    let roll = Math.random() * totalWeight;
    let chosen = pool[pool.length - 1];
    for (let i = 0; i < pool.length; i++) {
        roll -= weights[i];
        if (roll <= 0) {
            chosen = pool[i];
            break;
        }
    }

    return pickAndRemember(chosen);
}

function pickAndRemember(target) {
    recentlyShown.push(getTargetKey(target));
    if (recentlyShown.length > COOLDOWN_ROUNDS) recentlyShown.shift();
    return target;
}

// Update the mastery stat + progress bar
function updateMasteryUI() {
    if (!currentMode) return;
    const sourceData = getModeData(currentMode);
    const total = sourceData.length;
    const masteredCount = sourceData.filter(
        t => (knowledgeState[getTargetKey(t)] ?? BKT_L_INIT) >= BKT_MASTERY_THRESHOLD
    ).length;

    const pct = total > 0 ? Math.round((masteredCount / total) * 100) : 0;
    masteryPercentEl.textContent = `${pct}%`;
    masteryProgressFill.style.width = `${pct}%`;

    if (pct >= 100 && isRunActive) {
        endRun();
    }
}

// Update streak display
function updateStreakDisplay() {
    streakNumberEl.textContent = streak;

    if (streak > highScore) {
        highScore = streak;
        highScoreEl.textContent = highScore;

        if (currentMode) {
            localStorage.setItem(`best-streak-${currentMode}`, highScore);
        }
        console.log(`New high score: ${highScore}!`);
    }
}

// Handle map click
function handleMapClick(e) {
    if (hasGuessed || !isRunActive) return;

    hasGuessed = true;
    const userLatLng = e.latlng;
    const actualLatLng = L.latLng(currentTarget.lat, currentTarget.lng);

    // Place marker where user clicked (red)
    userMarker = L.circleMarker(userLatLng, {
        color: '#c0392b',
        fillColor: '#e74c3c',
        fillOpacity: 0.7,
        radius: 8,
        weight: 2
    }).addTo(map);

    // Place marker at the actual stadium (green)
    actualMarker = L.circleMarker(actualLatLng, {
        color: '#1e8449',
        fillColor: '#27ae60',
        fillOpacity: 0.7,
        radius: 8,
        weight: 2
    }).addTo(map);

    // Highlight the franchise's home state/province — consolation only,
    // drawn whenever we have geometry, regardless of hit/miss.
    if (currentTarget.geometry) {
        highlightedPolygon = L.geoJSON(currentTarget.geometry, {
            style: {
                color: '#27ae60',
                weight: 3,
                opacity: 0.8,
                fillColor: '#27ae60',
                fillOpacity: 0.2
            }
        }).addTo(map);
    }

    // Dashed line between click and the actual stadium
    connectionLine = L.polyline([userLatLng, actualLatLng], {
        color: '#3498db',
        weight: 2,
        dashArray: '10, 10',
        opacity: 0.7
    }).addTo(map);

    // Distance in miles
    const distanceMeters = userLatLng.distanceTo(actualLatLng);
    const distanceMiles = (distanceMeters * 0.000621371).toFixed(2);

    displayResult(distanceMiles, userLatLng);
}

function displayResult(distance, userLatLng) {
    let message = '';
    const config = MODE_CONFIG[currentMode];
    const distanceNum = parseFloat(distance);

    // TRUE correctness: strict proximity to the stadium point.
    lastGuessSuccessful = distanceNum <= STADIUM_HIT_RADIUS_MILES;

    // Consolation-only signal: did the click land in the franchise's home
    // state/province? This NEVER affects streak, BKT knowledge, or mastery —
    // it's purely flavor text so a near-miss still feels like progress.
    const clickedRightRegion = currentTarget.geometry
        ? isPointInPolygon([userLatLng.lng, userLatLng.lat], currentTarget.geometry)
        : false;

    // Knowledge tracking uses ONLY the strict hit/miss outcome.
    const updatedL = updateKnowledge(currentTarget, lastGuessSuccessful);
    saveKnowledgeState();
    resultConfidence.textContent = `${Math.round(updatedL * 100)}%`;
    updateMasteryUI();

    // 1. Determine the message.
    if (lastGuessSuccessful) {
        message = '🎯 Bullseye! You found the stadium!';
    } else if (clickedRightRegion) {
        const regionType = CANADIAN_PROVINCES.has(currentTarget.state) ? 'province' : 'state';
        message = `📍 Right ${regionType} — so close to the stadium!`;
    } else if (distanceNum < 100) {
        message = '👍 Great job! Pretty close!';
    } else if (distanceNum < 300) {
        message = '✓ Not bad! Getting warmer!';
    } else if (distanceNum < 600) {
        message = '🔍 Keep practicing!';
    } else {
        message = '🗺️ Try again next time!';
    }

    resultMessage.textContent = message;
    resultDistance.textContent = lastGuessSuccessful
        ? `You were ${distance} miles from ${currentTarget.venue} — right on target!`
        : `You were ${distance} miles from ${currentTarget.venue}.`;

    // 2. Populate the sidebar fields
    resultTeam.textContent = currentTarget.team;
    resultVenue.textContent = currentTarget.venue;
    resultCityState.textContent = `${currentTarget.city}, ${currentTarget.state}`;
    resultDivision.textContent = `${currentTarget.conference} — ${currentTarget.division}`;
    resultFact.textContent = currentTarget.funFact ? currentTarget.funFact : '';

    // 3. Team logo — images/<slugified-team-name>.webp, e.g. images/boston-celtics.webp
    const logoContainer = document.getElementById('logo-container');
    const teamLogo = document.getElementById('team-logo');
    const imagePath = `images/${slugify(currentTarget.team)}.webp`;

    teamLogo.onerror = () => {
        logoContainer.style.display = 'none';
    };
    teamLogo.onload = () => {
        logoContainer.style.display = 'flex';
    };

    teamLogo.alt = currentTarget.team;
    teamLogo.src = imagePath;
    logoContainer.style.display = 'flex';

    // 4. Next-button label + Wikipedia link
    nextBtn.textContent = config.nextBtnText;
    resultWikiLink.href = `https://en.wikipedia.org/wiki/${encodeURIComponent(currentTarget.team.replace(/ /g, '_'))}`;

    // 5. Show the panel
    resultPanel.classList.remove('hidden');
}

// Check if a point is inside a polygon (ray casting algorithm)
function isPointInPolygon(point, geometry) {
    if (geometry.type === 'MultiPolygon') {
        return geometry.coordinates.some(polygon =>
            checkPointInPolygonCoordinates(point, polygon)
        );
    } else if (geometry.type === 'Polygon') {
        return checkPointInPolygonCoordinates(point, geometry.coordinates);
    }
    return false;
}

function checkPointInPolygonCoordinates(point, coordinates) {
    if (!isInRing(point, coordinates[0])) return false;
    for (let r = 1; r < coordinates.length; r++) {
        if (isInRing(point, coordinates[r])) return false;
    }
    return true;
}

function isInRing(point, ring) {
    const [x, y] = point;
    let inside = false;

    for (let i = 0, j = ring.length - 1; i < ring.length; j = i++) {
        const [xi, yi] = ring[i];
        const [xj, yj] = ring[j];

        const intersect = ((yi > y) !== (yj > y)) &&
            (x < (xj - xi) * (y - yi) / (yj - yi) + xi);
        if (intersect) inside = !inside;
    }

    return inside;
}

// Clear markers and lines from map
function clearMarkers() {
    if (userMarker) {
        map.removeLayer(userMarker);
        userMarker = null;
    }
    if (actualMarker) {
        map.removeLayer(actualMarker);
        actualMarker = null;
    }
    if (connectionLine) {
        map.removeLayer(connectionLine);
        connectionLine = null;
    }
    if (highlightedPolygon) {
        map.removeLayer(highlightedPolygon);
        highlightedPolygon = null;
    }
}

// Next round
function nextRound() {
    if (lastGuessSuccessful) {
        streak++;
        updateStreakDisplay();
    } else {
        streak = 0;
        updateStreakDisplay();
    }

    map.setView(MAP_CENTER, MAP_ZOOM, { animate: true });

    if (isRunActive) {
        startRound();
    }
}

// Change game mode
function changeMode() {
    if (isRunActive) {
        const confirmQuit = confirm("Are you sure you want to quit this run? All progress will be lost.");
        if (!confirmQuit) return;
    }

    isRunActive = false;
    clearInterval(runTimer);
    timerDisplay.textContent = "00:00.000";
    masteryPercentEl.textContent = "0%";
    masteryProgressFill.style.width = "0%";
    resultPanel.classList.add('hidden');
    postGameScreen.classList.add('hidden');
    document.title = "Pro Sports Stadium Quiz";

    clearMarkers();
    map.setView(MAP_CENTER, MAP_ZOOM);
    modeSelection.classList.remove('hidden');
}

function handleBeforeUnload(e) {
    if (isRunActive) {
        e.preventDefault();
        e.returnValue = '';
    }
}

// --- End Run & Leaderboards ---
function endRun() {
    isRunActive = false;
    clearInterval(runTimer);
    finalRunTime = Date.now() - runStartTime;
    timerDisplay.textContent = formatTime(finalRunTime);

    setTimeout(() => {
        showPostGameScreen();
    }, 500);
}

function showPostGameScreen() {
    resultPanel.classList.add('hidden');
    clearMarkers();
    finalTimeDisplay.textContent = `Final Time: ${formatTime(finalRunTime)}`;

    renderLeaderboard();
    checkLeaderboardQualification();

    postGameScreen.classList.remove('hidden');
}

function getLeaderboard() {
    return JSON.parse(localStorage.getItem(`leaderboard-${currentMode}`)) || [];
}

function saveLeaderboard(data) {
    localStorage.setItem(`leaderboard-${currentMode}`, JSON.stringify(data));
}

function renderLeaderboard() {
    const lb = getLeaderboard();
    leaderboardBody.innerHTML = '';

    if (lb.length === 0) {
        leaderboardBody.innerHTML = '<tr><td colspan="3" style="text-align:center; padding: 12px;">No entries yet!</td></tr>';
        return;
    }

    lb.forEach(entry => {
        const tr = document.createElement('tr');

        const tdTime = document.createElement('td');
        tdTime.textContent = formatTime(entry.time);
        tr.appendChild(tdTime);

        const tdInitials = document.createElement('td');
        tdInitials.textContent = entry.initials;
        tr.appendChild(tdInitials);

        const tdDate = document.createElement('td');
        tdDate.textContent = entry.date;
        tr.appendChild(tdDate);

        leaderboardBody.appendChild(tr);
    });
}

function checkLeaderboardQualification() {
    const lb = getLeaderboard();
    if (lb.length < 5 || finalRunTime < lb[lb.length - 1].time) {
        initialsEntry.classList.remove('hidden');
        playerInitials.value = '';
        submitScoreBtn.disabled = false;
        setTimeout(() => playerInitials.focus(), 100);
    } else {
        initialsEntry.classList.add('hidden');
    }
}

function submitLeaderboardScore() {
    const inits = playerInitials.value.trim().toUpperCase() || '---';
    const lb = getLeaderboard();

    const today = new Date();
    const dateStr = `${(today.getMonth()+1).toString().padStart(2,'0')}/${today.getDate().toString().padStart(2,'0')}/${today.getFullYear()}`;

    lb.push({ time: finalRunTime, initials: inits, date: dateStr });

    lb.sort((a, b) => a.time - b.time);

    if (lb.length > 5) lb.length = 5;

    saveLeaderboard(lb);
    renderLeaderboard();

    submitScoreBtn.disabled = true;
    initialsEntry.classList.add('hidden');
}

// Start the game when page loads
init();
