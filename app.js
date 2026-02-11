// app.js
// CoNLL-U Tree-Vergleich (Multi-Autor) – lokal, ohne Server
// Idee/Logik angelehnt an trees.py: Union-Kanten pro Satz, Root/Children, Cycle-Schutz. :contentReference[oaicite:1]{index=1}

"use strict";

const $ = (sel) => document.querySelector(sel);

const fileInput = $("#fileInput");
const dirInput  = $("#dirInput");
const btnClear = $("#btnClear");

const docSelect = $("#docSelect");
const onlyDiffSents = $("#onlyDiffSents");
const onlyDiffEdges = $("#onlyDiffEdges");
const searchInput = $("#searchInput");

const sentList = $("#sentList");
const treeView = $("#treeView");
const treeMeta = $("#treeMeta");
const authorList = $("#authorList");

const btnDownloadTxt = $("#btnDownloadTxt");
const btnCopy = $("#btnCopy");

// dataset = { docs: Map(docKey -> doc), activeDocKey, activeSentIndex }
const dataset = {
  docs: new Map(),
  activeDocKey: null,
  activeSentIndex: null,
};

function makeId(){
  if (crypto?.randomUUID) return crypto.randomUUID();
  return "id_" + Math.random().toString(16).slice(2) + "_" + Date.now();
}

function basenameNoExt(name){
  const base = name.split(/[\\/]/).pop();
  return base.replace(/\.[^.]+$/, "");
}

function dirOfRelativePath(rel){
  const parts = rel.split("/");
  if (parts.length <= 1) return ".";
  parts.pop();
  return parts.join("/") || ".";
}

function uniq(arr){ return [...new Set(arr)]; }

async function readFileText(file){
  return new Promise((resolve, reject) => {
    const fr = new FileReader();
    fr.onload = () => resolve(String(fr.result || ""));
    fr.onerror = () => reject(fr.error);
    fr.readAsText(file, "utf-8");
  });
}

function downloadText(filename, text){
  const blob = new Blob([text], {type: "text/plain;charset=utf-8"});
  const a = document.createElement("a");
  a.href = URL.createObjectURL(blob);
  a.download = filename;
  document.body.appendChild(a);
  a.click();
  setTimeout(() => { URL.revokeObjectURL(a.href); a.remove(); }, 0);
}

// -------------------------
// CoNLL-U Parser
// -------------------------
// Pro Satz: tokens Map(tokId -> {form, upos, xpos}), edges Map(depId -> {head, deprel})
function parseConllu(text){
  const sentences = [];
  let tokens = new Map();
  let edges = new Map();

  const pushSentence = () => {
    if (tokens.size === 0 && edges.size === 0) return;
    sentences.push({ tokens, edges });
    tokens = new Map();
    edges = new Map();
  };

  for (const raw of text.split(/\r?\n/)){
    const line = raw.replace(/\r$/, "");
    if (line.trim() === ""){
      pushSentence();
      continue;
    }
    if (line.startsWith("#")) continue;

    const cols = line.split("\t");
    if (cols.length < 8) continue;

    const tid = cols[0];
    if (tid.includes("-") || tid.includes(".")) continue; // MW-tokens / empty nodes skip
    if (!/^\d+$/.test(tid)) continue;

    const tokId = Number(tid);
    const form = cols[1] ?? "_";
    const upos = cols[3] ?? "_";
    const xpos = cols[4] ?? "_";
    const headStr = cols[6] ?? "_";
    const deprel = cols[7] ?? "_";

    tokens.set(tokId, { form, upos, xpos });

    if (/^\d+$/.test(headStr)){
      edges.set(tokId, { head: Number(headStr), deprel });
    }
  }
  pushSentence();
  return sentences;
}

function sentenceText(sent){
  const ids = [...sent.tokens.keys()].sort((a,b)=>a-b);
  return ids.map(id => sent.tokens.get(id)?.form ?? "❓").join(" ").trim();
}

// -------------------------
// Load files
// -------------------------
async function loadFilesAsSingleDoc(files){
  const authors = [];
  for (const f of files){
    const text = await readFileText(f);
    authors.push({
      id: makeId(),
      name: basenameNoExt(f.name),
      fileName: f.name,
      sentences: parseConllu(text),
    });
  }
  const sentCount = Math.max(0, ...authors.map(a => a.sentences.length));
  return { key:"single", label:"Einzel-Dokument", authors, sentCount };
}

async function loadDirectoryFiles(files){
  const byDoc = new Map();

  for (const f of files){
    const rel = f.webkitRelativePath || f.name;
    const docKey = dirOfRelativePath(rel);
    if (!byDoc.has(docKey)){
      byDoc.set(docKey, { key: docKey, label: docKey, authors: [], sentCount: 0 });
    }
    const doc = byDoc.get(docKey);

    const text = await readFileText(f);
    const sentences = parseConllu(text);

    doc.authors.push({
      id: makeId(),
      name: basenameNoExt(f.name),
      fileName: rel,
      sentences,
    });
    doc.sentCount = Math.max(doc.sentCount, sentences.length);
  }

  return byDoc;
}

// -------------------------
// Vergleichslogik (Multi-Autor)
// -------------------------
function getSentence(doc, sentIndex){
  const perAuthor = doc.authors.map(a => a.sentences[sentIndex] || { tokens:new Map(), edges:new Map() });

  const edgeKeySet = new Set();
  for (const s of perAuthor){
    for (const [dep, e] of s.edges.entries()){
      edgeKeySet.add(`${dep}|${e.head}`);
    }
  }
  const edgeKeys = [...edgeKeySet].map(k => {
    const [dep, head] = k.split("|").map(Number);
    return { dep, head, key:k };
  });

  const children = new Map();
  for (const ek of edgeKeys){
    const list = children.get(ek.head) || [];
    list.push(ek.dep);
    children.set(ek.head, list);
  }
  for (const [h, deps] of children.entries()){
    deps.sort((a,b)=>a-b);
  }

  const nodes = new Set();
  const incoming = new Set();
  for (const ek of edgeKeys){
    nodes.add(ek.dep);
    if (ek.head !== 0){
      nodes.add(ek.head);
      incoming.add(ek.dep);
    }
  }
  const roots = [...nodes].filter(n => !incoming.has(n)).sort((a,b)=>a-b);
  const rootsFinal = roots.length ? roots : (nodes.size ? [Math.min(...nodes)] : []);

  const texts = perAuthor.map(sentenceText);
  const distinctTexts = uniq(texts.filter(t => t.length));
  const anyTextDiff = distinctTexts.length > 1;

  let missingEdges = 0;
  let labelDiffEdges = 0;
  for (const ek of edgeKeys){
    const labels = [];
    let present = 0;
    for (const s of perAuthor){
      const e = s.edges.get(ek.dep);
      if (e && e.head === ek.head){
        present++;
        labels.push(e.deprel);
      }
    }
    if (present !== perAuthor.length) missingEdges++;
    else if (uniq(labels).length > 1) labelDiffEdges++;
  }

  return { perAuthor, edgeKeys, children, roots: rootsFinal, texts, anyTextDiff, missingEdges, labelDiffEdges };
}

function tokenDisplay(doc, sentIndex, tokId){
  const forms = doc.authors.map(a => a.sentences[sentIndex]?.tokens.get(tokId)?.form ?? null);
  const present = forms.filter(x => x !== null);
  if (present.length === 0) return `${tokId}:❓`;

  const distinct = uniq(present);
  if (distinct.length === 1 && present.length === doc.authors.length){
    return `${tokId}:${distinct[0]}`;
  }

  const parts = [];
  for (let i=0;i<doc.authors.length;i++){
    const f = forms[i];
    parts.push(`${doc.authors[i].name}=${f === null ? "∅" : f}`);
  }
  return `${tokId}:${parts.join(" | ")}`;
}

function edgeStatus(doc, sentIndex, dep, head){
  const labels = [];
  const labelByAuthor = [];
  let present = 0;

  for (const a of doc.authors){
    const e = a.sentences[sentIndex]?.edges.get(dep);
    if (e && e.head === head){
      present++;
      labels.push(e.deprel);
      labelByAuthor.push([a.name, e.deprel]);
    } else {
      labelByAuthor.push([a.name, null]);
    }
  }

  const total = doc.authors.length;

  if (present === total){
    const distinct = uniq(labels);
    if (distinct.length === 1){
      return { emoji:"✅", labelText: distinct[0], kind:"same", present, total };
    }
    return {
      emoji:"⚠️",
      labelText: labelByAuthor.map(([n,l]) => `${n}:${l ?? "∅"}`).join(" | "),
      kind:"labelDiff",
      present, total
    };
  }

  const presentNames = labelByAuthor.filter(([_,l]) => l !== null).map(([n,l]) => `${n}:${l}`);
  const missingNames = labelByAuthor.filter(([_,l]) => l === null).map(([n]) => n);
  const detail = `${present}/${total}  ` +
    (presentNames.length ? `+ ${presentNames.join(", ")}` : "") +
    (missingNames.length ? `  − ${missingNames.join(", ")}` : "");
  return { emoji:"➖", labelText: detail.trim(), kind:"partial", present, total };
}

// -------------------------
// Rendering
// -------------------------
function renderTree(docKey, sentIndex){
  const doc = dataset.docs.get(docKey);
  if (!doc) return { text:"–", meta:"–", txtExport:"" };

  const info = getSentence(doc, sentIndex);
  const sentIdHuman = sentIndex + 1;

  const baseText = info.texts.find(t => t.length) || "";
  const lines = [];
  lines.push(`📝 S${sentIdHuman}: ${baseText}${info.anyTextDiff ? "  ✍️(Text-Diff)" : ""}`);

  if (info.anyTextDiff){
    for (let i=0;i<doc.authors.length;i++){
      lines.push(`   · ${doc.authors[i].name}: ${info.texts[i] || ""}`);
    }
  }
  lines.push("");

  const rec = (head, prefix, pathSet) => {
    const deps = info.children.get(head) || [];
    for (let i=0;i<deps.length;i++){
      const dep = deps[i];
      const last = (i === deps.length - 1);
      const conn = last ? "└─" : "├─";
      const nextPrefix = prefix + (last ? "  " : "│ ");

      const st = edgeStatus(doc, sentIndex, dep, head);
      if (!(onlyDiffEdges.checked && st.kind === "same")){
        lines.push(`${prefix}${conn} ${st.emoji} ${st.labelText} → ${tokenDisplay(doc, sentIndex, dep)}`);
      }

      if (pathSet.has(dep)){
        lines.push(`${nextPrefix}🔁 (cycle)`);
        continue;
      }
      rec(dep, nextPrefix, new Set([...pathSet, dep]));
    }
  };

  for (let r=0;r<info.roots.length;r++){
    const root = info.roots[r];
    lines.push(`🌱 ${tokenDisplay(doc, sentIndex, root)}`);
    rec(root, "", new Set([root]));
    if (r !== info.roots.length - 1) lines.push("");
  }

  const meta = `Autoren: ${doc.authors.length} · Kanten-Union: ${info.edgeKeys.length} · fehlt bei manchen: ${info.missingEdges} · Label-Diff: ${info.labelDiffEdges}`;
  const outText = lines.join("\n").trimEnd();
  return { text: outText, meta, txtExport: outText + "\n" };
}

function buildSentenceIndex(docKey){
  const doc = dataset.docs.get(docKey);
  if (!doc) return [];
  const list = [];

  for (let i=0;i<doc.sentCount;i++){
    const info = getSentence(doc, i);
    const text = info.texts.find(t => t.length) || "(leer)";
    const hasDiff = info.anyTextDiff || info.missingEdges > 0 || info.labelDiffEdges > 0;

    list.push({
      idx:i, sentIdHuman:i+1, text,
      anyTextDiff: info.anyTextDiff,
      missingEdges: info.missingEdges,
      labelDiffEdges: info.labelDiffEdges,
      hasDiff
    });
  }
  return list;
}

function renderSentenceList(){
  const docKey = dataset.activeDocKey;
  const doc = dataset.docs.get(docKey);
  sentList.innerHTML = "";

  if (!doc){
    sentList.classList.add("empty");
    sentList.textContent = "Noch keine Daten geladen.";
    return;
  }

  const q = (searchInput.value || "").toLowerCase().trim();
  const items = buildSentenceIndex(docKey).filter(it => {
    if (onlyDiffSents.checked && !it.hasDiff) return false;
    if (q && !it.text.toLowerCase().includes(q)) return false;
    return true;
  });

  if (items.length === 0){
    sentList.classList.add("empty");
    sentList.textContent = "Keine Sätze passen zu den Filtern.";
    return;
  }
  sentList.classList.remove("empty");

  const frag = document.createDocumentFragment();
  for (const it of items){
    const div = document.createElement("div");
    div.className = "sent-item" + (dataset.activeSentIndex === it.idx ? " active" : "");
    div.dataset.idx = String(it.idx);

    const id = document.createElement("div");
    id.className = "sent-id";
    id.textContent = `S${it.sentIdHuman}`;

    const txt = document.createElement("div");
    txt.className = "sent-text";
    txt.textContent = it.text;

    const badges = document.createElement("div");
    badges.className = "sent-badges";

    if (it.anyTextDiff){
      const b = document.createElement("span");
      b.className = "badge tok";
      b.textContent = "✍️ Text";
      badges.appendChild(b);
    }
    if (it.labelDiffEdges > 0){
      const b = document.createElement("span");
      b.className = "badge warn";
      b.textContent = `⚠️ ${it.labelDiffEdges}`;
      badges.appendChild(b);
    }
    if (it.missingEdges > 0){
      const b = document.createElement("span");
      b.className = "badge miss";
      b.textContent = `➖ ${it.missingEdges}`;
      badges.appendChild(b);
    }
    if (!it.anyTextDiff && it.labelDiffEdges === 0 && it.missingEdges === 0){
      const b = document.createElement("span");
      b.className = "badge ok";
      b.textContent = "✅";
      badges.appendChild(b);
    }

    div.appendChild(id);
    div.appendChild(txt);
    div.appendChild(badges);

    div.addEventListener("click", () => {
      dataset.activeSentIndex = it.idx;
      renderAll();
      if (window.matchMedia("(max-width: 980px)").matches){
        treeView.scrollIntoView({behavior:"smooth", block:"start"});
      }
    });

    frag.appendChild(div);
  }
  sentList.appendChild(frag);
}

function renderAuthors(){
  const doc = dataset.docs.get(dataset.activeDocKey);
  authorList.innerHTML = "";

  if (!doc){
    authorList.classList.add("empty");
    authorList.textContent = "–";
    return;
  }
  authorList.classList.remove("empty");

  const frag = document.createDocumentFragment();
  for (const a of doc.authors){
    const row = document.createElement("div");
    row.className = "author-row";

    const inp = document.createElement("input");
    inp.value = a.name;
    inp.addEventListener("input", () => {
      a.name = inp.value.trim() || a.name;
      renderAll();
    });

    const file = document.createElement("div");
    file.className = "file";
    file.title = a.fileName;
    file.textContent = a.fileName;

    row.appendChild(inp);
    row.appendChild(file);
    frag.appendChild(row);
  }
  authorList.appendChild(frag);
}

function renderDocSelect(){
  docSelect.innerHTML = "";
  const keys = [...dataset.docs.keys()].sort((a,b) => a.localeCompare(b));

  if (keys.length === 0){
    docSelect.disabled = true;
    const opt = document.createElement("option");
    opt.value = "";
    opt.textContent = "–";
    docSelect.appendChild(opt);
    return;
  }

  docSelect.disabled = false;
  for (const k of keys){
    const doc = dataset.docs.get(k);
    const opt = document.createElement("option");
    opt.value = k;
    opt.textContent = doc?.label ?? k;
    docSelect.appendChild(opt);
  }

  docSelect.value = dataset.activeDocKey ?? keys[0];
}

function renderTreePanel(){
  const doc = dataset.docs.get(dataset.activeDocKey);

  if (!doc){
    treeView.classList.add("empty");
    treeView.textContent = "Lade Daten, wähle dann links einen Satz.";
    treeMeta.textContent = "–";
    btnDownloadTxt.disabled = true;
    btnCopy.disabled = true;
    return;
  }
  if (dataset.activeSentIndex === null){
    treeView.classList.add("empty");
    treeView.textContent = "Wähle links einen Satz.";
    treeMeta.textContent = `Dokument: ${doc.label} · Autoren: ${doc.authors.length}`;
    btnDownloadTxt.disabled = true;
    btnCopy.disabled = true;
    return;
  }

  const out = renderTree(dataset.activeDocKey, dataset.activeSentIndex);
  treeView.classList.remove("empty");
  treeView.textContent = out.text;
  treeMeta.textContent = out.meta;

  btnDownloadTxt.disabled = false;
  btnCopy.disabled = false;
}

function renderAll(){
  const hasData = dataset.docs.size > 0;
  searchInput.disabled = !hasData;

  renderDocSelect();
  renderAuthors();
  renderSentenceList();
  renderTreePanel();
}

docSelect.addEventListener("change", () => {
  dataset.activeDocKey = docSelect.value;
  dataset.activeSentIndex = null;
  renderAll();
});

onlyDiffSents.addEventListener("change", renderAll);
onlyDiffEdges.addEventListener("change", renderAll);
searchInput.addEventListener("input", renderAll);

btnClear.addEventListener("click", () => {
  dataset.docs.clear();
  dataset.activeDocKey = null;
  dataset.activeSentIndex = null;
  fileInput.value = "";
  dirInput.value = "";
  renderAll();
});

btnDownloadTxt.addEventListener("click", () => {
  if (!dataset.activeDocKey || dataset.activeSentIndex === null) return;
  const doc = dataset.docs.get(dataset.activeDocKey);
  const out = renderTree(dataset.activeDocKey, dataset.activeSentIndex);
  const filename = `tree_${(doc?.label || "doc").replace(/[^\w\-]+/g,"_")}_S${dataset.activeSentIndex+1}.txt`;
  downloadText(filename, out.txtExport);
});

btnCopy.addEventListener("click", async () => {
  try{
    await navigator.clipboard.writeText(treeView.textContent || "");
    btnCopy.textContent = "Kopiert ✓";
    setTimeout(() => (btnCopy.textContent = "Ansicht kopieren"), 900);
  }catch{
    alert("Clipboard nicht verfügbar. Markiere den Text im Tree-Feld und kopiere manuell.");
  }
});

fileInput.addEventListener("change", async (ev) => {
  const files = [...(ev.target.files || [])];
  if (files.length === 0) return;

  dataset.docs.clear();
  const doc = await loadFilesAsSingleDoc(files);
  dataset.docs.set(doc.key, doc);
  dataset.activeDocKey = doc.key;
  dataset.activeSentIndex = null;
  renderAll();
});

dirInput.addEventListener("change", async (ev) => {
  const files = [...(ev.target.files || [])].filter(f => /\.conll(u)?$|\.txt$/i.test(f.name));
  if (files.length === 0) return;

  dataset.docs.clear();
  const byDoc = await loadDirectoryFiles(files);
  for (const [k, doc] of byDoc.entries()){
    doc.authors.sort((a,b) => a.fileName.localeCompare(b.fileName));
    dataset.docs.set(k, doc);
  }
  dataset.activeDocKey = [...dataset.docs.keys()].sort((a,b)=>a.localeCompare(b))[0] || null;
  dataset.activeSentIndex = null;
  renderAll();
});

renderAll();
