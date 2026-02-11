// app.js
"use strict";

const $ = (sel) => document.querySelector(sel);

const fileInput = $("#fileInput");
const dirInput  = $("#dirInput");
const btnClear = $("#btnClear");

const docSelect = $("#docSelect");
const onlyDiffSents = $("#onlyDiffSents");
const onlyDiffEdges = $("#onlyDiffEdges");
const showPos = $("#showPos");
const searchInput = $("#searchInput");

const sentList = $("#sentList");
const treeView = $("#treeView");
const treeMeta = $("#treeMeta");
const authorList = $("#authorList");
const fileList = $("#fileList");

const btnDownloadTxt = $("#btnDownloadTxt");
const btnCopy = $("#btnCopy");

// Gold UI
const goldAuthorA = $("#goldAuthorA");
const goldAuthorB = $("#goldAuthorB");
const goldMode = $("#goldMode");
const goldLabelMode = $("#goldLabelMode");
const goldTokenMode = $("#goldTokenMode");
const goldSentCountMode = $("#goldSentCountMode");
const goldIncludeComments = $("#goldIncludeComments");
const goldMarkMisc = $("#goldMarkMisc");
const goldFixOrphanHeads = $("#goldFixOrphanHeads");
const goldFilename = $("#goldFilename");
const btnGoldDownload = $("#btnGoldDownload");

const dataset = {
  docs: new Map(),
  activeDocKey: null,
  activeSentIndex: null,
  settings: {
    showPos: false,
  }
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
    if (tid.includes("-") || tid.includes(".")) continue;
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
  const upos  = doc.authors.map(a => a.sentences[sentIndex]?.tokens.get(tokId)?.upos ?? null);
  const xpos  = doc.authors.map(a => a.sentences[sentIndex]?.tokens.get(tokId)?.xpos ?? null);

  const presentForms = forms.filter(x => x !== null);
  if (presentForms.length === 0) return `${tokId}:❓`;

  const distinctForms = uniq(presentForms);
  const sameFormEverywhere = (distinctForms.length === 1 && presentForms.length === doc.authors.length);

  const posSuffix = (i) => {
    if (!dataset.settings.showPos) return "";
    const u = upos[i] ?? "∅";
    const x = xpos[i] ?? "∅";
    return `[{${u}|${x}}]`;
  };

  if (sameFormEverywhere){
    const f = distinctForms[0];
    // POS: wenn überall da, nimm A
    return dataset.settings.showPos ? `${tokId}:${f}${posSuffix(0)}` : `${tokId}:${f}`;
  }

  const parts = [];
  for (let i=0;i<doc.authors.length;i++){
    const f = forms[i];
    parts.push(`${doc.authors[i].name}=${f === null ? "∅" : (dataset.settings.showPos ? `${f}${posSuffix(i)}` : f)}`);
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
// Tree Rendering
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

  const meta = `Autoren: ${doc.authors.length} · Kanten-Union: ${info.edgeKeys.length} · fehlt: ${info.missingEdges} · Label-Diff: ${info.labelDiffEdges}`;
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

// -------------------------
// Gold generation
// -------------------------
function getAuthorById(doc, id){
  return doc.authors.find(a => a.id === id) || null;
}

function unionSortedNums(a, b){
  const s = new Set([...a, ...b]);
  return [...s].sort((x,y)=>x-y);
}

function miscJoin(parts){
  const xs = parts.filter(Boolean);
  if (xs.length === 0) return "_";
  return xs.join("|");
}

function resolveEdge(dep, eA, eB, opt, perTokMisc, conflictNotes){
  const mark = (key) => { if (opt.markMisc) perTokMisc.add(key); };

  const defaultConflict = (why) => {
    mark("Gold=conflict");
    if (opt.includeComments) conflictNotes.push(`dep=${dep}: ${why}`);
    return { head: 0, deprel: "dep" };
  };

  const chooseLabel = (la, lb) => {
    if (la === lb) return la;
    if (opt.includeComments) conflictNotes.push(`dep=${dep}: label-diff (${opt.labelMode === "preferA" ? "A" : "B"} gewählt) A=${la} B=${lb}`);
    mark("Gold=labeldiff");
    return opt.labelMode === "preferA" ? la : lb;
  };

  const pick = (e) => e ? ({ head: e.head, deprel: e.deprel }) : null;

  if (opt.mode === "preferA"){
    return pick(eA) || pick(eB) || defaultConflict("missing in both");
  }
  if (opt.mode === "preferB"){
    return pick(eB) || pick(eA) || defaultConflict("missing in both");
  }

  if (opt.mode === "unionPreferA" || opt.mode === "unionPreferB"){
    const first = (opt.mode === "unionPreferA") ? eA : eB;
    const second = (opt.mode === "unionPreferA") ? eB : eA;

    if (first && second){
      if (first.head === second.head){
        const deprel = chooseLabel(first.deprel, second.deprel);
        return { head: first.head, deprel };
      }
      mark("Gold=headconflict");
      if (opt.includeComments) conflictNotes.push(`dep=${dep}: head-conflict (${opt.mode.endsWith("A") ? "A" : "B"} gewählt) A=${eA.head} B=${eB.head}`);
      return { head: first.head, deprel: first.deprel };
    }
    return pick(first) || pick(second) || defaultConflict("missing in both");
  }

  if (opt.mode === "intersection"){
    if (eA && eB && eA.head === eB.head){
      const deprel = chooseLabel(eA.deprel, eB.deprel);
      return { head: eA.head, deprel };
    }
    if (eA && !eB) return defaultConflict("only in A (intersection)");
    if (!eA && eB) return defaultConflict("only in B (intersection)");
    if (eA && eB) return defaultConflict(`head-conflict (intersection) A=${eA.head} B=${eB.head}`);
    return defaultConflict("missing in both");
  }

  if (opt.mode === "strictAgree"){
    if (eA && eB && eA.head === eB.head && eA.deprel === eB.deprel){
      return { head: eA.head, deprel: eA.deprel };
    }
    if (eA && !eB) return defaultConflict("only in A (strict)");
    if (!eA && eB) return defaultConflict("only in B (strict)");
    if (eA && eB){
      if (eA.head !== eB.head) return defaultConflict(`head-conflict (strict) A=${eA.head} B=${eB.head}`);
      return defaultConflict(`label-conflict (strict) A=${eA.deprel} B=${eB.deprel}`);
    }
    return defaultConflict("missing in both");
  }

  // fallback
  return pick(eA) || pick(eB) || defaultConflict("missing in both");
}

function generateGoldConllu(doc, aId, bId, opt){
  const A = getAuthorById(doc, aId);
  const B = getAuthorById(doc, bId);
  if (!A || !B) throw new Error("Autor A/B ungültig");

  const sCount = (opt.sentCountMode === "min")
    ? Math.min(A.sentences.length, B.sentences.length)
    : Math.max(A.sentences.length, B.sentences.length);

  const out = [];

  for (let s=0; s<sCount; s++){
    const sa = A.sentences[s] || { tokens:new Map(), edges:new Map() };
    const sb = B.sentences[s] || { tokens:new Map(), edges:new Map() };

    const ids = unionSortedNums([...sa.tokens.keys()], [...sb.tokens.keys()]);
    if (ids.length === 0) continue;

    const baseTokFromA = (opt.tokenMode === "preferA");
    const perTokMiscById = new Map(); // id -> Set
    const conflictNotes = [];

    const pickTok = (id) => {
      const ta = sa.tokens.get(id) || null;
      const tb = sb.tokens.get(id) || null;

      let chosen = null;
      if (baseTokFromA) chosen = ta || tb;
      else chosen = tb || ta;

      const misc = new Set();
      if (!chosen){
        misc.add("Gold=tokmissing");
        if (opt.includeComments) conflictNotes.push(`tok=${id}: missing in both`);
        return { tok: {form:"_", upos:"_", xpos:"_"}, misc };
      }

      // mismatch marker
      if (ta && tb){
        if (ta.form !== tb.form || ta.upos !== tb.upos || ta.xpos !== tb.xpos){
          misc.add("Gold=tokmismatch");
          if (opt.includeComments){
            conflictNotes.push(`tok=${id}: mismatch A=(${ta.form},${ta.upos},${ta.xpos}) B=(${tb.form},${tb.upos},${tb.xpos})`);
          }
        }
      }
      return { tok: chosen, misc };
    };

    // sentence header/comments
    const textA = sentenceText(sa);
    const textB = sentenceText(sb);
    const text = (baseTokFromA ? (textA || textB) : (textB || textA));

    if (opt.includeComments){
      out.push(`# sent_id = ${s+1}`);
      out.push(`# text = ${text}`);
      out.push(`# gold_from = ${A.name} | ${B.name}`);
      out.push(`# gold_mode = ${opt.mode}; label=${opt.labelMode}; tokens=${opt.tokenMode}; sentCount=${opt.sentCountMode}`);
    }

    // token lines
    for (const id of ids){
      const { tok, misc } = pickTok(id);

      // resolve edge for this dep id
      const eA = sa.edges.get(id) || null;
      const eB = sb.edges.get(id) || null;

      const edgeMisc = new Set();
      const resolved = resolveEdge(
        id,
        eA ? {head:eA.head, deprel:eA.deprel} : null,
        eB ? {head:eB.head, deprel:eB.deprel} : null,
        opt,
        edgeMisc,
        conflictNotes
      );

      // orphan head fix
      let head = resolved.head;
      let deprel = resolved.deprel;

      if (opt.fixOrphanHeads && head !== 0 && !ids.includes(head)){
        if (opt.includeComments) conflictNotes.push(`tok=${id}: orphan head=${head} (→ 0)`);
        edgeMisc.add("Gold=orphanhead");
        head = 0;
        deprel = "dep";
      }

      const miscSet = new Set();
      if (opt.markMisc){
        for (const m of misc) miscSet.add(m);
        for (const m of edgeMisc) miscSet.add(m);
      }

      // Columns: ID FORM LEMMA UPOS XPOS FEATS HEAD DEPREL DEPS MISC
      const cols = [
        String(id),
        tok.form ?? "_",
        "_",
        tok.upos ?? "_",
        tok.xpos ?? "_",
        "_",
        String(head),
        deprel ?? "_",
        "_",
        miscJoin([...miscSet])
      ];
      out.push(cols.join("\t"));
    }

    if (opt.includeComments && conflictNotes.length){
      out.push(`# gold_conflicts = ${conflictNotes.length}`);
      // kurze Liste, aber nicht pro Token 100 Zeilen; dennoch hilfreich:
      for (const c of conflictNotes.slice(0, 30)){
        out.push(`# gold_note = ${c}`);
      }
      if (conflictNotes.length > 30){
        out.push(`# gold_note = ... (${conflictNotes.length - 30} weitere)`);
      }
    }

    out.push(""); // sentence separator
  }

  return out.join("\n");
}

// -------------------------
// Rendering UI
// -------------------------
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
      renderGoldAuthorSelects();
      renderFileList();
      renderAll(); // damit Baum gleich neue Namen nutzt
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

function renderFileList(){
  const doc = dataset.docs.get(dataset.activeDocKey);
  if (!doc){
    fileList.value = "–";
    fileList.disabled = true;
    return;
  }
  fileList.disabled = false;
  const lines = [];
  lines.push(`Dokument: ${doc.label}`);
  lines.push(`Autoren: ${doc.authors.length}`);
  lines.push("");
  for (const a of doc.authors){
    lines.push(`- ${a.name}  ⇢  ${a.fileName}`);
  }
  fileList.value = lines.join("\n");
}

function enableGoldUI(enabled){
  const els = [
    goldAuthorA, goldAuthorB, goldMode, goldLabelMode, goldTokenMode, goldSentCountMode,
    goldIncludeComments, goldMarkMisc, goldFixOrphanHeads, goldFilename, btnGoldDownload
  ];
  for (const el of els) el.disabled = !enabled;
}

function renderGoldAuthorSelects(){
  const doc = dataset.docs.get(dataset.activeDocKey);
  goldAuthorA.innerHTML = `<option value="">–</option>`;
  goldAuthorB.innerHTML = `<option value="">–</option>`;

  if (!doc || doc.authors.length < 2){
    enableGoldUI(false);
    return;
  }
  enableGoldUI(true);

  for (const a of doc.authors){
    const o1 = document.createElement("option");
    o1.value = a.id;
    o1.textContent = `${a.name}`;
    goldAuthorA.appendChild(o1);

    const o2 = document.createElement("option");
    o2.value = a.id;
    o2.textContent = `${a.name}`;
    goldAuthorB.appendChild(o2);
  }

  // defaults: erste zwei Autoren
  if (!goldAuthorA.value) goldAuthorA.value = doc.authors[0].id;
  if (!goldAuthorB.value) goldAuthorB.value = doc.authors[1].id;
}

function renderAll(){
  const hasData = dataset.docs.size > 0;
  searchInput.disabled = !hasData;

  renderDocSelect();
  renderAuthors();
  renderFileList();
  renderGoldAuthorSelects();
  renderSentenceList();
  renderTreePanel();
}

// -------------------------
// Events
// -------------------------
docSelect.addEventListener("change", () => {
  dataset.activeDocKey = docSelect.value;
  dataset.activeSentIndex = null;
  renderAll();
});

onlyDiffSents.addEventListener("change", renderAll);
onlyDiffEdges.addEventListener("change", renderAll);

showPos.addEventListener("change", () => {
  dataset.settings.showPos = showPos.checked;
  renderAll();
});

searchInput.addEventListener("input", renderAll);

btnClear.addEventListener("click", () => {
  dataset.docs.clear();
  dataset.activeDocKey = null;
  dataset.activeSentIndex = null;
  fileInput.value = "";
  dirInput.value = "";
  enableGoldUI(false);
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

btnGoldDownload.addEventListener("click", () => {
  const doc = dataset.docs.get(dataset.activeDocKey);
  if (!doc) return;

  const aId = goldAuthorA.value;
  const bId = goldAuthorB.value;
  if (!aId || !bId || aId === bId){
    alert("Bitte zwei unterschiedliche Autoren auswählen.");
    return;
  }

  const opt = {
    mode: goldMode.value,
    labelMode: goldLabelMode.value,
    tokenMode: goldTokenMode.value,
    sentCountMode: goldSentCountMode.value,
    includeComments: goldIncludeComments.checked,
    markMisc: goldMarkMisc.checked,
    fixOrphanHeads: goldFixOrphanHeads.checked,
  };

  const name = (goldFilename.value || "gold.conllu").trim() || "gold.conllu";
  const text = generateGoldConllu(doc, aId, bId, opt);
  downloadText(name, text);
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

enableGoldUI(false);
renderAll();
