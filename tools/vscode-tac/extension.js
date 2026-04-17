"use strict";

const vscode = require("vscode");

const TOKEN_RE = /[A-Za-z0-9_]+(?::\d+)?/;
const VAR_RE = /^[RBIFTS][A-Za-z0-9_]*(?::\d+)?$/;

function collectBlockDefinitions(document) {
  const defs = new Map();
  const labelRe = /^\s*([A-Za-z0-9_]+):\s*$/;
  for (let i = 0; i < document.lineCount; i += 1) {
    const line = document.lineAt(i).text;
    const m = labelRe.exec(line);
    if (!m) {
      continue;
    }
    const blockId = m[1];
    const start = line.indexOf(blockId);
    if (start < 0) {
      continue;
    }
    defs.set(blockId, new vscode.Location(document.uri, new vscode.Position(i, start)));
  }
  return defs;
}

function collectVariableDefinitions(document) {
  const defs = new Map();
  // pp/human command lines: "  R1 = ...", "  B2 = ...", etc.
  const assignRe = /^\s*([RBIFTS][A-Za-z0-9_]*(?::\d+)?)\s*=/;
  for (let i = 0; i < document.lineCount; i += 1) {
    const line = document.lineAt(i).text;
    const m = assignRe.exec(line);
    if (!m) {
      continue;
    }
    const sym = m[1];
    const start = line.indexOf(sym);
    if (start < 0) {
      continue;
    }
    const arr = defs.get(sym) || [];
    arr.push(new vscode.Location(document.uri, new vscode.Position(i, start)));
    defs.set(sym, arr);
  }
  return defs;
}

function collectTokenReferences(document, token) {
  const refs = [];
  const safeToken = token.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const re = new RegExp(`\\b${safeToken}\\b`, "g");
  for (let i = 0; i < document.lineCount; i += 1) {
    const line = document.lineAt(i).text;
    let m;
    while ((m = re.exec(line)) !== null) {
      refs.push(
        new vscode.Location(
          document.uri,
          new vscode.Range(i, m.index, i, m.index + token.length)
        )
      );
    }
  }
  return refs;
}

function activate(context) {
  const definitionProvider = {
    provideDefinition(document, position) {
      const range = document.getWordRangeAtPosition(position, TOKEN_RE);
      if (!range) {
        return null;
      }
      const token = document.getText(range);

      const blockDefs = collectBlockDefinitions(document);
      if (blockDefs.has(token)) {
        return blockDefs.get(token);
      }

      if (VAR_RE.test(token)) {
        const varDefs = collectVariableDefinitions(document).get(token) || [];
        if (varDefs.length > 0) {
          // First assignment as the "definition".
          return varDefs[0];
        }
      }
      return null;
    }
  };

  const referenceProvider = {
    provideReferences(document, position, _context) {
      const range = document.getWordRangeAtPosition(position, TOKEN_RE);
      if (!range) {
        return [];
      }
      const token = document.getText(range);
      if (!VAR_RE.test(token)) {
        return [];
      }
      return collectTokenReferences(document, token);
    }
  };

  context.subscriptions.push(
    vscode.languages.registerDefinitionProvider({ language: "htac" }, definitionProvider),
    vscode.languages.registerReferenceProvider({ language: "htac" }, referenceProvider)
  );
}

function deactivate() {}

module.exports = {
  activate,
  deactivate
};
