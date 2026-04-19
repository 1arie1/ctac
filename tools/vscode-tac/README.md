# ctac VSCode extension (htac + sbf)

This extension targets **human TAC** output from:

```bash
ctac pp ...
```

Language ids: `htac`, `sbf`  
Suggested file extensions: `.htac`, `.sbf`

## Features

- Syntax highlighting for:
  - `htac`: human TAC (`ctac pp` output)
  - `sbf`: rendered SBF files (`.sbf`)
- Go to Definition for:
  - block targets (jump target -> `block_id:` line in same file)
  - variables (`R*`, `B*`, `I*`, `F*`, `T*`, `S*`) to first assignment line in file
- Find References for variables (all occurrences in same file).

`sbf` and `htac` use separate grammar files.

## Use with `tac1.txt` / `tac2.txt` without renaming

Add this to VSCode `settings.json`:

```json
{
  "files.associations": {
    "**/examples/tac1.txt": "htac",
    "**/examples/tac2.txt": "htac",
    "**/*.sbf": "sbf"
  }
}
```

Or rename files to `.htac`:

- `tac1.htac`
- `tac2.htac`

## Local install

From this folder:

```bash
npm init -y
npx @vscode/vsce package
code --install-extension *.vsix
```

No build step is required (`extension.js` is plain JavaScript).
