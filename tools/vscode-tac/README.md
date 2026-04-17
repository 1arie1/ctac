# ctac VSCode extension (htac)

This extension targets **human TAC** output from:

```bash
ctac pp ...
```

Language id: `htac`  
Suggested file extension: `.htac`

## Features

- Syntax highlighting tuned for `ctac pp` output.
- Go to Definition for:
  - block targets (jump target -> `block_id:` line in same file)
  - variables (`R*`, `B*`, `I*`, `F*`, `T*`, `S*`) to first assignment line in file
- Find References for variables (all occurrences in same file).

## Use with `tac1.txt` / `tac2.txt` without renaming

Add this to VSCode `settings.json`:

```json
{
  "files.associations": {
    "**/examples/tac1.txt": "htac",
    "**/examples/tac2.txt": "htac"
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
