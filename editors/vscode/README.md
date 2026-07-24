# Souther for VS Code

Syntax highlighting for the Souther language (`.sou`).

The TextMate grammar in `syntaxes/souther.tmLanguage.json` is generated from the compiler's
lexer, so it stays in step with the language. Regenerate it with:

```sh
mvn -q -pl souther-compiler exec:java \
  -Dexec.mainClass=net.unit8.souther.compiler.highlight.TmLanguageGenerator \
  -Dexec.args="editors/vscode/syntaxes/souther.tmLanguage.json"
```

A test (`TmLanguageGeneratorTest`) fails if the committed grammar drifts from the generator, so a
keyword added to the lexer forces the grammar — and this file — to be regenerated.

## Language server

The Souther language server is a self-contained jar that speaks LSP over stdio. Build it with:

```sh
mvn -q -pl souther-lsp -am package
# → souther-lsp/target/souther-lsp.jar
```

It provides diagnostics (all syntax errors plus the first semantic error), the document outline,
hover, go-to-definition, find-references, rename, name completion, quick-fix code actions (a
did-you-mean spelling fix), formatting, and semantic tokens — the last read the CST, so a type name
and a value are coloured differently even though Souther identifiers are not capitalised.

Formatting is also available on the command line: `souther fmt <file.sou>` prints the canonical
form, `souther fmt -w <file.sou>` rewrites in place, and `souther fmt --check <file.sou>` exits
non-zero if a file is not already formatted (for CI).

## Running the client in VS Code

`extension.js` launches the jar over stdio via `vscode-languageclient`. To try it from source:

```sh
mvn -q -pl souther-lsp -am package                 # build the server jar
mkdir -p editors/vscode/server
cp souther-lsp/target/souther-lsp.jar editors/vscode/server/
cd editors/vscode && npm install                   # fetch vscode-languageclient
```

Then open `editors/vscode` in VS Code and press F5 (Extension Development Host), or package it with
`vsce package`. Point `souther.server.jar` at another jar, or `souther.server.java` at a specific
`java`, through the settings if the defaults do not fit.

## Packaging and publishing

The bundled `server/souther-lsp.jar` is a build output, not tracked in git. Build and stage it
before packaging:

```sh
mvn -q -pl souther-lsp -am package
mkdir -p editors/vscode/server
cp souther-lsp/target/souther-lsp.jar editors/vscode/server/
cd editors/vscode
npm ci
npm run package                                    # → souther-<version>.vsix
```

`npm run package` runs `@vscode/vsce` (a dev dependency). `vscode:prepublish` refuses to package
if `server/souther-lsp.jar` is missing, so the VSIX never ships without the server.

The `.github/workflows/release-vscode.yml` workflow automates this. Push a `vscode-v*` tag to build
the jar, package the VSIX, and attach it to the matching GitHub Release:

```sh
git tag vscode-v0.1.0
git push origin vscode-v0.1.0
```

`workflow_dispatch` runs the same build and uploads the VSIX as a workflow artifact without cutting
a release.

Publishing to a marketplace is manual. Download the `.vsix` from the GitHub Release (or build it
locally with `npm run package`), then upload it under the `wolfchief` publisher at
<https://marketplace.visualstudio.com/manage>. A manual upload needs neither a Personal Access Token
nor an Azure subscription — both are only required for the `vsce publish` CLI.
