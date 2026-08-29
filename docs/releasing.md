# Releasing

develop never carries a release version. It carries the snapshot of the version after the last one
released, and the number a release is cut at is set on `main`. That is what keeps a release to one
pull request: bumping develop to the release version and taking it back off afterwards were two
more, and both existed only because develop had been made to claim a number it was not.

## Cutting one

1. Open the release pull request, `develop` into `main`, titled `Souther <version>`. What goes in
   the body is what changed since the last tag —
   `git log --oneline v<previous>..develop --grep='Merge pull request' | wc -l` counts the pull
   requests, and `docs/adr/README.md` indexes the decisions with the reasoning behind each.

2. Merge it. develop survives the merge because a repository ruleset refuses to delete it: this
   repository deletes a head branch on merge, and the head of a release pull request is develop.
   It was deleted that way once, at `0.1.0-rc5`, and restored by pushing the commit back under the
   name.

3. On `main`, set the version and commit it there:

   ```sh
   git switch main && git pull
   bin/set-version.sh <version>
   git commit -am "Bump the reactor to <version>"
   git push
   ```

4. Tag that commit and push the tag:

   ```sh
   git tag -a v<version> -m "Souther <version>"
   git push origin v<version>
   ```

   The release workflow runs on the tag: it builds, and attaches `souther`, `souther.jar`,
   `souther-lsp.jar`, `souther.tmLanguage.json` and `SHA256SUMS` to the GitHub Release. A version
   with a hyphen in it is published as a prerelease, which the workflow reads off the tag rather
   than being told.

5. Publish to Maven Central from the tag:

   ```sh
   git switch --detach v<version>
   mvn -Prelease deploy
   ```

   `autoPublish` is false, so what this uploads waits in the Central Portal until it is published
   there. souther-runtime, souther-syntax, souther-compiler, souther-build-driver and souther-fmt go
   up, and souther-parent with them, being the pom they name as their parent. souther-cli,
   souther-lsp and souther-bench do not: the really-executable jar and the language server are
   distributed through GitHub Releases, and the benchmarks are not an artifact anyone depends on.

6. Move develop to the next snapshot:

   ```sh
   git switch develop && git pull
   bin/set-version.sh <next version>-SNAPSHOT
   ```

   on a branch of its own, as any other change to develop is. Nothing of the release goes back —
   what this carries is that the version just released is behind develop rather than ahead of it.
   `souther-lang/examples` names the snapshot, so it moves with this.

## The examples

`souther-lang/examples` pins the compiler in four places and has a `bin/set-version.sh` of its own.
It tracks the snapshot rather than a release, so a release does not move it. Building it against a
release is a check on the release, and worth doing before cutting one — but it is not a step of the
release, and a red examples build is a thing to fix there rather than a reason to hold the tag.
