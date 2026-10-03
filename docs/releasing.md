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
   git clone --branch v<version> git@github.com:souther-lang/souther.git souther-v<version>
   cd souther-v<version>
   mvn -Prelease deploy
   ```

   From a fresh clone, because the release build refuses a tree that holds anything HEAD does not,
   an ignored `target` from an earlier build included.

   The build reads the commit from git and writes it into every jar's manifest as
   `Implementation-Revision`, so a consumer that resolved `souther-compiler` can read the commit
   from the jar without going through the tag. `-Prelease` fails unless the working tree is exactly
   what HEAD records (`bin/require-clean-checkout.sh`, ignored files included), the commit is a full
   object id, and `v<version>` points at it.

   A `v*` tag is protected by a repository ruleset that forbids updating and deleting it, with no
   bypass. A tag pushed for the wrong commit is not moved: the next version is released instead.

   `autoPublish` is true, so what this uploads is released once the Portal has validated it, with
   nothing left to do there. souther-runtime, souther-syntax, souther-compiler, souther-build-driver
   and souther-fmt go up, and souther-parent with them, being the pom they name as their parent.
   souther-cli, souther-lsp and souther-bench do not: the really-executable jar and the language
   server are distributed through GitHub Releases, and the benchmarks are not an artifact anyone
   depends on.

6. Take main into develop and move develop to the next snapshot, in one commit straight to develop:

   ```sh
   git switch develop && git pull
   git merge --no-commit --no-ff main
   bin/set-version.sh <next version>-SNAPSHOT
   git commit -am "Take develop to the snapshot after the release"
   git push
   ```

   The merge is what keeps the next release to one pull request. Both branches write the version
   line, so unless develop holds the commit that set the released number, each side has changed that
   line since their common ancestor and every module's pom comes back as a conflict. With the merge
   here, the next release's merge base is the bump on main, main has not touched the line since, and
   only develop has.

   `set-version.sh` runs before the commit so that no commit on develop ever carries a release
   version: what the merge brings in is written over while it is still staged. What develop ends up
   with is the version just released being behind it rather than ahead.

   No pull request. The whole of it is a merge and what `set-version.sh` wrote, there is nothing in
   it to review, and it is the tail of a release rather than work anyone is proposing. This is the
   one change to develop that goes straight there; anything carrying a decision still opens one.

   `souther-lang/examples` names the snapshot, so it moves with this.

## Publishing a snapshot

What develop carries is published to the Central Portal's snapshot repository with a plain deploy,
from any checkout of develop:

```sh
mvn deploy
```

Without `-Prelease`. That profile is a release's: it refuses any tree but a clean checkout of
`v<version>`, which a snapshot never has, and it signs and attaches sources and javadoc, which a
snapshot does not need. The publishing plugin itself is in the plain build, so both go to the same
place, and the modules a release leaves out are left out of a snapshot as well.

`souther-lang/examples` resolves the snapshot from there, so it sees a change on develop once one
is published.

## The examples

`souther-lang/examples` pins the compiler in four places and has a `bin/set-version.sh` of its own.
It tracks the snapshot rather than a release, so a release does not move it. Building it against a
release is a check on the release, and worth doing before cutting one — but it is not a step of the
release, and a red examples build is a thing to fix there rather than a reason to hold the tag.
