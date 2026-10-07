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

   Setting a version that is not a snapshot freezes the adequacy report's `schemaVersion` the
   compiler writes, if no release has shipped it before: the script stages the schema as it ships
   under `souther-compiler/src/test/resources/souther/compiler/schema/released/`, and the commit
   above carries it. A version already frozen keeps the copy it first shipped with. The tests hold
   every frozen version to accepting what it shipped accepting, and refuse a release whose version
   has no copy.

4. Tag that commit and push the tag:

   ```sh
   git tag -a v<version> -m "Souther <version>"
   git push origin v<version>
   ```

   The release workflow runs on the tag: it builds, and attaches `souther`, `souther.jar`,
   `souther-lsp.jar`, `souther.tmLanguage.json` and `SHA256SUMS` to the GitHub Release. A version
   with a hyphen in it is published as a prerelease, which the workflow reads off the tag rather
   than being told.

5. Publish to Maven Central from the tag, in any checkout with nothing uncommitted:

   ```sh
   git switch --detach v<version>
   mvn -Prelease deploy
   ```

   The build reads the commit from git and writes it into every jar's manifest as
   `Implementation-Revision`, so a consumer that resolved `souther-compiler` can read the commit
   from the jar without going through the tag. What makes that true is checked rather than
   assumed. `-Prelease` fails on a change HEAD does not record, on a file git ignores in a place the
   build reads (`bin/require-clean-checkout.sh`: each module's `src`, and what the root pom lists as
   `souther.build.reads`), unless the commit is a full object id, and unless `v<version>` points at
   it; and it cleans every module before building it, so nothing an earlier build wrote goes in.
   An ignored file the build never reads, an editor's settings or `.DS_Store`, is no reason to
   refuse.

   A `v*` tag is protected by a repository ruleset that forbids updating and deleting it, with no
   bypass. A tag pushed for the wrong commit is not moved: the next version is released instead.

   `autoPublish` is true, so what this uploads is released once the Portal has validated it, with
   nothing left to do there. Every module goes up except the ones whose pom sets
   `souther.publish.skip`, each saying there why it is not a Maven artifact; souther-parent goes up
   with them, being the pom they name as their parent. The really-executable jar and the language
   server are distributed through GitHub Releases instead.

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

## The snapshot

`<version>-SNAPSHOT` on the Central Portal's snapshot repository is a commit of develop, published
by hand like a release. CI publishes nothing, a snapshot or a release. Publish once CI has passed
on develop's tip, from a checkout of it with nothing uncommitted:

```sh
git switch develop && git pull
mvn -Psnapshot deploy
```

The `snapshot` profile holds the coordinate to that meaning, as the `release` profile holds a
release to its tag. The repository keeps one coordinate per version and every publication
overwrites it, so a publication from anywhere else would silently replace what develop published.
The profile refuses a version that is not a snapshot, what the `release` profile refuses of the
tree (a change HEAD does not record, or an ignored file where the build reads), and a HEAD that is
not the commit develop points at on origin (`bin/require-develop-tip.sh`); and it cleans every
module before building it. A plain `mvn deploy` publishes nothing: the publishing plugin is used
only by the two profiles.

A release is a build of its own, so the build CI checked and the one published resolve the same
dependencies only because none of them can change: the `release` profile refuses a snapshot
dependency. The `snapshot` profile allows one, because what it publishes is replaced by the next
publication and promises nothing a dependency's moving could break.

A release and a snapshot go through the same plugin and not to the same place. A release is
uploaded to the Portal as one deployment, validated there and then published to Maven Central; a
snapshot is deployed straight to the snapshot repository, which Maven Central does not serve. A
build resolves a snapshot only if it declares
`https://central.sonatype.com/repository/maven-snapshots/` as a snapshot repository. The modules
left out are the same for both, being the ones that set `souther.publish.skip`.

## The examples

`souther-lang/examples` pins the compiler in four places and has a `bin/set-version.sh` of its own.
What it builds against is the version its own build names, and a snapshot only resolves there if
its build declares the snapshot repository above. Building it against a release is a check on the
release, and worth doing before cutting one — but it is not a step of the release, and a red
examples build is a thing to fix there rather than a reason to hold the tag.
