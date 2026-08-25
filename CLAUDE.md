# Working in a second checkout

Two things bite when this repository is worked on from more than one directory at once — which is
what a worktree is for, and what an agent doing one issue while a person does another is. Both are
about state that lives outside the checkout.

## Worktrees

Take an issue in a worktree of its own, placed outside the repository directory:

```sh
git worktree add ../souther-327 -b feature/327-<slug> origin/develop
```

Branch from `origin/develop` rather than from whatever the main checkout has in it. A checkout is
often part-way through someone else's issue, and the point of the worktree is to leave that alone.

Outside the repository directory rather than in `.worktrees/`, because nothing ignores that path:
putting a worktree inside would need a `.gitignore` commit on whichever branch the main checkout is
sitting on, which is the branch being kept out of.

Branches are `feature/<issue>-<slug>` and merge into `develop`.

## Maven

Both checkouts share one local repository, and `mvn install` writes `souther-*` SNAPSHOTs into it —
so the second checkout can end up building against the first one's jars. Give the worktree a
writable local repository of its own and keep the shared one as a read-only tail (Maven 3.9's
chained local repository), which isolates what is installed without re-downloading anything:

```sh
mvn -o verify \
    -Dmaven.repo.local=../.m2-327 \
    -Dmaven.repo.local.tail="$HOME/.m2/repository"
```

Keep that head repository outside the worktree; inside, it shows up as an untracked directory. Add
`-Dmaven.repo.local.tail.ignoreAvailability=true` only if resolution through the tail complains.

**`-pl <module>` without `-am` reaches the tail for `souther-*`** and tests against whatever the
other checkout installed there. Always `-am`, or build the whole reactor. This is not a theoretical
hazard: a test has passed on its own and failed in the full run for exactly this reason.

**A `package` that skipped `clean` has left a stale `souther-cli/target/souther.jar`** — newer than
the classes it was supposedly built from, and behaving as the previous build. Run `mvn clean package`
before driving the CLI to check a change, or what is being checked is the build before the change.

`mvn verify` writes no `souther-*` anywhere, so the isolation above only starts to matter once
`install` is in play. It takes about two minutes over the whole reactor; while iterating, prefer one
targeted run:

```sh
mvn -o test -pl souther-runtime -am -Dtest=RepresentationsTest -Dsurefire.failIfNoSpecifiedTests=false
```

Do not add `-q` to a build that will take minutes — a silent one is indistinguishable from a hung
one.

## Cleaning up

```sh
git worktree remove ../souther-327
git branch -d feature/327-<slug>
rm -rf ../.m2-327
```
