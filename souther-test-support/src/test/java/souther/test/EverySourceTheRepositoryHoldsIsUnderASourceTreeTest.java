package souther.test;

import org.junit.jupiter.api.Test;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * That looking only where sources are kept is not looking in too few places.
 *
 * <p>A sweep built on {@link RepositoryLayout#southerSources()} descends into
 * {@code <module>/src} and nowhere else, which is what keeps a build's own files out of it. The
 * cost of stating where to look rather than what to leave out is that a source put somewhere else
 * is not looked at, and nothing about the sweep would say so: it would go on passing, over a
 * corpus quietly one file short.
 *
 * <p>So this holds the one direction that matters. Every {@code .sou} the repository owns lies
 * under some module's source tree; a {@code docs/tour/hello.sou} that somebody commits fails here,
 * naming itself, rather than being silently left out of every check the formatter has.
 *
 * <p>Only that direction. The other — that every source found is one git holds — would be a
 * different claim, and a false one while somebody is writing a file they have not added yet. That a
 * new source is swept before it is committed is what the sweep is for.
 */
class EverySourceTheRepositoryHoldsIsUnderASourceTreeTest {

    private static final RepositoryLayout REPOSITORY = RepositoryLayout.ofWorkingDirectory();

    @Test
    void everyTrackedSourceIsSomewhereTheSweepsLook() {
        List<Path> swept = REPOSITORY.southerSources();
        List<Path> missed = new ArrayList<>();
        GitIndex git = GitIndex.of(REPOSITORY);
        for (Path tracked : git.trackedSoutherSources()) {
            if (!swept.contains(git.resolve(tracked).normalize())) {
                missed.add(tracked);
            }
        }
        assertEquals(List.of(), missed,
                "these are Souther sources this repository holds that no module keeps under its"
                        + " src, so every sweep that reads sources reads around them; put them"
                        + " under a module's src, or teach RepositoryLayout the tree they are in");
    }

    /**
     * And the sweep is reading something.
     *
     * <p>A layout that found no source trees at all would satisfy the check above by having nothing
     * to compare, so the count is held from the other side too.
     */
    @Test
    void andThereAreSourcesToHaveMissed() {
        assertTrue(GitIndex.of(REPOSITORY).trackedSoutherSources().size() >= 20,
                "this repository holds Souther sources for the check above to be about");
    }
}
