package souther.architecture;

import org.junit.jupiter.api.Test;
import souther.test.ClosedWorldContract;
import souther.test.GitIndex;
import souther.test.Nightly;
import souther.test.RepositoryLayout;

import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * The hook refuses nothing in a source the repository holds.
 *
 * <p>The hook is the half of CI a parser can answer, and what it must never be is stricter than the
 * half it stands for: a commit it stops that CI would accept is a commit stopped for nothing. CI
 * is green over every Java file git tracks, so a file the hook refuses is a rule reading more than
 * the Error Prone check it mirrors. That is what each of its rules has been found doing, one shape
 * at a time, in the first commit that happened to touch a file written that way.
 *
 * <p>This asks every rule at once, over the whole of what is tracked, so that the next shape is found
 * where it is written and not in somebody's commit. The two rules that have a pair of cases per
 * shape — {@link TheCommitHookRefusesAnUnusedLocalOnlyWhereErrorProneDoesTest} and
 * {@link TheCommitHookRefusesTheCollectionClassesErrorProneRefusesInASignatureTest} — say where the
 * edge of each is; this says that there is no edge left that the sources cross.
 *
 * <p>Left to the nightly, because every rule reads every tracked source, javadoc included, and that
 * is more than a minute. No cheaper way to ask it was found: a sample of the files would not be the
 * population a shape turns up in. And a shape found by the morning is found as well as one found by
 * the change that wrote it, since the hook only ever stops the next commit that touches such a file,
 * and the red names the file and the rule.
 */
@ClosedWorldContract
@Nightly
class TheCommitHookRefusesNothingInWhatCIAcceptsTest {

    @Test
    void everyJavaFileGitTracksIsAcceptedByEveryRuleTheHookRuns() throws Exception {
        RepositoryLayout layout = RepositoryLayout.ofWorkingDirectory();
        GitIndex index = GitIndex.of(layout);
        List<Path> sources = index.trackedFiles().stream()
                .filter(tracked -> tracked.toString().endsWith(".java"))
                .map(index::resolve)
                .toList();
        assertFalse(sources.isEmpty(), "the repository holds Java sources, so this asked about some");

        List<String> refused = TheCommitHook.refusals(sources).stream()
                .map(each -> layout.root().relativize(each.file()) + ":" + each.line() + " "
                        + each.rule() + " " + each.message())
                .toList();

        assertEquals(List.of(), refused);
    }
}
