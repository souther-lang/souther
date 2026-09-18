package souther.compiler.report;

import souther.compiler.conformance.RepositoryModels;
import souther.compiler.observe.RunSensitivity;
import souther.compiler.query.Compilation;
import souther.test.ClosedWorldContract;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Everything the analysis could not answer leaves a reader somewhere, and somewhere they can act.
 *
 * <p>The question a reader of {@code undetermined} has is what to do next, and until now the report
 * answered it only where the answer was a row. What is held here is the other half: every entry
 * reaches exactly one {@link ReaderDisposition}, and which one follows from what the compiler
 * established rather than from a formatter's reading of the words.
 *
 * <p><b>Asked of the assessment and not of what keeps a verdict open.</b> Those are the same list
 * only where a scope has no gap, and where it has one the verdict shows a reader nothing while the
 * entries are still there. Asked through the verdict, this law covered whichever models happened to
 * be short of something and refused about nothing — and a module short of a thing this compiler has
 * a whole arm for went unasked because a sibling module in the same compilation was refused.
 *
 * <p><b>Over the models this repository carries and not over values a test built.</b> A
 * disposition worked out from a hand-made entry says the switch is total, which javac already
 * says; what it does not say is that the entries a real model produces reach the arms anybody
 * expected. Those are two claims and only the second can go wrong quietly.
 */
@ClosedWorldContract
class EveryUnresolvedAdequacyFactLeavesTheReaderSomewhereTest {

    /**
     * Every unanswered thing every model here produces, which is where a claim about them has to be
     * held.
     *
     * <p>Built once for the class. Nothing else here asks a bench corpus how adequate its rows
     * are, so the measuring of one of them is paid by this and by nothing else — measured, it is
     * that one model rather than the population, which is built for whoever asks first.
     *
     * <p>It is not narrowed to make it cheaper. Narrowed, the law is held over fewer of the arms it
     * is about, which is a smaller claim rather than a faster one. What it is instead is where such
     * a claim belongs: its subject is the models this repository carries, so it runs where they are
     * the subject.
     *
     * <p>One scope apiece and not one per selection. What a narrowed report holds is a selection
     * from what the whole one holds, so asking the compilation asks about all of them
     * ({@link AdequacyReport#assessment()}).
     */
    private static final List<AdequacyUncertainty> UNRESOLVED = everythingUnresolved();

    private static List<AdequacyUncertainty> everythingUnresolved() {
        List<AdequacyUncertainty> out = new ArrayList<>();
        for (Compilation compilation : RepositoryModels.all()) {
            out.addAll(AdequacyReport.of(compilation).assessment().uncertainties());
        }
        return List.copyOf(out);
    }

    /**
     * One apiece, and the population is not empty.
     *
     * <p>The second half is what keeps this from passing over a corpus that answers everything. A
     * law about unanswered things held over none of them is a law nothing has been held to.
     */
    @Test
    void everyUnresolvedFactReachesADisposition() {
        List<AdequacyUncertainty> unresolved = UNRESOLVED;

        assertFalse(unresolved.isEmpty(), "the models here go without things, which is what this is"
                + " a law about");
        for (AdequacyUncertainty each : unresolved) {
            assertTrue(ReaderDisposition.of(each) != null,
                    () -> each + " was not answered and leaves a reader nowhere");
        }
    }

    /**
     * And a wider run is offered exactly where a wider run would answer it.
     *
     * <p>The one arm a reader acts on without looking at anything, so it is the one that must not be
     * offered where it is wrong: told to measure again over a rule this compiler has no reading for,
     * an author runs the build and meets the same sentence.
     */
    @Test
    void aWiderRunIsOfferedExactlyWhereItWouldAnswer() {
        for (AdequacyUncertainty each : UNRESOLVED) {
            boolean offered = ReaderDisposition.of(each) instanceof ReaderDisposition.WidenTheRun;

            assertEquals(each.runSensitivity() == RunSensitivity.MAY_CHANGE, offered,
                    () -> "a wider run is offered for " + each + " and it says "
                            + each.runSensitivity());
        }
    }

    /**
     * The dispositions a model this repository carries reaches.
     *
     * <p>Written out so that a change which quietly stops producing an entry, or starts answering
     * one with a different arm, is read here rather than found by someone running the command. The
     * set and not the counts: how many of a kind a model holds unanswered moves with the model.
     */
    private static final Set<String> WITNESSED = Set.of(
            "LookAtTheRule", "LookAtWhyNothingWasMeasured", "LookAtWhatShowedNoRow");

    /**
     * Each of those is reached, and an arm not among them is not said anything about here.
     *
     * <p>What is held is one direction. An arm these models reach only while one of them is short of
     * something is reached by accident — the models are evidence about the language and not fixtures
     * for these arms, and one made more adequate takes such a reading away. So an arm missing from
     * the list above is not thereby a defect, and neither is one that turns up in what these models
     * reach without being listed: what would settle either is a model written to reach the arm
     * through the analysis, which is a different thing from a corpus happening to.
     *
     * <p>Which is why nothing here is asked of the arms not listed. Asked of them, this would answer
     * a question about a written witness with what the corpora are doing this week, and a corpus
     * change would read as that witness arriving or leaving.
     */
    @Test
    void theModelsHereReachTheseDispositions() {
        Set<String> reached = new LinkedHashSet<>();
        for (AdequacyUncertainty each : UNRESOLVED) {
            reached.add(ReaderDisposition.of(each).getClass().getSimpleName());
        }

        Set<String> unwitnessed = new LinkedHashSet<>(WITNESSED);
        unwitnessed.removeAll(reached);
        assertEquals(Set.of(), unwitnessed,
                () -> "a disposition held to be reached by these models is reached by none of them."
                        + " Reached: " + reached);
    }
}
