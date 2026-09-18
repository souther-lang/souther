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
     * <p><b>Every scope the published projection can make, and not the compilation alone.</b>
     * Asking the compilation would be enough if a narrowed report only ever held entries the whole
     * one holds. It does not: narrowed to one behavior, a report keeps a line an {@code invariant}
     * drew and loses the rows of the behaviors that showed a row can be written at it, so it
     * answers the same obligation again and comes back with an entry the compilation never had.
     * Those entries reach a reader through {@code only}, which is how a run answers a request
     * about one behavior, so a law about where entries leave a reader is about them too.
     *
     * <p>Which scopes those are is {@link ReportScopes}'s and is read off what a run may ask for,
     * rather than walked here as modules and then their behaviors — a walk that shape misses the
     * one a run allows and this report's nesting has no place for.
     *
     * <p>Repeats are no trouble here. What is asked of an entry is where it sends a reader, and an
     * entry met twice sends them to the same place both times.
     *
     * <p>Asking the compilation alone would be right again once narrowing invents nothing at every
     * grain. That is the thing that is not true, and it is what this reads instead of assuming
     * ({@link AdequacyReport#assessment()}).
     */
    private static final List<AdequacyUncertainty> UNRESOLVED = everythingUnresolved();

    private static List<AdequacyUncertainty> everythingUnresolved() {
        List<AdequacyUncertainty> out = new ArrayList<>();
        for (Compilation compilation : RepositoryModels.all()) {
            AdequacyReport whole = AdequacyReport.of(compilation);
            for (ReportScopes scope : ReportScopes.of(String.valueOf(compilation.modules()),
                    whole)) {
                out.addAll(scope.report().assessment().uncertainties());
            }
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
     * The arms with no model written to reach them, watched here until one is.
     *
     * <p><b>Not part of the law above and not a claim about these models.</b> What settles an arm is
     * a model written to produce the entry it answers, and three of the four arms an entry here can
     * reach have one. This is the fourth: nothing is written for it, so the only thing standing
     * between it and nobody noticing it has gone is that the corpora still happen to reach it.
     *
     * <p>Watching a corpus is the wrong instrument and is what this is a note about. A model made
     * more adequate takes such a reading away, and the day this fails the answer is not to put the
     * reading back — it is that the debt came due.
     *
     * <p>What the witness needs when it is written is an oracle on the whole route: no error
     * diagnostic, the expected uncertainty, the subject and reason it carries, and the arm read off
     * it. Reachability alone is not enough, which a source that reached this arm while failing to
     * compile is what showed.
     */
    private static final Set<String> AWAITING_DEDICATED_WITNESS = Set.of("LookAtWhatShowedNoRow");

    /**
     * The arms still owed a witness have not quietly stopped being reached.
     *
     * <p>A holding position. Nothing about the arms not named here is asked — those have models
     * written for them, and asking the corpora about them would answer a question about a written
     * witness with what the corpora are doing this week.
     */
    @Test
    void anArmStillOwedAWitnessIsStillReachedByTheseModels() {
        Set<String> reached = new LinkedHashSet<>();
        for (AdequacyUncertainty each : UNRESOLVED) {
            reached.add(ReaderDisposition.of(each).getClass().getSimpleName());
        }

        Set<String> gone = new LinkedHashSet<>(AWAITING_DEDICATED_WITNESS);
        gone.removeAll(reached);
        assertEquals(Set.of(), gone,
                () -> "an arm with no model written to reach it is no longer reached by these"
                        + " models either, so nothing holds it at all. Reached: " + reached);
    }
}
