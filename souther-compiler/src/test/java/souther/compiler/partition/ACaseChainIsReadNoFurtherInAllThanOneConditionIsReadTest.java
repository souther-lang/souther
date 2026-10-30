package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.PathReachability;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.meaning.MeaningsOfABody;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.WhyUnread;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A helper called on what the call before it answered reads, in each condition, every condition
 * before it — the value it compares is chosen by those — and the readings of one condition are
 * held to a figure in all, along every way, and not only along each.
 *
 * <p>Each condition of the chain is read once along each way the earlier calls could have gone,
 * and every way down stays under how many readings one way makes: so it is the total that grows
 * with the chain, and the total that stops it.
 *
 * <p>The amounts are numbers nothing declares a bound on. Every way the earlier calls could have
 * gone is then some input's, and none is left unread as one no run takes: the chain reads as many
 * ways as it has, which is what makes it the case for the total. With amounts that cannot fall
 * below nought most of those ways are closed, and the same chain is read to the end however long
 * it is ({@link ATakeChainIsReadAlongOnlyTheWaysARunTakesTest}).
 */
class ACaseChainIsReadNoFurtherInAllThanOneConditionIsReadTest {

    private static final int MOST = CompositionBudget.TOTAL_READINGS_OF_ONE_CONDITION.maximum();

    private static final WhyUnread PAST_THE_TOTAL = new WhyUnread.MoreTotalReadingsThanAreMade();

    /**
     * The longest chain whose conditions are each read within the figure in all. The last
     * condition of a chain of {@code calls} is read once for each case of every call before it
     * and of its own, two each, short of the first: {@code 2^calls - 2} readings.
     */
    private static final int WITHIN = 31 - Integer.numberOfLeadingZeros(MOST + 2);

    /** A chain of {@code calls} calls of the helper, each on what the call before it left. */
    static String model(int calls) {
        List<String> caps = new ArrayList<>();
        List<String> takes = new ArrayList<>();
        List<String> fills = new ArrayList<>();
        String rest = "used";
        for (int i = 0; i < calls; i++) {
            caps.add("c" + i + ": MB");
            takes.add("    let (a%d, rest%d) = take(%s, held.c%d)".formatted(i, i, rest, i));
            fills.add("a" + i);
            rest = "rest" + i;
        }
        return """
                module demo

                data MB = Int
                data Held = { CAPS }

                behavior draw : (used: MB, held: Held) -> List<MB>
                    constructs MB

                let draw (used, held) = {
                TAKES
                    [FILLS, REST]
                }

                let take (used: MB, cap: MB): (MB, MB) =
                    if used.value <= cap.value then (used, MB(0)) else (cap, MB(used.value - cap.value))
                """.replace("CAPS", String.join(", ", caps))
                .replace("TAKES", String.join("\n", takes))
                .replace("FILLS", String.join(", ", fills))
                .replace("REST", rest);
    }

    private record Read(Compilation compilation, List<Proposition> stated) {}

    /** Each chain read once, for every test asking about it. */
    private static final Map<Integer, Read> READ = new ConcurrentHashMap<>();

    private static Read read(int calls) {
        return READ.computeIfAbsent(calls, ACaseChainIsReadNoFurtherInAllThanOneConditionIsReadTest::readAnew);
    }

    private static Read readAnew(int calls) {
        Compilation compilation = Compilation.ofSource(model(calls), "Main");
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("demo")).value();
        assertNotNull(checked, "the chain under test compiles");
        AnalysisBody analysis = checked.analysisBodies().get("draw");
        RuleReadingSource rules = RuleReadings.of(compilation, "demo");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs("demo")).value().get("draw");
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                inputs.dependencies());
        MeaningsOfABody meanings = MeaningsOfABodyReading.of(analysis,
                () -> inputs.reading(rules), reads, rules.symbols(), rules.newtypes());
        return new Read(compilation, meanings.stated().values().stream()
                .map(each -> each.states()).toList());
    }

    private static List<WhyUnread> whysIn(Proposition stated) {
        return Proposition.stopsIn(stated);
    }

    /** The parts {@code stated} comes to written out, each as many times as it is held. */
    private static long partsIn(Proposition stated) {
        return 1 + stated.partsHeld().stream()
                .mapToLong(ACaseChainIsReadNoFurtherInAllThanOneConditionIsReadTest::partsIn)
                .sum();
    }

    private static long largest(Read read) {
        return read.stated().stream()
                .mapToLong(ACaseChainIsReadNoFurtherInAllThanOneConditionIsReadTest::partsIn)
                .max().orElseThrow();
    }

    @Test
    void withinTheFigureNoConditionIsGivenUpForIt() {
        Read within = read(WITHIN);

        for (Proposition stated : within.stated()) {
            assertFalse(whysIn(stated).contains(PAST_THE_TOTAL), stated::spelledOut);
        }
    }

    @Test
    void oneCallMoreGivesTheLastConditionsUpAtTheFigure() {
        Read past = read(WITHIN + 1);

        assertTrue(past.stated().stream().anyMatch(each -> whysIn(each).contains(PAST_THE_TOTAL)),
                "the conditions of the last call are read more times in all than are made");
    }

    /** No arm of the chain's forks is one nothing arrives at, on conditions given up at the
     *  figure. The question reads the conditions for itself, apart from the reading above. */
    @Test
    void whatWasGivenUpProvesNoArmUnreached() {
        Map<String, PathReachability.Answers> byBehavior = read(WITHIN + 1).compilation().db()
                .ask(new Adequacy.PathReached("demo")).value();

        byBehavior.get("draw").found().forEach((place, reached) ->
                assertFalse(reached instanceof souther.compiler.reach.Reachability.Unreachable,
                        () -> place + " is proved unreached on a reading that stopped"));
    }

    /**
     * A longer chain reads no condition further: the largest statement is the one the first chain
     * past the figure came to, and no larger, where unbounded it doubles with every call.
     */
    @Test
    void aLongerChainStatesNoMoreOfAnyCondition() {
        Read first = read(WITHIN + 1);
        Read longer = read(WITHIN + 2);

        assertTrue(largest(longer) <= largest(first),
                () -> largest(longer) + " parts past " + largest(first));
        assertTrue(largest(longer) <= CompositionBudget.PARTS_A_DERIVATION_CONCLUDES.maximum());
    }
}
