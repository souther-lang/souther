package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.ReadingPolicy;
import souther.compiler.inputs.RuleWithoutALine;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Front;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.regex.PatternPlan;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A position whose rules about the strings were not built says that, and not that the model states
 * nothing there.
 *
 * <p>The two are opposite sentences and the difference is invisible from the report unless
 * something makes it. A rule stating which strings stand at a position holds it to them and this
 * measure has no line for that, which is a fact about the model; a rule whose set this compiler
 * did not make leaves whether it holds the position to anything unknown, which is a fact about the
 * compiler. Filed alike, the second goes out as the first and an author is told their format
 * restricts a position when nobody worked out what it admits.
 *
 * <p><b>Both sides of the allowance, over one model.</b> What a reading may build is granted by the
 * compilation ({@link Front.Reading}), so a test standing in for one grants a different figure and
 * runs the same rule through the same readers. Asked at the standard grant alone, this would pass
 * over a compiler that files nothing at all when the building stops.
 */
class APositionThatDidNotBuildItsStringsSaysSoRatherThanNothingTest {

    /**
     * A format on a newtype, which is a rule about the strings at the position and no order.
     *
     * <p>Written as a pattern rather than as a prefix on purpose: a prefix is a run of the order
     * and comes back as an edge, and what is being asked here is the answer for a rule that
     * restricts the position without bounding it.
     */
    private static final String MODEL = """
            module probe.format

            data Code = String
                invariant format = String.matches("[A-Z]{2}", value)

            data Ok

            behavior f : (c: Code) -> Ok
            """;

    /** What a compilation grants a reading that has room to build the machines its rules name. */
    private static final ReadingPolicy WITH_ROOM = souther.compiler.query.ReadAs.THE_COMPILATION_DOES;

    /**
     * And one with room for nothing.
     *
     * <p>One state is what the smallest machine there is costs, so a pattern of two characters is
     * refused and every rule of this position goes unpublished with it. The other two figures are
     * the compilation's: what is being changed is the allowance to build and nothing else.
     */
    private static final ReadingPolicy WITH_NO_ROOM = new ReadingPolicy(
            WITH_ROOM.dnfExpansionLimit(), WITH_ROOM.scalePlacesLimit(),
            new PatternPlan.Budget(1, 1));

    @Test
    void aRuleReadToItsStringsIsTheModelHoldingThePositionToThem() {
        assertEquals(List.of("RuleRestrictingToAdmittedValues"), reasonsUnder(WITH_ROOM),
                "the format was read and the position is held to what it admits, which is a fact"
                        + " about the model and not about this compiler");
    }

    /**
     * And under an allowance that builds nothing, the position is one nothing about the model
     * follows from.
     *
     * <p>Two halves, because either alone passes over the answer this is about. Nothing says the
     * model holds the position to what the rule admits — that would be a sentence about a set
     * nobody made — and the position does not come back divided no way either: what is published
     * is that a question about what it admits went unanswered.
     */
    @Test
    void andOneWhoseStringsWereNotBuiltIsThisCompilerFallingShort() {
        assertEquals(List.of(), reasonsUnder(WITH_NO_ROOM),
                "the same rule under an allowance that builds nothing states nothing about the"
                        + " model: a set nobody made holds no position to anything");
        assertEquals(List.of("c: CannotDerive / ADMITTED_VALUES at c"),
                positionsUnder(WITH_NO_ROOM),
                "and the position says which question was left open rather than coming back as one"
                        + " the model divides no way");
    }

    /** What every rule of the model came to that drew no line, under {@code policy}. */
    private static List<String> reasonsUnder(ReadingPolicy policy) {
        List<String> out = new ArrayList<>();
        for (PartitionEvidence evidence : read(policy)) {
            for (RuleWithoutALine each : evidence.rulesWithoutALine()) {
                out.add(each.why().getClass().getSimpleName());
            }
        }
        return out;
    }

    /** What each position no class came back for came to, and what is standing at it. */
    private static List<String> positionsUnder(ReadingPolicy policy) {
        List<String> out = new ArrayList<>();
        for (PartitionEvidence evidence : read(policy)) {
            for (UndividedPosition each : evidence.notDerivable()) {
                List<String> asked = new ArrayList<>();
                evidence.unanswered().forEach(one -> asked.add(one.asked().toString()));
                out.add(each.at() + ": " + each.why().getClass().getSimpleName()
                        + " / " + String.join(", ", asked));
            }
        }
        return out;
    }

    private static List<PartitionEvidence> read(ReadingPolicy policy) {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.db().set(new Front.Reading(), policy);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();

        List<PartitionEvidence> out = new ArrayList<>();
        for (String module : compilation.modules()) {
            Map<String, PartitionEvidence> coverage =
                    compilation.db().ask(new Adequacy.Coverage(module)).value();
            if (coverage != null) {
                out.addAll(coverage.values());
            }
        }
        return out;
    }
}
