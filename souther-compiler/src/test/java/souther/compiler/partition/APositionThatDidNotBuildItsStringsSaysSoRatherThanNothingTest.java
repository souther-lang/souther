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

    /**
     * A rule about the strings the position's own answer has no use for.
     *
     * <p>What the position admits is the two alternatives joined, and one of them says nothing
     * about it — so the answer is every string and the pattern is never made. The rule is still a
     * rule about the strings there, and a reader that draws lines wants what it leaves on its own,
     * so it is one of the sets the reading hands on.
     *
     * <p>Which is what makes this the model for the other allowance. The answer is exact and cost
     * nothing; what a small allowance for handing rules on refuses is the set the reader was
     * promised, and that is a different shortfall about the same position.
     */
    private static final String ONE_THE_ANSWER_DOES_NOT_NEED = """
            module probe.spare

            data Code = String
                invariant named = value == "x"
                invariant other = value /= "x"
                invariant format = String.matches("[A-Z]{2}", value)

            data Ok

            behavior f : (c: Code) -> Ok
            """;

    /**
     * A rule whose strings are a run of the order, which is an edge wherever it is read.
     *
     * <p>The model for what the second allowance may not do. A prefix read to its strings puts a
     * line on the position, so a reading that answered it out of the allowance for handing rules on
     * would be publishing a boundary at a position whose own answer it had just said it could not
     * build — the two allowances answering one model, and the wider of them speaking where the
     * narrower had stopped.
     */
    private static final String ONE_THAT_WOULD_DRAW_A_LINE = """
            module probe.prefix

            data Code = String
                invariant starts = String.startsWith("A", value)

            data Ok

            behavior f : (c: Code) -> Ok
            """;

    /** What a compilation grants a reading that has room to build the machines its rules name. */
    private static final ReadingPolicy WITH_ROOM = souther.compiler.query.ReadAs.THE_COMPILATION_DOES;

    /**
     * And one with room for nothing to answer a position with.
     *
     * <p>One state is what the smallest machine there is costs, so a pattern of two characters is
     * refused and the position's own answer comes back widened. The other figures are the
     * compilation's: what is being changed is one allowance and nothing else.
     */
    private static final ReadingPolicy WITH_NO_ROOM = new ReadingPolicy(
            WITH_ROOM.dnfExpansionLimit(), WITH_ROOM.scalePlacesLimit(),
            new PatternPlan.Budget(1, 1),
            souther.compiler.values.AsACompilationAllows.whatARuleLeaves());

    /** And one with room for the answer and none for handing the rules on. */
    private static final ReadingPolicy WITH_NOTHING_TO_HAND_ON_WITH = new ReadingPolicy(
            WITH_ROOM.dnfExpansionLimit(), WITH_ROOM.scalePlacesLimit(),
            souther.compiler.values.AsACompilationAllows.admittedValues(),
            new PatternPlan.Budget(1, 1));

    /** And the pair the other way round, which is the one nothing may be published under. */
    private static final ReadingPolicy ROOM_TO_HAND_ON_AND_NONE_TO_ANSWER = new ReadingPolicy(
            WITH_ROOM.dnfExpansionLimit(), WITH_ROOM.scalePlacesLimit(),
            new PatternPlan.Budget(1, 1),
            souther.compiler.values.AsACompilationAllows.whatARuleLeaves());

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
        assertEquals(List.of("c: CannotDerive"), positionsUnder(WITH_NO_ROOM),
                "and the position comes back as one nothing about the model follows from, rather"
                        + " than as one the model divides no way");
        assertEquals(List.of("c"), askedAbout(WITH_NO_ROOM),
                "with the question that was left open standing at it, which is what holds the"
                        + " measure open");
    }

    /**
     * A position whose answer is exact and whose rules could not be handed on says which of the two
     * it was short of.
     *
     * <p>The two shortfalls are different facts about one position and only one of them is about
     * what the model admits. Here the answer is every string and was free, and what is missing is
     * the set one rule leaves on its own — so a reader is told this compiler fell short and is
     * never told the model holds the position to something, and the position is not one the model
     * divides no way either.
     */
    @Test
    void andAPositionWhoseAnswerStandsSaysWhenItsRulesCouldNotBeHandedOn() {
        assertEquals(List.of(), reasonsIn(ONE_THE_ANSWER_DOES_NOT_NEED, WITH_ROOM),
                "with room to hand them on there is nothing outstanding: the rule leaves the"
                        + " position every string and every string is where it was found");
        assertEquals(List.of("RulesNotHandedOnAsSets"),
                reasonsIn(ONE_THE_ANSWER_DOES_NOT_NEED, WITH_NOTHING_TO_HAND_ON_WITH),
                "and with none, the position says the set its rule leaves was not worked out —"
                        + " without naming the rule, which was affordable, and without saying"
                        + " anything about what the position admits, which is exact");
    }

    /**
     * And the allowance for handing rules on does not answer where the answer could not.
     *
     * <p>The rule here is one that draws a line when it is read, so a reading that made its machine
     * out of the second allowance would put a boundary on the position — at a position whose own
     * answer it could not build. What the second allowance is for is the sets the first had no use
     * for, not the ones it could not manage, and the difference is only visible on a rule whose set
     * would show.
     */
    @Test
    void andTheAllowanceForHandingRulesOnDoesNotAnswerWhereTheAnswerCouldNot() {
        assertEquals(List.of(), positionsIn(ONE_THAT_WOULD_DRAW_A_LINE, WITH_ROOM),
                "read with room, the position is answered and nothing about it is outstanding");

        assertEquals(List.of("c: CannotDerive"),
                positionsIn(ONE_THAT_WOULD_DRAW_A_LINE, ROOM_TO_HAND_ON_AND_NONE_TO_ANSWER),
                "and with none — however much is left to hand its rules on with — it is a position"
                        + " nothing about the model follows from");
        assertEquals(List.of(), reasonsIn(ONE_THAT_WOULD_DRAW_A_LINE,
                        ROOM_TO_HAND_ON_AND_NONE_TO_ANSWER),
                "nothing is said about what its rules leave, and the rule is one that leaves a"
                        + " line when it is read: a set the answer never made draws none");
    }

    /** What every rule of the model came to that drew no line, under {@code policy}. */
    private static List<String> reasonsUnder(ReadingPolicy policy) {
        return reasonsIn(MODEL, policy);
    }

    private static List<String> reasonsIn(String model, ReadingPolicy policy) {
        List<String> out = new ArrayList<>();
        for (PartitionEvidence evidence : read(model, policy)) {
            for (RuleWithoutALine each : evidence.rulesWithoutALine()) {
                out.add(each.why().getClass().getSimpleName());
            }
        }
        return out;
    }

    /** Which of the three each position no class came back for came to. */
    private static List<String> positionsUnder(ReadingPolicy policy) {
        return positionsIn(MODEL, policy);
    }

    private static List<String> positionsIn(String model, ReadingPolicy policy) {
        List<String> out = new ArrayList<>();
        for (PartitionEvidence evidence : read(model, policy)) {
            for (UndividedPosition each : evidence.notDerivable()) {
                out.add(each.at() + ": " + each.why().getClass().getSimpleName());
            }
        }
        return out;
    }

    /** The positions a question of the model stands at, asked of the question itself. */
    private static List<String> askedAbout(ReadingPolicy policy) {
        List<String> out = new ArrayList<>();
        for (PartitionEvidence evidence : read(MODEL, policy)) {
            evidence.unanswered().forEach(each -> out.add(each.at()));
        }
        return out;
    }

    private static List<PartitionEvidence> read(String model, ReadingPolicy policy) {
        Compilation compilation = Compilation.ofSource(model, "Main");
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
