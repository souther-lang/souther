package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.RuleWithoutALine;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * An element compared against a value beside the list is reached at every value of both, though
 * the comparison sits in one case of the element and the list is held to more than one element.
 *
 * <p>That the arm is the one the element is says what stands there and nothing of how many
 * elements there are but that there is one, so a list holding an element of that case is a run
 * that gets to the comparison. A rule that reads only how many a list holds says nothing of what
 * its elements are, whether it asks for one or for two, so it leaves each element every value.
 * A rule keeping the elements apart is a reading of its own, and the control below holds that it
 * is still asked.
 */
class ARelationReachedOnlyInOneCaseOfAnElementIsReachedAtEveryValueTest {

    private static final String DECLARED = """
            module example.cases

            data UserId = String
                invariant String.length(value) >= 1

            data Call = { owner: UserId }
            data Meeting = { owner: UserId, minutes: Int }
            data Activity = Call | Meeting

            data Several = List<Meeting>
                invariant atLeastTwo = List.length(value) >= 2

            data Apart = List<Meeting>
                invariant atLeastTwo = List.length(value) >= 2
                invariant different = List.allDistinctBy(.owner, value)

            let meetingOf (a: Activity, owner: UserId): List<Meeting> =
                match a with
                    | Call -> []
                    | Meeting as m -> if m.owner == owner then [ m ] else []

            behavior inACase : (activities: List<Activity>, owner: UserId) -> List<Meeting>

            let inACase (activities, owner) = List.flatMap(a -> meetingOf(a, owner), activities)

            behavior ofSeveral : (meetings: Several, owner: UserId) -> List<Meeting>

            let ofSeveral (meetings, owner) = List.filter(m -> m.owner == owner, meetings.value)

            behavior keptApart : (meetings: Apart, owner: UserId) -> List<Meeting>

            let keptApart (meetings, owner) = List.filter(m -> m.owner == owner, meetings.value)
            """;

    /** Said at each of the two places the comparison reads. */
    private static final List<BlockReason.RuleWithoutLineReason> RELATES_TWO_VALUES = List.of(
            new BlockReason.ComparisonRelatingTwoValues(),
            new BlockReason.ComparisonRelatingTwoValues());

    @Test
    void aComparisonInOneCaseOfTheElementRelatesTwoValues() {
        assertEquals(RELATES_TWO_VALUES, whyNoLine("inACase"),
                "a run that reaches it is a list of one element of that case");
    }

    @Test
    void aListHeldToTwoElementsLeavesEachElementEveryValue() {
        assertEquals(RELATES_TWO_VALUES, whyNoLine("ofSeveral"),
                "two elements may be one value, and the count says no more of them");
    }

    @Test
    void aRuleKeepingTheElementsApartIsStillAskedOfThem() {
        assertEquals(List.of(), whyNoLine("keptApart"),
                "the owners differ, so an owner is not every value of an element, and the"
                        + " comparison is not said to relate two values");
    }

    /** The reasons for which a rule of {@code behavior} came to no line, one for each place. */
    private static List<BlockReason.RuleWithoutLineReason> whyNoLine(String behavior) {
        Compilation compilation = Compilation.ofSource(DECLARED, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        PartitionEvidence evidence = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value().get(behavior);
        assertNotNull(evidence, "the model under test compiles");
        return evidence.rulesWithoutALine().stream().map(RuleWithoutALine::why).toList();
    }
}
