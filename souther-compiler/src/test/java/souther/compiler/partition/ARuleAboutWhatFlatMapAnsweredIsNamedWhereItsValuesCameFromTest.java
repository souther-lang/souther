package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.BoundOperationFacts;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.types.ValueName;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A rule an author wrote about what {@code List.flatMap} answered is named at the position the
 * values came from, as one about what {@code List.filterMap} answered is.
 *
 * <p>Where a {@code flatMap}'s elements came from is declared without its count, which is neither
 * as many as its source nor no more. The count is what the invariant discharge reads a building
 * for, so the operation is not a building and the discharge states nothing new about it.
 */
class ARuleAboutWhatFlatMapAnsweredIsNamedWhereItsValuesCameFromTest {

    private static final String MODULE = "probe";

    private static final String BARE = """
            module probe

            data Person = { age: Int }
            data Count = Int

            behavior scored : (people: List<Person>) -> Count
                constructs Count
            let scored (people) =
                Count(List.length(List.filter(n -> n >= 18, List.flatMap(p -> [p.age], people))))
            """;

    private static final String COMPUTED = """
            module probe

            data Person = { age: Int }
            data Count = Int

            behavior scored : (people: List<Person>) -> Count
                constructs Count
            let scored (people) =
                Count(List.length(
                    List.filter(n -> n >= 18, List.flatMap(p -> [p.age + 1, p.age + 2], people))))
            """;

    private static PartitionEvidence measured(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        PartitionEvidence scored = compilation.db()
                .ask(new Adequacy.Coverage(MODULE)).value().get("scored");
        assertNotNull(scored, "the model under test compiles");
        return scored;
    }

    private static List<String> namedAsDerived(PartitionEvidence evidence) {
        return evidence.notRead().stream()
                .filter(each -> each.reason()
                        == UndividedPosition.Reason.RULE_ABOUT_A_DERIVED_VALUE)
                .map(PartitionEvidence.NotRead::at).toList();
    }

    @Test
    void theRuleIsNamedAtThePositionItsValuesCameFrom() {
        PartitionEvidence evidence = measured(BARE);

        assertEquals(List.of("people[*]"), namedAsDerived(evidence),
                () -> "said once, where the values came from: " + evidence.notRead());
    }

    /** A value made from a position is not the position's value, however many it is made of. */
    @Test
    void noLineIsDrawnAtAPositionTheValuesWereOnlyMadeFrom() {
        PartitionEvidence evidence = measured(COMPUTED);

        assertEquals(List.of("people[*]"), namedAsDerived(evidence),
                () -> "said once, where the values came from: " + evidence.notRead());
        assertEquals(List.of(), evidence.axes().stream()
                .map(PartitionEvidence.AxisCoverage::path).toList());
    }

    /** Where it came from is answered, and the building the discharge reads is not one. */
    @Test
    void itIsAnsweredWhereTheValuesCameFromAndIsNoBuildingToTheDischarge() {
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();
        ValueName flatMap = ValueName.Stdlib.operation("List", "flatMap");

        assertNotNull(facts.derivesItsElementsFrom(flatMap),
                "where a flatMap's elements came from is answered");
        assertNull(facts.buildsItsResultFrom(flatMap),
                "a flatMap answers any number for each element, which no building states");
        assertFalse(facts.buildsItsResultFrom().contains(flatMap));
    }
}
