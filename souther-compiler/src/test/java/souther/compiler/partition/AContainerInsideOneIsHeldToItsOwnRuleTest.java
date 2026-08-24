package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * How many a container holds is read off its own type, wherever the container stands.
 *
 * <p>A rule counting a collection is written on the type of the collection as readily as on a record
 * holding one as a field. Read only as a field of the parameter's own type, it was found for
 * {@code order.items} and for nothing else: a collection that is a type of its own, and one standing
 * inside another collection, have rules no such name reaches. Both the floor and the cap went blind
 * at the same positions, so the two are stated together here.
 *
 * <p>What each of them costs is different, which is why neither stands in for the other. Missing the
 * floor, the search offers a collection the model refuses and reports the refusal as every value
 * having been tried. Missing the cap, it goes on offering rows for a position nothing can ever stand
 * at, and says the same thing about them -- which reads as a failure of the search over a model that
 * left no room.
 */
class AContainerInsideOneIsHeldToItsOwnRuleTest {

    private static final String MODULE = "example.rows";

    private static final String MODEL = """
            module example.rows

            data Count = Int
            data Inner = List<Int>
                invariant HOW = List.length(value) RULE

            behavior deep : (rows: List<Inner>) -> Count
                constructs Count
            let deep (rows) =
                Count(List.length(
                    List.filter(r -> List.length(List.filter(n -> n >= 5, r.value)) >= 1, rows)))

            example deep
                | "one" : ([ Inner(HELD) ]) -> Count(0)
            """;

    private static Adequacy.Filling offered(String how, String rule, String held) {
        Compilation compilation = Compilation.ofSource(
                MODEL.replace("HOW", how).replace("RULE", rule).replace("HELD", held), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, Adequacy.Filling> generated =
                Adequacy.generatedOf(compilation.db(), MODULE);
        assertNotNull(generated, "the model under test compiles");
        return generated.get("deep");
    }

    /** A floor written on the inner collection's own type is met by what is offered for it. */
    @Test
    void aRowOfferedForAnInnerCollectionMeetsThatCollectionsFloor() {
        assertEquals(List.of("[Inner([5, 5])]"),
                offered("twice", ">= 2", "[ 1, 2 ]").composed().rows().stream()
                        .map(row -> row.inputs().get(0).text()).toList(),
                "the inner list holds the two its own rule asks for");
    }

    /** And a cap of none there leaves nothing to offer a row for, rather than a search that failed. */
    @Test
    void aPositionInsideACollectionCappedAtNoneIsOfferedNothing() {
        Adequacy.Filling filling = offered("none", "<= 0", "[ ]");

        assertEquals(List.of(), filling.composed().rows().stream()
                        .map(row -> row.inputs().get(0).text()).toList(),
                "no row is composed for a position nothing can stand at");
        assertEquals(List.of(), filling.composed().unresolved().stream()
                        .map(Object::toString).toList(),
                "and no combination of it is left owed a row, whichever way the search fell short");
    }
}
