package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.PartitionEvidence;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * {@code List.flatMap(x -> [f(x)], xs)} answers one element for each element of {@code xs}, which
 * is what {@code List.map(x -> f(x), xs)} answers, so a rule about how many of its elements meet
 * something is read as it is of the map. A closure that writes the one element only under a choice
 * answers fewer than it walked and is not one.
 */
class AFlatMapThatWritesOneElementForEachIsReadAsAMapTest {

    private static final String PIECES = "List.drop(1, String.split(\"@\", email))";

    private static String guarded(String pieces) {
        return """
                module h

                behavior f : (email: String, doms: List<String>) -> Int
                let f (email, doms) = {
                    let ma = List.flatMap(d -> List.filter(a -> a == d, doms), %s)
                    guard List.length(ma) >= 1 else 0
                    1
                }
                """.formatted(pieces);
    }

    private static List<String> unreadAt(String source) {
        return WhereAStringRelationIsLeftOpen.evidenceOf(source, "f").unanswered().stream()
                .filter(each -> !(each.asked() instanceof
                        souther.compiler.inputs.StandingQuestion.RegionUndetermined))
                .map(PartitionEvidence.Unanswered::asked).map(Object::toString).toList();
    }

    @Test
    void aGuardOverTheListsMadeOverAFlatMapOfOneEachIsReadAsOverAMap() {
        String walked = guarded("List.flatMap(p -> [ p ], " + PIECES + ")");

        assertEquals(List.of(), unreadAt(guarded("List.map(p -> p, " + PIECES + ")")));
        assertEquals(List.of(), unreadAt(guarded(PIECES)));
        assertEquals(List.of(), unreadAt(walked));
        assertEquals(WhereAStringRelationIsLeftOpen.leftOpen(guarded(PIECES), "f"),
                WhereAStringRelationIsLeftOpen.leftOpen(walked, "f"));
    }

    /** What is written under a choice is no one for each element, so the list is not read as a
     *  map of its elements, and what is said of it is said as it was. */
    @Test
    void aFlatMapThatWritesTheElementOnlyWhereSomethingHoldsIsNotAMap() {
        List<String> unread = unreadAt(guarded(
                "List.flatMap(p -> if p == \"x\" then [ p ] else [], " + PIECES + ")"));

        assertFalse(unread.isEmpty(), unread::toString);
    }
}
