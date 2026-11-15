package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.values.TextExtents;
import souther.compiler.values.Value;
import souther.compiler.values.ValuesWithin;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a {@code String} stops is no distinction a model made, so a relation between strings
 * whose whole no length rule bounds leaves no value in no class for being long. Every value of a
 * place is on the true side, the false side, open for an operation, or of a length no run gets to
 * the relation at, at every length; and a value of a kind the whole holds at every length is on
 * the true side however long it is, past the longest {@code String} less what stands round it as
 * well.
 */
class NoValueOfAStringRelationIsLeftInNoClassByWhereAStringStopsTest {

    /** A domain is the piece after the {@code @} of an address no length rule bounds. */
    private static final String A_PIECE = """
            module probe.piece

            data Yes
            data No
            data Email = String
                invariant String.matches("[a-z]+@[a-z]+", value)

            behavior f : (email: Email, domain: String) -> Yes | No
            let f (email, domain) =
                match List.get(1, String.split("@", email.value)) with
                    | Some d -> if d == domain then Yes else No
                    | None -> No
            """;

    /** A string looked for inside a wrapped one no length rule bounds. */
    private static final String A_CONTAINMENT = """
            module probe.inside

            data Yes
            data No
            data Wrapped = String
                invariant String.matches("<[a-z]*>", value)

            behavior f : (p: Wrapped, s: String) -> Yes | No
            let f (p, s) = if String.contains(s, p.value) then Yes else No
            """;

    @Test
    void aPieceOfAnUnboundedWholeLeavesNoDomainInNoClass() {
        SetStatement domain = statementAt(A_PIECE, "domain");

        assertEveryLengthIsOnASide(domain, "example");
        assertEveryLengthIsOnASide(domain, "EXAMPLE");
        assertOnTheTrueSideAtEveryLength(domain, "example");
    }

    @Test
    void aContainmentInAnUnboundedWholeLeavesNoStringInNoClass() {
        SetStatement inside = statementAt(A_CONTAINMENT, "s");

        assertEveryLengthIsOnASide(inside, "abc");
        assertEveryLengthIsOnASide(inside, "<abc>");
        assertEveryLengthIsOnASide(inside, "ABC");
        assertOnTheTrueSideAtEveryLength(inside, "abc");
    }

    /**
     * No region of a rule's statement ends, or begins, within a few code points of the longest a
     * {@code String} holds: the strings a value of the other side cannot be the partner of for
     * being too long are drawn on no side of their own, since a class only a string of that length
     * could fill is one no row is in. A length cuts a region where a model declared it, and these
     * models declare none.
     */
    @Test
    void noRegionIsCutWhereAStringStops() {
        long near = TextExtents.LONGEST_STRING - 1_000;
        for (SetStatement statement : List.of(statementAt(A_PIECE, "domain"),
                statementAt(A_CONTAINMENT, "s"))) {
            for (List<ValuesWithin> side : List.of(statement.whenTrue().pieces(),
                    statement.whenFalse().pieces(), statement.notShown(),
                    statement.notReached())) {
                for (ValuesWithin each : side) {
                    assertTrue(each.shortest() < near
                            && (each.longest() == null || each.longest() < near),
                            () -> "a region is cut at the longest a String holds: " + each);
                }
            }
        }
    }

    /**
     * The regions of {@code statement} whose set holds {@code sample}, on whichever side, together
     * hold every length: the strings of its kind are each on some side however long they are.
     */
    private static void assertEveryLengthIsOnASide(SetStatement statement, String sample) {
        Value value = new Value.Text(sample);
        List<ValuesWithin> holding = new ArrayList<>();
        for (List<ValuesWithin> side : List.of(statement.whenTrue().pieces(),
                statement.whenFalse().pieces(), statement.notShown(), statement.notReached())) {
            side.stream().filter(each -> each.values().has(value)).forEach(holding::add);
        }
        holding.sort(Comparator.comparingLong(ValuesWithin::shortest));
        long next = 0;
        for (ValuesWithin each : holding) {
            assertTrue(each.shortest() <= next, () -> sample + ": no side holds a string of "
                    + "its kind of " + each.shortest() + " code points or fewer: " + statement);
            if (each.longest() == null) {
                return;
            }
            next = Math.max(next, each.longest() + 1);
        }
        throw new AssertionError(sample + ": no side holds a string of its kind of " + next
                + " code points or more: " + statement);
    }

    /** {@code sample}'s kind is on the true side from its own length up, with no greatest. */
    private static void assertOnTheTrueSideAtEveryLength(SetStatement statement, String sample) {
        Value value = new Value.Text(sample);
        assertTrue(statement.whenTrue().pieces().stream().anyMatch(each ->
                        each.values().has(value) && each.shortest() <= sample.length()
                                && each.longest() == null),
                () -> sample + " is on the true side however long: " + statement);
        assertFalse(statement.notShown().stream().anyMatch(each -> each.values().has(value)),
                () -> sample + " is open at no length: " + statement);
    }

    private static SetStatement statementAt(String source, String place) {
        return SetStatementAt.of(source, place);
    }
}
