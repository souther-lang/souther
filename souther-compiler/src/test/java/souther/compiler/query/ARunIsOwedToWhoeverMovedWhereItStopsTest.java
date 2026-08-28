package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.BorderObligationPoint;
import souther.compiler.partition.FarEnd;
import souther.compiler.partition.PointRole;
import souther.compiler.partition.RegionBasis;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A run stopping where a declaration took the position in is owed to that declaration too.
 *
 * <p>Which of two things this is about is the whole point. Where the run stops is what every rule
 * about the position leaves together and is no one rule's, so the point is the same point however
 * the position came to stop there — that is its identity, and the declaration that moved the end is
 * no part of it. Who can move it is another question, and the answer to that is who a report tells
 * about a row nobody has written.
 *
 * <p>Read off the identity instead — the lines that happen to be inside it — the run came back owed
 * to the line it lies against and to nobody else, and the declaration that put the end there was
 * told nothing about a row it could be asked for.
 */
class ARunIsOwedToWhoeverMovedWhereItStopsTest {

    /** {@code Held} relates one of its fields to the other, which is what moves where {@code Cap}
     *  stops. */
    private static final String NARROWED = """
            module example.narrow

            data Cap = Int
                invariant floor = value >= 0

            data Lim = Int
                invariant capped = value <= 50

            data Held = { c: Cap, l: Lim }
                invariant tight = c.value <= l.value

            behavior take : (h: Held) -> Int
            let take (h) = 1

            example take
                | "x" : (Held { c = Cap(1), l = Lim(2) }) -> 1
            """;

    /**
     * The run above {@code Cap}'s floor stops where {@code Held} takes the position in, and both are
     * told about it.
     *
     * <p>{@code Cap} wrote the line the run lies against and {@code Held} put the end it stops at,
     * and either of them moving theirs moves the row somebody has to write. The point on the line is
     * {@code Cap}'s alone, which is what says the two questions are answered apart rather than one
     * being read off the other.
     */
    @Test
    void aDeclarationThatTookThePositionInIsToldAboutTheRunItStops() {
        assertEquals("Cap", ownersOf(PointRole.ON, "value = 0"),
                "the row at the line is a fact about the type that drew it");
        assertEquals("Cap or Held", ownersOf(PointRole.IN, "value in 0 < value <= 50"),
                "and the run beside it stops where the record put the end, so both are told");
    }

    /** And what moved the end is no part of which point it is. */
    @Test
    void whoMovedTheEndIsNoPartOfWhichPointItIs() {
        BorderObligationPoint point = pointOf(PointRole.IN, "value in 0 < value <= 50");

        RegionBasis basis = ((BorderObligationPoint.InRegion) point).region();
        assertInstanceOf(FarEnd.AtTheDomain.class, ((RegionBasis.Beside) basis).farEnd(),
                "the run stops where every rule about the position leaves it, which is nobody's"
                        + " line — so the point names the place and not the record");
    }

    /** What a report tells about the debt at that point, as it names the declarations. */
    private static String ownersOf(PointRole role, String said) {
        return debtOf(role, said).subject().named();
    }

    private static BorderObligationPoint pointOf(PointRole role, String said) {
        return debtOf(role, said).debt().point();
    }

    private static Adequacy.DeclaredDebt debtOf(PointRole role, String said) {
        Compilation compilation = Compilation.ofSource(NARROWED, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Adequacy.DeclaredBoundaries account =
                compilation.db().ask(new Adequacy.DeclaredBorders("example.narrow")).value();
        assertNotNull(account, "the model under test compiles");
        List<Adequacy.DeclaredDebt> debts = account.owed();
        return debts.stream()
                .filter(each -> each.debt().role() == role && each.said().equals(said))
                .findFirst()
                .orElseThrow(() -> new AssertionError("no " + role + " debt asking " + said + ": "
                        + debts.stream()
                                .map(each -> each.debt().role() + " " + each.said())
                                .toList()));
    }
}
