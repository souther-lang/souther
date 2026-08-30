package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.PointRole;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A declaration is named beside an end only where the clauses relating the position to something
 * else left it anywhere other than where it stops without them.
 *
 * <p>Writing a relation about a position is not deciding where it stops. A clause reaching a value
 * the position's own type has already stopped it at moves nothing, and a name written down there
 * does not stand beside the type's: a line a declaration took in is that declaration's to answer for
 * and no longer the type's ({@code AuthoredLine.obligationOwners}), so the row moves to an author
 * who can rewrite their clause with the run staying exactly where it is.
 *
 * <p>Read here rather than at a cut. {@code LocalInspection}'s {@code moved} asks whether a cut owes
 * anything to a name that is about the end it stands at, which is a question a run between two ends
 * does not have to ask — so what the names themselves say shows up here as it was worked out.
 */
class ANameBesideAnEndIsOwedToTheDifferenceItMadeTest {

    /**
     * {@code Held} holds both ends it arrived at and moved one of them.
     *
     * <p>{@code c} stops at twenty because {@code Cap} says so, and {@code tight} taken away leaves
     * it there. {@code l} has no floor of its own, and the same clause is the whole of why it has
     * one — so one clause is a reason to name {@code Held} at one of the two and no reason at all at
     * the other.
     */
    private static final String ONE_CLAUSE_MOVING_ONE_END = """
            module example.tight

            data Cap = Int
                invariant floor = value >= 0
                invariant capped = value <= 20

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
     * Two declarations reaching one end, neither of them missed on its own.
     *
     * <p>{@code Inner} stops {@code c} at thirty through its own {@code Lim}, and {@code Outer} says
     * the same of the same position through another. Take either away and the other still says it,
     * so neither is holding the end by itself and both of them say what the edge says.
     */
    private static final String TWO_SAYING_THE_SAME = """
            module example.both

            data Cap = Int
                invariant floor = value >= 0
                invariant capped = value <= 50

            data Lim = Int
                invariant floor = value >= 0
                invariant capped = value <= 30

            data Inner = { c: Cap, l: Lim }
                invariant tight = c.value <= l.value

            data Outer = { i: Inner, m: Lim }
                invariant also = i.c.value <= m.value

            behavior take : (o: Outer) -> Int
            let take (o) = 1

            example take
                | "x" : (Outer { i = Inner { c = Cap(1), l = Lim(2) }, m = Lim(2) }) -> 1
            """;

    /** Where the record moved the end, the run beside it is the record's to answer for as well. */
    @Test
    void aDeclarationThatMovedAnEndIsNamedBesideIt() {
        // In the declarations' own order and not the order the readings were met in: who owes a
        // point is a set, and which of them a walk reached first is no part of it.
        assertEquals("Held or Lim",
                ownersOf(ONE_CLAUSE_MOVING_ONE_END, "example.tight", PointRole.IN,
                        "value in 0 <= value < 50"),
                "nothing but the record's clause gives this field a floor, so the record holds it");
    }

    /** And where it moved none, the run stays the type's alone. */
    @Test
    void aDeclarationThatMovedNoEndIsNotNamedBesideIt() {
        assertEquals("Cap",
                ownersOf(ONE_CLAUSE_MOVING_ONE_END, "example.tight", PointRole.IN,
                        "value in 0 < value <= 20"),
                "the type stops the field at twenty on its own, so the run there is the type's");
    }

    /**
     * Neither of two reaching one end is the answer over the other, and both are named.
     *
     * <p>Naming nobody here would be as wrong as naming everybody where nobody moved it: the end is
     * thirty because these two say so, and an author of either is looking at a clause they can move
     * it with.
     */
    @Test
    void twoDeclarationsSayingWhatTheEdgeSaysAreBothNamed() {
        assertEquals("Inner or Outer",
                ownersOf(TWO_SAYING_THE_SAME, "example.both", PointRole.ON, "value = 30"),
                "each of them says the edge and neither is missed on its own");
    }

    /** Who a report says owes one row of a module's account. */
    private static String ownersOf(String source, String module, PointRole role, String said) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Adequacy.DeclaredBoundaries account =
                compilation.db().ask(new Adequacy.DeclaredBorders(module)).value();
        assertNotNull(account, "the model under test compiles");
        List<Adequacy.DeclaredDebt> debts = account.owed();
        return debts.stream()
                .filter(each -> each.debt().role() == role && each.said().equals(said))
                .map(each -> each.subject().named())
                .findFirst()
                .orElseThrow(() -> new AssertionError("no " + role + " debt asking " + said + ": "
                        + debts.stream()
                                .map(each -> each.debt().role() + " " + each.said()
                                        + " -> " + each.subject().named())
                                .toList()));
    }
}
