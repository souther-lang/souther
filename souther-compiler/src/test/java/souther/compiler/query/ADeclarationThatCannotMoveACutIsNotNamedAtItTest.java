package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.PointRole;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A declaration is named beside a cut only where its clause could move where the cut falls.
 *
 * <p>Which is what {@code LocalInspection}'s {@code moved} asks, and it is a rule about what a cut
 * is owed to rather than a stand-in for one. The names come from what the value the position sits in
 * projects onto it; the cut is drawn where the position's own type stops, taken in to that
 * projection. So where the type already stops it there, the projection can move as far as it likes
 * and the cut stays put.
 *
 * <p><b>And the difference is which declaration owes the row, not how many are listed.</b> A line a
 * declaration took in is that declaration's to answer for and no longer the type's
 * ({@code AuthoredLine.obligationOwners}), so writing the narrowing where nothing was narrowed does
 * not add a name — it moves the row from the author who can move the line to one who cannot.
 */
class ADeclarationThatCannotMoveACutIsNotNamedAtItTest {

    /**
     * {@code Held} holds where {@code Cap} stops, and moves it nowhere.
     *
     * <p>{@code c.value <= l.value} is the whole of what the record says about {@code c} — take the
     * clause away and the record says nothing about it — so the reading of {@code Held} answers that
     * {@code Held} is holding the end it arrived at. That end is the same fifty {@code Cap}'s own
     * clause stops at, and the cut is where the two meet.
     */
    private static final String AT_THE_SAME_VALUE = """
            module example.same

            data Cap = Int
                invariant capped = value <= 50

            data Lim = Int
                invariant capped = value <= 50

            data Held = { c: Cap, l: Lim }
                invariant tight = c.value <= l.value

            behavior take : (h: Held) -> Int
            let take (h) = 1

            example take
                | "x" : (Held { c = Cap(1), l = Lim(2) }) -> 1
            """;

    /** The same record with {@code Lim} stopping lower, so the cut moves and the record moved it. */
    private static final String AT_A_LOWER_VALUE = """
            module example.lower

            data Cap = Int
                invariant capped = value <= 50

            data Lim = Int
                invariant capped = value <= 30

            data Held = { c: Cap, l: Lim }
                invariant tight = c.value <= l.value

            behavior take : (h: Held) -> Int
            let take (h) = 1

            example take
                | "x" : (Held { c = Cap(1), l = Lim(2) }) -> 1
            """;

    /**
     * Where the record took the end in, the row at the line is the record's.
     *
     * <p>Thirty is not a value {@code Cap} says anything about. A row there shows what {@code Held}
     * leaves its field, and {@code Held} is who can move it.
     */
    @Test
    void aDeclarationThatMovedTheCutOwesTheRowAtIt() {
        assertEquals("Held", ownersAtTheLine(AT_A_LOWER_VALUE, "example.lower", "value = 30"),
                "the record pulled the end down to thirty, so the line there is the record's");
    }

    /**
     * And where it did not, the row stays the type's.
     *
     * <p>The reading still answers that {@code Held} is holding fifty — it is, and its clause is why
     * the record leaves the field nothing above it. It is not why the line is at fifty. Written down
     * here, the row at {@code Cap}'s own ceiling would be filed against a declaration that can
     * rewrite its clause without the line moving at all.
     */
    @Test
    void aDeclarationThatCouldNotMoveTheCutDoesNotOweTheRowAtIt() {
        assertEquals("Cap", ownersAtTheLine(AT_THE_SAME_VALUE, "example.same", "value = 50"),
                "the type stops the position at fifty on its own, so the line there is the type's");
    }

    /** Who a report says owes the row at one line. */
    private static String ownersAtTheLine(String source, String module, String said) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Adequacy.DeclaredBoundaries account =
                compilation.db().ask(new Adequacy.DeclaredBorders(module)).value();
        assertNotNull(account, "the model under test compiles");
        List<Adequacy.DeclaredDebt> debts = account.owed();
        return debts.stream()
                .filter(each -> each.debt().role() == PointRole.ON
                        && each.said().equals(said))
                .map(each -> each.subject().named())
                .findFirst()
                .orElseThrow(() -> new AssertionError("no ON debt asking " + said + ": "
                        + debts.stream()
                                .map(each -> each.debt().role() + " " + each.said()
                                        + " -> " + each.subject().named())
                                .toList()));
    }
}
