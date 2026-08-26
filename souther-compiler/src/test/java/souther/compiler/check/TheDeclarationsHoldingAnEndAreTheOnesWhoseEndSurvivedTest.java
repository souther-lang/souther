package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Two readings of one coordinate meet, and the declarations follow the end that survived.
 *
 * <p>Which declaration holds an end is worked out against that end, by taking the declaration's
 * clauses away and seeing whether the number moves. So it is true of that number and of no other,
 * and two readings of one position — a case's own and the value the case was narrowed out of — are
 * two such answers about two numbers. Kept as one answer per side and put back together afterwards,
 * the reading whose end lies further out kept its names against an end the position does not stop
 * at.
 *
 * <p>The laws are here because the meet is one operation over one value. What they do not state is
 * which names survive, which is the whole of what went wrong: a union is commutative, associative
 * and idempotent too. So the cases stand beside them.
 */
class TheDeclarationsHoldingAnEndAreTheOnesWhoseEndSurvivedTest {

    private static final TypeSymbol.AtModule A = named("A");
    private static final TypeSymbol.AtModule B = named("B");
    private static final TypeSymbol.AtModule C = named("C");

    /**
     * The tighter end is the one the position stops at, and only its declarations are holding it.
     *
     * <p>The other reading's clause moved an end that is not here. Named all the same, an author
     * asking which declaration to go and look at is sent to a clause that admits every value this
     * position stops short of.
     */
    @Test
    void onlyTheReadingWhoseEndSurvivedIsHoldingIt() {
        NarrowedBounds tight = upper(3, true, A);
        NarrowedBounds loose = upper(10, true, B);

        assertEquals(List.of(A), tight.meet(loose).maxBy(),
                "3 is where it stops, and A is what says 3");
        assertEquals(List.of(A), loose.meet(tight).maxBy(),
                "whichever way round the two are met");
        assertEquals(endAt(3, true), tight.meet(loose).bounds().max(),
                "and the end is the one that survived");
    }

    /**
     * Both, where both readings arrive at the same end.
     *
     * <p>Neither settled it alone and each is as much the answer as the other. Which is not the same
     * as either being necessary: take one away and the other still says 3, so this is what holds the
     * end and not what the end depends on.
     */
    @Test
    void bothAreHoldingAnEndTheyBothArriveAt() {
        assertEquals(List.of(A, B), upper(3, true, A).meet(upper(3, true, B)).maxBy(),
                "one end, arrived at twice");
    }

    /**
     * The same place is not the same end.
     *
     * <p>{@code (3, inclusive)} and {@code (3, exclusive)} stop at one number and leave different
     * values, and a conjunction leaves the second. Read as one because the number is the same, a
     * position that stops short of 3 would be reported as held by a clause that admits it.
     */
    @Test
    void aPlaceSharedByTwoEndsIsNotOneEnd() {
        NarrowedBounds admits = upper(3, true, A);
        NarrowedBounds refuses = upper(3, false, B);

        assertEquals(endAt(3, false), admits.meet(refuses).bounds().max(),
                "what both leave stops short of 3");
        assertEquals(List.of(B), admits.meet(refuses).maxBy(),
                "and only the clause that takes 3 away is holding it");
    }

    /** Each side is its own question: one declaration can hold a floor while another holds a
     *  ceiling. */
    @Test
    void thetwoEndsAreHeldSeparately() {
        NarrowedBounds floor = new NarrowedBounds(
                new NumericDomain.Bounds(endAt(0, true), null), List.of(A), List.of());
        NarrowedBounds ceiling = upper(10, true, B);

        NarrowedBounds met = floor.meet(ceiling);
        assertEquals(List.of(A), met.minBy(), "A holds the floor");
        assertEquals(List.of(B), met.maxBy(), "and B the ceiling");
    }

    /** An end nobody stops is nobody's, and two readings with no end on a side have not agreed on
     *  one. */
    @Test
    void anEndThatIsNotThereIsHeldByNobody() {
        NarrowedBounds met = upper(3, true, A).meet(NarrowedBounds.NOTHING);

        assertEquals(List.of(), met.minBy(), "nothing stops it from below");
        assertEquals(List.of(A), met.maxBy(), "and the one end there is stands");
        assertEquals(List.of(), NarrowedBounds.NOTHING.meet(NarrowedBounds.NOTHING).maxBy(),
                "two readings that stop it nowhere have not met at an end");
    }

    /** A name against an end that is not there cannot be written down at all. */
    @Test
    void namingAnEndThatIsNotThereIsRefused() {
        assertThrows(IllegalArgumentException.class,
                () -> new NarrowedBounds(new NumericDomain.Bounds(null, endAt(3, true)),
                        List.of(A), List.of()),
                "nothing stops it from below for A to be holding");
    }

    /**
     * The names are in one order and each of them once.
     *
     * <p>Several of them are one answer, and an order read off the walk that met them would make two
     * readings of one edge into two answers. Which is also what leaves the meet idempotent: met with
     * itself, a reading that holds an end twice holds it once.
     */
    @Test
    void theNamesAreCanonical() {
        assertEquals(List.of(A, B),
                upper(3, true, B, A).meet(upper(3, true, A)).maxBy(),
                "in the declarations' own order, and each once");
    }

    /** Meeting a reading with itself leaves it as it was. */
    @Test
    void meetingAReadingWithItselfChangesNothing() {
        for (NarrowedBounds each : List.of(upper(3, true, A), upper(3, true, A, B),
                NarrowedBounds.NOTHING)) {
            assertEquals(each, each.meet(each), "met with itself, " + each);
        }
    }

    /** Which two readings are met in does not decide what they come to. */
    @Test
    void theOrderOfTwoReadingsDoesNotDecideTheAnswer() {
        for (NarrowedBounds left : readings()) {
            for (NarrowedBounds right : readings()) {
                assertEquals(left.meet(right), right.meet(left),
                        () -> left + " met with " + right);
            }
        }
    }

    /** Nor which of three is met first. */
    @Test
    void theGroupingOfThreeReadingsDoesNotDecideTheAnswer() {
        for (NarrowedBounds left : readings()) {
            for (NarrowedBounds mid : readings()) {
                for (NarrowedBounds right : readings()) {
                    assertEquals(left.meet(mid).meet(right), left.meet(mid.meet(right)),
                            () -> left + ", " + mid + ", " + right);
                }
            }
        }
    }

    /** Ends at two places and at one place both ways, held by one declaration, by another, and by
     *  none. */
    private static List<NarrowedBounds> readings() {
        return List.of(NarrowedBounds.NOTHING,
                upper(3, true, A), upper(3, true, B), upper(3, true, A, B),
                upper(3, false, A), upper(3, false, C),
                upper(10, true, A), upper(10, true, B),
                NarrowedBounds.held(new NumericDomain.Bounds(null, endAt(3, true))),
                new NarrowedBounds(new NumericDomain.Bounds(endAt(0, true), endAt(10, true)),
                        List.of(C), List.of(A)));
    }

    private static NarrowedBounds upper(long at, boolean inclusive, TypeSymbol.AtModule... by) {
        return new NarrowedBounds(new NumericDomain.Bounds(null, endAt(at, inclusive)),
                List.of(), List.of(by));
    }

    private static Endpoint endAt(long at, boolean inclusive) {
        return new Endpoint(Count.of(at), inclusive);
    }

    private static TypeSymbol.AtModule named(String name) {
        return TypeSymbols.declared(new TypeKey("probe", name));
    }
}
