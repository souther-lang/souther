package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.EndSide;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.math.BigDecimal;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

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

        assertEquals(List.of(A), holding(tight.meet(loose), EndSide.UPPER),
                "3 is where it stops, and A is what says 3");
        assertEquals(List.of(A), holding(loose.meet(tight), EndSide.UPPER),
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
        assertEquals(List.of(A, B),
                holding(upper(3, true, A).meet(upper(3, true, B)), EndSide.UPPER),
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
        assertEquals(List.of(B), holding(admits.meet(refuses), EndSide.UPPER),
                "and only the clause that takes 3 away is holding it");
    }

    /** Each side is its own question: one declaration can hold a floor while another holds a
     *  ceiling. */
    @Test
    void theTwoEndsAreHeldSeparately() {
        NarrowedBounds floor = NarrowedBounds.of(
                new NumericDomain.Bounds(endAt(0, true), null), List.of(A), List.of());
        NarrowedBounds ceiling = upper(10, true, B);

        NarrowedBounds met = floor.meet(ceiling);
        assertEquals(List.of(A), holding(met, EndSide.LOWER), "A holds the floor");
        assertEquals(List.of(B), holding(met, EndSide.UPPER), "and B the ceiling");
    }

    /** An end nobody stops is nobody's, and two readings with no end on a side have not agreed on
     *  one. */
    @Test
    void anEndThatIsNotThereIsHeldByNobody() {
        NarrowedBounds met = upper(3, true, A).meet(NarrowedBounds.NOTHING);

        assertEquals(List.of(), holding(met, EndSide.LOWER), "nothing stops it from below");
        assertEquals(List.of(A), holding(met, EndSide.UPPER), "and the one end there is stands");
        assertEquals(List.of(),
                holding(NarrowedBounds.NOTHING.meet(NarrowedBounds.NOTHING), EndSide.UPPER),
                "two readings that stop it nowhere have not met at an end");
    }

    /** A name against an end that is not there cannot be written down at all. */
    @Test
    void namingAnEndThatIsNotThereIsRefused() {
        assertThrows(IllegalArgumentException.class,
                () -> NarrowedBounds.of(new NumericDomain.Bounds(null, endAt(3, true)),
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
                holding(upper(3, true, B, A).meet(upper(3, true, A)), EndSide.UPPER),
                "in the declarations' own order, and each once");
    }

    /**
     * One place written two ways is one end, and both readings are holding it.
     *
     * <p>What a rule wrote is what a report writes back, so a reading keeps the spelling it was
     * handed and two readings of one end can hold two of them. Told apart by what they hold rather
     * than by where they stop, whichever spelling the meet happened to keep would decide which
     * declaration is named — and the answer would turn on the order the two were met in.
     */
    @Test
    void onePlaceWrittenTwoWaysIsOneEnd() {
        NarrowedBounds plain = upper(endAt("3", true), A);
        NarrowedBounds padded = upper(endAt("3.00", true), B);

        assertEquals(List.of(A, B), holding(plain.meet(padded), EndSide.UPPER),
                "one end, spelled twice, held by both");
        assertEquals(List.of(A, B), holding(padded.meet(plain), EndSide.UPPER),
                "and the spelling the meet kept decides nothing");
    }

    /** Meeting a reading with itself leaves it as it was. */
    @Test
    void meetingAReadingWithItselfChangesNothing() {
        for (NarrowedBounds each : readings()) {
            assertSameAnswer(each, each.meet(each), () -> "met with itself, " + each);
        }
    }

    /** Which two readings are met in does not decide what they come to. */
    @Test
    void theOrderOfTwoReadingsDoesNotDecideTheAnswer() {
        for (NarrowedBounds left : readings()) {
            for (NarrowedBounds right : readings()) {
                assertSameAnswer(left.meet(right), right.meet(left),
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
                    assertSameAnswer(left.meet(mid).meet(right), left.meet(mid.meet(right)),
                            () -> left + ", " + mid + ", " + right);
                }
            }
        }
    }

    /**
     * The same answer: the same ends, held by the same declarations.
     *
     * <p>Not the same value. A meet keeps one of the two ends it was handed and each is written as
     * whoever wrote it wrote it, so two answers that stop a coordinate at one place can hold two
     * spellings of it — which is a fact about the rules that were read and not about where the
     * coordinate stops. Held to a derived equality, these laws would be statements about which
     * spelling survives.
     */
    private static void assertSameAnswer(NarrowedBounds left, NarrowedBounds right,
                                         java.util.function.Supplier<String> what) {
        for (EndSide side : EndSide.values()) {
            assertTrue(sameEnd(endOf(left, side), endOf(right, side)),
                    () -> side + " end: " + what.get());
            assertEquals(holding(left, side), holding(right, side),
                    () -> "holding the " + side + " end: " + what.get());
        }
    }

    private static boolean sameEnd(Endpoint left, Endpoint right) {
        return left == null ? right == null : left.sameAs(right);
    }

    private static Endpoint endOf(NarrowedBounds narrowed, EndSide side) {
        return side.at(narrowed.bounds());
    }

    /**
     * Who is holding the end this reading leaves on one side.
     *
     * <p>Asked with that end, because that is the only way to ask. What a reading holds is about the
     * number it arrived at, so a caller wanting the names says which number it means — and here the
     * caller means this reading's own, which is what the laws below are about.
     */
    private static List<TypeSymbol.AtModule> holding(NarrowedBounds narrowed, EndSide side) {
        return narrowed.matching(side, endOf(narrowed, side))
                .map(MatchedEndAttribution::names).orElseGet(List::of);
    }

    /**
     * Ends at two places, at one place both ways, and at one place spelled two ways.
     *
     * <p>The last of those is here because the laws cannot fail without it. Every end written one
     * way is an end the comparison under test and the assertion agree about, whatever the comparison
     * is — so a set built from a single spelling holds for a reading of {@code equals} as readily as
     * for a reading of the order, and says nothing about which of the two this is.
     */
    private static List<NarrowedBounds> readings() {
        return List.of(NarrowedBounds.NOTHING,
                upper(endAt("3", true), A), upper(endAt("3", true), B),
                upper(endAt("3", true), A, B),
                upper(endAt("3.00", true), B), upper(endAt("3.00", true), C),
                upper(endAt("3", false), A), upper(endAt("3.00", false), C),
                upper(endAt("10", true), A), upper(endAt("10", true), B),
                NarrowedBounds.of(new NumericDomain.Bounds(null, endAt("3", true)),
                        List.of(), List.of()),
                NarrowedBounds.of(new NumericDomain.Bounds(endAt("0", true), endAt("10", true)),
                        List.of(C), List.of(A)));
    }

    private static NarrowedBounds upper(Endpoint at, TypeSymbol.AtModule... by) {
        return NarrowedBounds.of(new NumericDomain.Bounds(null, at), List.of(), List.of(by));
    }

    private static NarrowedBounds upper(long at, boolean inclusive, TypeSymbol.AtModule... by) {
        return upper(endAt(String.valueOf(at), inclusive), by);
    }

    /** An end written as {@code spelled}, so that two spellings of one place can be told apart here
     *  and not by the algebra. */
    private static Endpoint endAt(String spelled, boolean inclusive) {
        return new Endpoint(new Count(new BigDecimal(spelled)), inclusive);
    }

    private static Endpoint endAt(long at, boolean inclusive) {
        return endAt(String.valueOf(at), inclusive);
    }

    private static TypeSymbol.AtModule named(String name) {
        return TypeSymbols.declared(new TypeKey("probe", name));
    }
}
