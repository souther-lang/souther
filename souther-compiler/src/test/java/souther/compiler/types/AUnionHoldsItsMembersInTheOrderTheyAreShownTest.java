package souther.compiler.types;

import org.junit.jupiter.api.Test;

import java.util.Comparator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.SequencedSet;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A union holds its members in the order they are shown, whoever reads them.
 *
 * <p>The contract a renderer rests on, asked of the union and not through anything that renders
 * one. What a reader is shown following the container the members were put in is the defect, and
 * a check that only watches what comes out of {@code Type.show} passes as well when the order is
 * established there as when it is established here — which is the arrangement this replaces,
 * because an order established at one reader is an order the next reader has to establish again.
 *
 * <p>So this is about {@code members()} itself. A walk that takes them in the order it finds them
 * — a renderer written later, a list built out of them, a fold that stops early — is shown one
 * order however the union was built, by having done nothing at all.
 *
 * <p><b>Each claim asked of what owns it.</b> That the members are in one order however they were
 * collected is asked of {@code Type.union}, which is where a plain set becomes a union; that the
 * constructor is what puts them in it is asked of the constructor, because a factory that arranged
 * them on the way would answer the first while leaving the second false.
 */
class AUnionHoldsItsMembersInTheOrderTheyAreShownTest {

    private static final TypeSymbol MINOR = TypeSymbols.declared(new TypeKey("example", "Minor"));
    private static final TypeSymbol ADULT = TypeSymbols.declared(new TypeKey("example", "Adult"));
    private static final TypeSymbol PENSIONER =
            TypeSymbols.declared(new TypeKey("example", "Pensioner"));

    /** Every way of holding the three members that this compiler has anywhere reached for. */
    private static List<Set<TypeSymbol>> everyWayOfHoldingThem() {
        Set<TypeSymbol> written = new LinkedHashSet<>(List.of(ADULT, MINOR, PENSIONER));
        Set<TypeSymbol> theOtherWay = new LinkedHashSet<>(List.of(PENSIONER, MINOR, ADULT));
        Set<TypeSymbol> hashed = new java.util.HashSet<>(List.of(ADULT, MINOR, PENSIONER));
        Set<TypeSymbol> against = new TreeSet<>(Comparator.reverseOrder());
        against.addAll(List.of(ADULT, MINOR, PENSIONER));
        return List.of(written, theOtherWay, hashed, against);
    }

    /**
     * The control. Were every way of holding them to walk alike, a union that simply kept what it
     * was handed would pass the claim below, and what this says would be about the containers
     * rather than about the union.
     */
    @Test
    void theWaysOfHoldingThemDoNotAllIterateAlike() {
        Set<List<TypeSymbol>> walked = new LinkedHashSet<>();
        for (Set<TypeSymbol> each : everyWayOfHoldingThem()) {
            walked.add(List.copyOf(each));
        }

        assertTrue(walked.size() > 1,
                () -> "every way of holding the members walks them alike, so a union keeping what"
                        + " it was handed would pass this as it stands: " + walked);
    }

    /**
     * And the constructor is what puts them in it.
     *
     * <p>Asked of the constructor because that is what owns the claim. Every union below this one
     * is made through {@code Type.union}, which has to make a sequenced set of what it was handed
     * and could arrange the members while it does — and were the arranging to move there, each of
     * them would go on passing while {@code new Type.Union(...)} built a union in whatever order it
     * was given.
     */
    @Test
    void theConstructorIsWhatPutsTheMembersInThatOrder() {
        SequencedSet<TypeSymbol> backwards = new LinkedHashSet<>(List.of(PENSIONER, MINOR, ADULT));

        assertEquals(List.of(ADULT, MINOR, PENSIONER),
                List.copyOf(new Type.Union(backwards).members()),
                "a union built through its constructor holds the members in the order it was"
                        + " handed them");
    }

    /** However it was built, the members come back in one order. */
    @Test
    void theMembersComeBackInOneOrderHoweverTheUnionWasBuilt() {
        for (Set<TypeSymbol> each : everyWayOfHoldingThem()) {
            assertEquals(List.of(ADULT, MINOR, PENSIONER),
                    List.copyOf(((Type.Union) Type.union(each)).members()),
                    "a union handed its members back in the order the container walked them");
        }
    }

    /**
     * And that order is not the caller's to take back.
     *
     * <p>Two ways it would be. A union built over the caller's own set holds what the caller does
     * to it next, and members handed out writable hold what a reader does to them — and a set's
     * encounter order moves when something is taken out and put back, so either is the order
     * established again by somebody who was not deciding it.
     *
     * <p>Built through the constructor and not through {@code Type.union}, because the constructor
     * is where this closes. A factory taking a plain set has to make a sequenced one of it and
     * copies on the way whatever the record does, so a union built that way would answer this
     * while the record itself held what it was handed — and the callers that build one directly
     * would be outside what this says.
     *
     * <p>Of the two, only the second falls on its own: putting the members in the order they are
     * shown is building a set of them, so a union that kept the caller's could not be in that
     * order either, and the first fails where the whole of this does. It is said all the same,
     * because what a reader of this has to know is which of them is the contract and not which of
     * them a mutation separates.
     */
    @Test
    void theOrderIsNotTakenBackAfterwards() {
        SequencedSet<TypeSymbol> caller = new LinkedHashSet<>(List.of(ADULT, MINOR));
        Type.Union union = new Type.Union(caller);

        caller.remove(ADULT);
        caller.add(ADULT);
        assertEquals(List.of(ADULT, MINOR), List.copyOf(union.members()),
                "a union holds the caller's own set, so what the caller does to it next is what a"
                        + " reader is shown");

        assertThrows(UnsupportedOperationException.class, () -> union.members().remove(ADULT),
                "the members are handed out writable, so the order is whatever a reader of them"
                        + " leaves behind");
    }

    /** Two writings are still one value, which is what makes the order this compiler's to decide. */
    @Test
    void everyWayOfHoldingThemIsOneUnion() {
        for (Set<TypeSymbol> each : everyWayOfHoldingThem()) {
            assertEquals(Type.union(everyWayOfHoldingThem().getFirst()), Type.union(each),
                    "a union is its members, and these are the same members");
        }
    }
}
