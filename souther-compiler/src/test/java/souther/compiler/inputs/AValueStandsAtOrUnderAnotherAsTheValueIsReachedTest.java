package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.Arrays;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * One place stands at or under another ({@link TermPath#standsAtOrUnder}) where its value is the
 * other's or one inside it as the value is reached: the cases each requires holding together, and
 * the steps that go somewhere one within the other. Narrowings that leave some value no case in
 * common are neither inside the other.
 */
class AValueStandsAtOrUnderAnotherAsTheValueIsReachedTest {

    private static final TermPath R = TermPath.of("r");
    private static final TermPath ITEMS = R.then("items");
    private static final TermPath PRESENT = R.refine(Refinement.of(new Case.Presence(true)));
    private static final TermPath ABSENT = R.refine(Refinement.of(new Case.Presence(false)));

    @Test
    void aNameReadAtAValueIsTheNameReadAtTheValueNarrowedToACase() {
        assertTrue(R.then("code").standsAtOrUnder(PRESENT.then("code")));
        assertTrue(PRESENT.then("code").standsAtOrUnder(R.then("code")));
        assertTrue(PRESENT.standsAtOrUnder(R));
        assertTrue(R.standsAtOrUnder(PRESENT));
    }

    @Test
    void whatIsInsideAValueNarrowedToACaseIsUnderTheValue() {
        assertTrue(PRESENT.then("code").standsAtOrUnder(R));
        assertTrue(R.then("code").then("digit").standsAtOrUnder(PRESENT.then("code")));
        assertFalse(R.standsAtOrUnder(PRESENT.then("code")));
        assertFalse(PRESENT.then("code").standsAtOrUnder(R.then("code").then("digit")));
    }

    /** Which case a value is stands around whatever is asked under another case of it. */
    @Test
    void twoCasesOfOneValueAreNeitherUnderTheOther() {
        assertFalse(PRESENT.standsAtOrUnder(ABSENT));
        assertFalse(PRESENT.then("a").standsAtOrUnder(ABSENT));
        assertFalse(ABSENT.standsAtOrUnder(PRESENT.then("a")));
        assertFalse(PRESENT.then("a").standsAtOrUnder(ABSENT.then("b")));
    }

    @Test
    void placesApartAreNeitherUnderTheOther() {
        assertFalse(R.then("a").standsAtOrUnder(R.then("b")));
        assertFalse(PRESENT.then("a").standsAtOrUnder(R.then("b")));
        assertFalse(ITEMS.element().standsAtOrUnder(R.then("total")));
        assertFalse(R.standsAtOrUnder(TermPath.of("s")));
    }

    /** Two cases of one value bear on each other ({@link TermPath#bearsOn}), as each excludes the
     *  other, and neither stands at, under or around the other. */
    @Test
    void twoCasesOfOneValueBearOnEachOtherAndStandApart() {
        assertTrue(PRESENT.then("a").bearsOn(ABSENT.then("a")));
        assertFalse(PRESENT.then("a").standsAtUnderOrAround(ABSENT.then("a")));
        assertFalse(PRESENT.standsAtUnderOrAround(ABSENT.then("b")));
        assertTrue(PRESENT.then("a").standsAtUnderOrAround(R));
        assertTrue(R.then("a").standsAtUnderOrAround(PRESENT.then("a").then("b")));
    }

    private static final TypeSymbol HOSPITAL = TypeSymbols.declared(new TypeKey("probe", "Hospital"));
    private static final TypeSymbol STATION = TypeSymbols.declared(new TypeKey("probe", "Station"));
    private static final TypeSymbol DEPOT = TypeSymbols.declared(new TypeKey("probe", "Depot"));

    private static CasesLeft casesOf(TypeSymbol... leaves) {
        return CasesLeft.ofEach(Arrays.stream(leaves)
                .map(leaf -> Refinement.of(new Case.SumCase(leaf, true))).toList());
    }

    private static final TermPath KIND = TermPath.of("x");
    private static final TermPath EITHER = KIND.refine(casesOf(HOSPITAL, STATION));
    private static final TermPath A_STATION = KIND.refine(casesOf(STATION));
    private static final TermPath A_HOSPITAL = KIND.refine(casesOf(HOSPITAL));
    private static final TermPath NOT_A_HOSPITAL = KIND.refine(casesOf(STATION, DEPOT));

    /**
     * A narrowing to several cases holds together with one to a case among them, as the meet of the
     * two says ({@link CasesLeft#meet}): a value left {@code Hospital} or {@code Station} may be a
     * {@code Station}, so a name read under each is one place.
     */
    @Test
    void aNarrowingToSeveralCasesHoldsTogetherWithOneToACaseAmongThem() {
        assertNotNull(casesOf(HOSPITAL, STATION).meet(casesOf(STATION)));
        assertTrue(EITHER.standsAtUnderOrAround(A_STATION));
        assertTrue(A_STATION.standsAtUnderOrAround(EITHER));
        assertTrue(EITHER.then("code").standsAtOrUnder(A_STATION.then("code")));
        assertTrue(A_STATION.then("code").standsAtOrUnder(EITHER.then("code")));
        assertTrue(EITHER.then("code").bearsOn(A_STATION.then("code")));
    }

    /** Two narrowings that leave one case in common hold together, and two that leave none are
     *  two cases of the value. */
    @Test
    void narrowingsThatShareACaseHoldTogetherAndOnesThatShareNoneDoNot() {
        assertTrue(EITHER.then("code").standsAtOrUnder(NOT_A_HOSPITAL.then("code")));
        assertFalse(EITHER.then("code").standsAtOrUnder(NOT_A_HOSPITAL.then("name")));
        assertFalse(EITHER.then("code").bearsOn(NOT_A_HOSPITAL.then("name")));
        assertFalse(A_HOSPITAL.then("code").standsAtUnderOrAround(NOT_A_HOSPITAL.then("code")));
        assertTrue(A_HOSPITAL.then("code").bearsOn(NOT_A_HOSPITAL.then("name")));
    }

    /**
     * A narrowing taken under another is of another position: {@code r@Some@Some} says the value
     * the outer optional holds is present as well, and asks nothing of the outer one that
     * {@code r@Some} does not.
     */
    @Test
    void aNarrowingTakenUnderAnotherIsOfTheValueTheOtherLeaves() {
        TermPath inner = PRESENT.refine(Refinement.of(new Case.Presence(true)));
        TermPath innerAbsent = PRESENT.refine(Refinement.of(new Case.Presence(false)));
        assertTrue(inner.isAtOrUnder(PRESENT));
        assertTrue(inner.standsAtOrUnder(PRESENT));
        assertTrue(inner.standsAtUnderOrAround(PRESENT));
        assertTrue(inner.then("code").standsAtOrUnder(PRESENT));
        assertFalse(inner.standsAtUnderOrAround(innerAbsent));
        assertTrue(inner.bearsOn(innerAbsent));
        assertFalse(inner.standsAtUnderOrAround(ABSENT));
    }

    /**
     * A narrowing at a name the cases of a sum may share and one under a case of the sum may be of
     * one value, which a path cannot tell. Where they share no case, each question answers on its
     * own side: they bear on each other, they stand together, and neither is within the other on
     * every row.
     */
    @Test
    void narrowingsThatMayExcludeEachOtherThroughASharedNameAreAnsweredOnEachQuestionsOwnSide() {
        TermPath q = TermPath.of("r").then("q");
        TermPath atTheName = q.then("flag").refine(Refinement.of(new Case.Presence(true)));
        TermPath underACase = q.refine(casesOf(STATION)).then("flag")
                .refine(Refinement.of(new Case.Presence(false)));
        assertTrue(atTheName.then("x").bearsOn(underACase.then("y")));
        assertTrue(underACase.then("y").bearsOn(atTheName.then("x")));
        assertTrue(atTheName.standsAtUnderOrAround(underACase));
        assertTrue(atTheName.standsAtOrUnder(underACase));
        assertFalse(atTheName.standsAtOrUnderOnEveryRow(underACase));
        assertFalse(underACase.standsAtOrUnderOnEveryRow(atTheName));
        TermPath presentUnderACase = q.refine(casesOf(STATION)).then("flag")
                .refine(Refinement.of(new Case.Presence(true)));
        assertFalse(atTheName.then("x").bearsOn(presentUnderACase.then("y")),
                "where they share a case the two are apart as their steps are");
        assertFalse(presentUnderACase.standsAtOrUnderOnEveryRow(atTheName),
                "within on every row only where shown, and where the name stands under the case is"
                        + " what a path does not say");
    }

    /** A narrowing of what an optional holds is of another position than the optional, and leaves
     *  nothing of the two in doubt. */
    @Test
    void aNarrowingOfWhatAnOptionalHoldsLeavesNothingInDoubt() {
        TermPath innerAbsent = PRESENT.refine(Refinement.of(new Case.Presence(false)));
        assertTrue(innerAbsent.standsAtOrUnderOnEveryRow(PRESENT));
        assertFalse(innerAbsent.then("x").bearsOn(PRESENT.then("y")));
    }

    /**
     * A place is within another on every row ({@link TermPath#standsAtOrUnderOnEveryRow}) where
     * it is narrowed as far as the other is or further: on a row where {@code x} is a
     * {@code Hospital}, {@code x.code} stands at no {@code x@Station.code}.
     */
    @Test
    void aPlaceIsWithinAnotherOnEveryRowWhereItIsNarrowedAsFarOrFurther() {
        assertTrue(A_STATION.then("code").standsAtOrUnderOnEveryRow(EITHER.then("code")));
        assertTrue(A_STATION.then("code").standsAtOrUnderOnEveryRow(KIND.then("code")));
        assertTrue(A_STATION.then("code").standsAtOrUnderOnEveryRow(KIND));
        assertFalse(KIND.then("code").standsAtOrUnderOnEveryRow(A_STATION.then("code")));
        assertFalse(EITHER.then("code").standsAtOrUnderOnEveryRow(A_STATION.then("code")));
        assertFalse(A_HOSPITAL.then("code").standsAtOrUnderOnEveryRow(NOT_A_HOSPITAL.then("code")));
        TermPath inner = PRESENT.refine(Refinement.of(new Case.Presence(true)));
        assertTrue(inner.standsAtOrUnderOnEveryRow(PRESENT));
        assertFalse(PRESENT.standsAtOrUnderOnEveryRow(inner));
    }

    /**
     * Over every pair of a set of places, against what owns each half of the question: two stand
     * at, under or around each other exactly where the cases each requires hold together
     * ({@link Requirements#compatibleWith}) and the steps that go somewhere, narrowings taken out,
     * are one within the other ({@link TermPath#isAtOrUnder}); they bear on each other where that
     * holds or the cases do not; and the one-way half extends being inside step for step.
     */
    @Test
    void itIsTheOneWayHalfOfBearingThatExtendsBeingInsideStepForStep() {
        TermPath inner = PRESENT.refine(Refinement.of(new Case.Presence(true)));
        List<TermPath> places = List.of(R, ITEMS, ITEMS.element(), ITEMS.element().then("price"),
                R.then("code"), R.then("code").then("digit"), PRESENT, ABSENT,
                PRESENT.then("code"), PRESENT.then("a"), ABSENT.then("b"), R.then("total"),
                TermPath.of("s"), inner, inner.then("code"),
                PRESENT.refine(Refinement.of(new Case.Presence(false))),
                KIND, EITHER, A_STATION, A_HOSPITAL, NOT_A_HOSPITAL, EITHER.then("code"),
                A_STATION.then("code"), A_HOSPITAL.then("code"), NOT_A_HOSPITAL.then("name"),
                KIND.then("code"));
        for (TermPath one : places) {
            for (TermPath other : places) {
                String pair = one + " and " + other;
                boolean together = one.requirements().compatibleWith(other.requirements());
                TermPath here = withoutNarrowings(one);
                TermPath there = withoutNarrowings(other);
                assertEquals(together && here.isAtOrUnder(there), one.standsAtOrUnder(other),
                        pair);
                assertEquals(together && (here.isAtOrUnder(there) || there.isAtOrUnder(here)),
                        one.standsAtUnderOrAround(other), pair);
                assertEquals(!together || one.standsAtUnderOrAround(other), one.bearsOn(other),
                        pair);
                if (one.isAtOrUnder(other)) {
                    assertTrue(one.standsAtOrUnderOnEveryRow(other), pair);
                }
                assertEquals(one.standsAtOrUnder(other) && narrowedAsFar(one, other),
                        one.standsAtOrUnderOnEveryRow(other), pair);
            }
        }
    }

    /** Whether every position {@code wider} narrows, {@code one} narrows to cases among those. */
    private static boolean narrowedAsFar(TermPath one, TermPath wider) {
        for (var each : wider.requirements().refinements().entrySet()) {
            CasesLeft mine = one.requirements().at(each.getKey());
            if (mine == null || !mine.within(each.getValue())) {
                return false;
            }
        }
        return true;
    }

    private static TermPath withoutNarrowings(TermPath path) {
        return TermPath.of(path.head(), path.steps().stream()
                .filter(step -> !(step instanceof TermPath.Step.Refine)).toList());
    }
}
