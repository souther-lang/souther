package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A path requires every narrowing it is written with ({@link TermPath#requirements}): a narrowing
 * of a position the step before narrowed to several cases is the same position narrowed once, to
 * the cases both leave, however the path is made; one to cases that share none with it is no path;
 * and one after a narrowing to one case is of the value that case stands for.
 */
class EveryNarrowingAPathIsWrittenWithIsOneItRequiresTest {

    private static final TypeSymbol HOSPITAL = TypeSymbols.declared(new TypeKey("probe", "Hospital"));
    private static final TypeSymbol STATION = TypeSymbols.declared(new TypeKey("probe", "Station"));
    private static final TypeSymbol DEPOT = TypeSymbols.declared(new TypeKey("probe", "Depot"));

    private static CasesLeft casesOf(TypeSymbol... leaves) {
        return CasesLeft.ofEach(Arrays.stream(leaves)
                .map(leaf -> Refinement.of(new Case.SumCase(leaf, true))).toList());
    }

    private static final CasesLeft SOME = CasesLeft.of(Refinement.of(new Case.Presence(true)));
    private static final TermPath X = TermPath.of("x");

    private static TermPath.Step narrowing(CasesLeft cases) {
        return new TermPath.Step.Refine(cases);
    }

    @Test
    void aNarrowingOfAPositionNarrowedToSeveralCasesIsOneNarrowingToWhatBothLeave() {
        TermPath folded = X.refine(casesOf(HOSPITAL, STATION)).refine(casesOf(STATION, DEPOT));
        assertEquals(X.refine(casesOf(STATION)), folded);
        assertEquals(List.of(narrowing(casesOf(STATION))), folded.steps());
        assertEquals(X.refine(casesOf(STATION)), X.refine(casesOf(HOSPITAL, STATION))
                .refine(casesOf(STATION)));
    }

    /** No value is left cases a narrowing shares none with, nor is both a case of a sum and an
     *  optional holding something; no path is narrowed to both. */
    @Test
    void aNarrowingThatSharesNoCaseWithTheOneBeforeIsNoPath() {
        TermPath either = X.refine(casesOf(HOSPITAL, STATION));
        assertThrows(IllegalArgumentException.class, () -> either.refine(casesOf(DEPOT)));
        assertThrows(IllegalArgumentException.class, () -> either.refine(SOME));
        assertFalse(either.admits(casesOf(DEPOT)));
        assertFalse(either.admits(SOME));
        assertTrue(either.admits(casesOf(STATION, DEPOT)));
        assertTrue(X.refine(casesOf(STATION)).admits(SOME));
        assertTrue(X.admits(casesOf(DEPOT)));
        assertThrows(IllegalArgumentException.class, () -> TermPath.of("x",
                List.of(narrowing(casesOf(HOSPITAL, STATION)), narrowing(SOME))));
    }

    /** A narrowing after one to a single case is of the value that case stands for, and both are
     *  kept. */
    @Test
    void aNarrowingAfterOneToASingleCaseIsOfTheValueThatCaseStandsFor() {
        TermPath inner = X.refine(SOME).refine(SOME);
        assertEquals(List.of(narrowing(SOME), narrowing(SOME)), inner.steps());
        assertEquals(2, inner.requirements().refinements().size());
        TermPath station = X.refine(casesOf(STATION)).refine(SOME);
        assertEquals(2, station.steps().size());
    }

    /** Every way of making a path from steps holds them alike. */
    @Test
    void everyWayOfMakingAPathFoldsTheNarrowingsAlike() {
        List<TermPath.Step> written = List.of(narrowing(casesOf(HOSPITAL, STATION)),
                narrowing(casesOf(STATION, DEPOT)), new TermPath.Step.Field("code"));
        TermPath expected = X.refine(casesOf(STATION)).then("code");
        assertEquals(expected, TermPath.of("x", written));
        assertEquals(expected, new TermPath("x", written));
        assertEquals(expected, new ElementProjection(written).from(X));
        assertEquals(new ElementProjection(expected.steps()), new ElementProjection(written));
        assertEquals(new ElementProjection(List.of(narrowing(casesOf(STATION)))),
                new ElementProjection(List.of()).narrowedTo(casesOf(HOSPITAL, STATION))
                        .narrowedTo(casesOf(STATION, DEPOT)));
    }

    /**
     * Over paths written every way two narrowings and a field can be put in a row: the path made of
     * them stands, on every row it stands anywhere, within the path of each prefix of what was
     * written that ends in a narrowing ({@link TermPath#standsAtOrUnderOnEveryRow}) — so what it
     * requires is every narrowing it was written with, and no requirement is put down for another.
     */
    @Test
    void whatAPathRequiresIsEveryNarrowingItWasWrittenWith() {
        List<CasesLeft> narrowings = List.of(casesOf(HOSPITAL, STATION), casesOf(STATION, DEPOT),
                casesOf(STATION), casesOf(HOSPITAL, DEPOT), SOME);
        List<List<TermPath.Step>> written = new ArrayList<>();
        for (CasesLeft first : narrowings) {
            for (CasesLeft second : narrowings) {
                written.add(List.of(narrowing(first), narrowing(second)));
                written.add(List.of(narrowing(first), new TermPath.Step.Field("f"),
                        narrowing(second)));
                written.add(List.of(narrowing(first), narrowing(second),
                        new TermPath.Step.Field("g")));
            }
        }
        int made = 0;
        int refused = 0;
        for (List<TermPath.Step> steps : written) {
            TermPath path;
            TermPath opened = TermPath.of("x", steps.subList(0, 1));
            boolean admitted = !(steps.get(1) instanceof TermPath.Step.Refine(CasesLeft second))
                    || opened.admits(second);
            // Refused exactly where the first narrows to several cases sharing none with the
            // second, which is what admits says of the path the first makes.
            boolean sharesNone = steps.getFirst() instanceof TermPath.Step.Refine(CasesLeft one)
                    && one.only() == null && steps.get(1)
                            instanceof TermPath.Step.Refine(CasesLeft other)
                    && one.meet(other) == null;
            assertEquals(sharesNone, !admitted, () -> "admits " + steps);
            try {
                path = TermPath.of("x", steps);
                assertTrue(admitted, () -> "made what was not admitted: " + steps);
            } catch (IllegalArgumentException noValue) {
                assertFalse(admitted, () -> "refused what was admitted: " + steps);
                refused++;
                continue;
            }
            made++;
            for (int at = 0; at < steps.size(); at++) {
                if (steps.get(at) instanceof TermPath.Step.Refine) {
                    TermPath prefix = TermPath.of("x", steps.subList(0, at + 1));
                    assertTrue(path.standsAtOrUnderOnEveryRow(prefix),
                            () -> path + " written as " + steps + " keeps " + prefix);
                }
            }
            for (int at = 1; at < path.steps().size(); at++) {
                assertFalse(path.steps().get(at - 1) instanceof TermPath.Step.Refine(CasesLeft had)
                        && had.only() == null
                        && path.steps().get(at) instanceof TermPath.Step.Refine,
                        () -> path + " narrows one position twice");
            }
        }
        assertTrue(made > 0, "some of them are paths");
        assertTrue(refused > 0, "some of them are no path");
    }
}
