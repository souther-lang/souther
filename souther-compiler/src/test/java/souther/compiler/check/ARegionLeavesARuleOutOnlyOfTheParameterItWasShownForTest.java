package souther.compiler.check;

import souther.compiler.TestDay;
import souther.compiler.carrier.Membership;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * A rule put aside for one parameter stays in force for every other.
 *
 * <p>A rule of a declaration is a rule of every value of it, and what shows it holds nothing a row
 * at a line needs is shown of the value a guard is about. A region read again without it for that
 * parameter and without it for the next as well would answer about a second value from a proof
 * made about the first.
 */
class ARegionLeavesARuleOutOnlyOfTheParameterItWasShownForTest {

    private static final String MODULE = "example.pairs";

    private static final String PAIRS = """
            module example.pairs

            data Pair = { a: Int, b: Int }
                invariant a + b >= 9

            data Done

            behavior take : (x: Pair, y: Pair) -> Done
            """;

    private static final Endpoint FLOOR = Endpoint.inclusive(Count.of(9));

    @Test
    void theParameterItWasLeftOutOfLosesTheFloorAndTheOtherKeepsIt() {
        Compilation compilation = Compilation.ofSource(PAIRS, "Main");
        SearchRegion region = regionOf(compilation);
        assertEquals(FLOOR, floorOfTheSum(region, "x"));
        assertEquals(FLOOR, floorOfTheSum(region, "y"));

        SearchRegion withoutForX =
                region.withoutTheRelationOf(Map.of("x", partsOfTheRule(compilation)));
        assertNull(floorOfTheSum(withoutForX, "x"), "the rule is put aside where it was shown");
        assertEquals(FLOOR, floorOfTheSum(withoutForX, "y"),
                "and is in force for the parameter it was not shown for");

        SearchRegion withoutForY =
                region.withoutTheRelationOf(Map.of("y", partsOfTheRule(compilation)));
        assertEquals(FLOOR, floorOfTheSum(withoutForY, "x"));
        assertNull(floorOfTheSum(withoutForY, "y"));
    }

    @Test
    void nothingLeftOutIsTheRegionItself() {
        SearchRegion region = regionOf(Compilation.ofSource(PAIRS, "Main"));
        assertSame(region, region.withoutTheRelationOf(Map.of()));
    }

    private static final String BAND = """
            module example.pairs

            data Band = { a: Int, b: Int }
                invariant a >= -30
                invariant a <= 30
                invariant b >= 210
                invariant b <= 220
                invariant a + b >= 100
                invariant a + b <= 201

            data Done

            behavior take : (x: Band) -> Done
            """;

    /**
     * Left out is the relation and not what each place was left by itself: the sum rule is what
     * keeps {@code a} below nought, and the region without it still holds {@code a} there, so
     * the sum of the two reaches the top of the two runs and not the top of the two boxes.
     */
    @Test
    void whatEachPlaceWasLeftIsKeptWhenTheRelationBetweenThemIsLeftOut() {
        Compilation compilation = Compilation.ofSource(BAND, "Main");
        SearchRegion region = regionOf(compilation);
        NumericTerm.ValueOf a = new NumericTerm.ValueOf(TermPath.of("x").then("a"));
        Endpoint top = Endpoint.inclusive(Count.of(-9));
        assertEquals(top, runOf(region, a).max(), "the rules leave a nothing above -9");

        SearchRegion without = region.withoutTheRelationOf(
                Map.of("x", partsOfTheRule(compilation, "Band")));
        assertEquals(runOf(region, a), region.wholeRunOf(a),
                "with the relation in force every a still has a b, the lowest sum being past 100");
        assertEquals(runOf(region, a), without.wholeRunOf(a),
                "the region without the relation answers the run it kept as whole");
        assertEquals(runOf(region, a), runOf(without, a),
                "a keeps the run it was left with the relation in force");
        Endpoint sumTop = Endpoint.inclusive(Count.of(211));
        assertEquals(sumTop, ceilingOfTheSum(without, "x"),
                "the sum reaches what the two runs reach, which is past what the rule allows");
        assertEquals(Endpoint.inclusive(Count.of(201)), ceilingOfTheSum(region, "x"));
    }

    /** The run the region leaves the one field. */
    private static NumericDomain.Bounds runOf(SearchRegion region, NumericTerm.ValueOf field) {
        return switch (region.projectionOf(LinearForm.atom(field))) {
            case NumericDomain.FormProjection.Within(NumericDomain.Bounds runs) -> runs;
            default -> throw new AssertionError("these rules leave a value for " + field);
        };
    }

    /** Where the sum of the parameter's two fields stops, or null where nothing stops it. */
    private static Endpoint ceilingOfTheSum(SearchRegion region, String parameter) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(new NumericTerm.ValueOf(TermPath.of(parameter).then("a")), ExactRatio.ONE);
        coefs.put(new NumericTerm.ValueOf(TermPath.of(parameter).then("b")), ExactRatio.ONE);
        return switch (region.projectionOf(new LinearForm<>(ExactRatio.ZERO, coefs))) {
            case NumericDomain.FormProjection.Within(NumericDomain.Bounds runs) -> runs.max();
            default -> throw new AssertionError("these rules leave a value for " + parameter);
        };
    }

    private static Set<PartId<RuleRef.Invariant>> partsOfTheRule(Compilation compilation) {
        return partsOfTheRule(compilation, "Pair");
    }

    /** The parts of the clauses of {@code declaration} that relate two of its fields. */
    private static Set<PartId<RuleRef.Invariant>> partsOfTheRule(Compilation compilation,
                                                                 String declaration) {
        DeclarationMeaning.Product product = (DeclarationMeaning.Product) ClauseReadings.meaningOf(
                compilation.db(), MODULE, TypeSymbols.declared(new TypeKey(MODULE, declaration)));
        Set<PartId<RuleRef.Invariant>> parts = new LinkedHashSet<>();
        for (ClauseMeaning each : product.clauses()) {
            ClauseMeaning.Stated stated = (ClauseMeaning.Stated) each;
            if (stated.affine() instanceof ClauseAffineMeaning.Exact exact
                    && exact.conjuncts().getFirst().form().coefs().size() == 2) {
                parts.addAll(stated.parts().ids());
            }
        }
        return parts;
    }

    /** Where the sum of the parameter's two fields starts, or null where nothing stops it. */
    private static Endpoint floorOfTheSum(SearchRegion region, String parameter) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(new NumericTerm.ValueOf(TermPath.of(parameter).then("a")), ExactRatio.ONE);
        coefs.put(new NumericTerm.ValueOf(TermPath.of(parameter).then("b")), ExactRatio.ONE);
        return switch (region.projectionOf(new LinearForm<>(ExactRatio.ZERO, coefs))) {
            case NumericDomain.FormProjection.Within(NumericDomain.Bounds runs) -> runs.min();
            default -> throw new AssertionError("these rules leave a value for " + parameter);
        };
    }

    private static SearchRegion regionOf(Compilation compilation) {
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext reading =
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        return InputDomain.of(sigs.get("take"), reading,
                        TypeCardinality.Counts.workedOutIn(reading), Membership.none())
                .quantities(rules).region();
    }
}
