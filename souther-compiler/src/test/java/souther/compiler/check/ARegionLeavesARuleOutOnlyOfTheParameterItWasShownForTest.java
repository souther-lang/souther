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

        SearchRegion withoutForX = region.leavingOut(Map.of("x", partsOfTheRule(compilation)));
        assertNull(floorOfTheSum(withoutForX, "x"), "the rule is put aside where it was shown");
        assertEquals(FLOOR, floorOfTheSum(withoutForX, "y"),
                "and is in force for the parameter it was not shown for");

        SearchRegion withoutForY = region.leavingOut(Map.of("y", partsOfTheRule(compilation)));
        assertEquals(FLOOR, floorOfTheSum(withoutForY, "x"));
        assertNull(floorOfTheSum(withoutForY, "y"));
    }

    @Test
    void nothingLeftOutIsTheRegionItself() {
        SearchRegion region = regionOf(Compilation.ofSource(PAIRS, "Main"));
        assertSame(region, region.leavingOut(Map.of()));
    }

    private static Set<PartId<RuleRef.Invariant>> partsOfTheRule(Compilation compilation) {
        DeclarationMeaning.Product pair = (DeclarationMeaning.Product) ClauseReadings.meaningOf(
                compilation.db(), MODULE, TypeSymbols.declared(new TypeKey(MODULE, "Pair")));
        Set<PartId<RuleRef.Invariant>> parts = new LinkedHashSet<>();
        for (ClauseMeaning each : pair.clauses()) {
            parts.addAll(((ClauseMeaning.Stated) each).parts().ids());
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
