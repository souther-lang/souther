package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Scopes;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A fact a caller holds beside the rules is solved with them, not met onto their answer.
 *
 * <p>Projecting is not distributive over meeting. What the rules leave a form, met afterwards
 * against what each of its coordinates is known to be, is wider than what the rules and those facts
 * leave it together — and the difference is a rule going missing rather than a bound being loose.
 *
 * <p>A rule holding two coordinates at one apiece says nothing about a form that also names a third
 * the rules leave unbounded: the third can be taken as far below nothing as anybody likes, so the
 * form has no floor. Met afterwards against a floor the caller did have for that third coordinate,
 * the sum of the three still has no floor, because meeting a bound on the whole form against a
 * bound on the whole form is all that is left to do. Put in first, the rule and the floor hold each
 * other up and the form stops where it should.
 *
 * <p>Which facts a caller has that these do not is that caller's business — where a position was
 * read to stop is read by a reader of its own, and what a term guarantees of itself is true whether
 * or not a clause says so.
 */
class WhatIsKnownBesideTheRulesIsSolvedWithThemTest {

    /** Two coordinates a rule relates, and a third nothing here bounds. */
    private static final String TWO_RELATED_AND_A_THIRD = """
            module example.third

            data P = { x: Int, y: Int, z: Int }
                invariant oneOfXY = x + y >= 1

            data Taken

            behavior take : (p: P) -> Taken
            """;

    @Test
    void aFloorPutInHoldsTheRuleUpAndMetAfterwardsDoesNot() {
        FieldDomains.Settled rules = read(TWO_RELATED_AND_A_THIRD).given(Map.of());
        Map<FieldDomains.Coordinate, BigDecimal> sum = new LinkedHashMap<>();
        sum.put(at("x"), BigDecimal.ONE);
        sum.put(at("y"), BigDecimal.ONE);
        sum.put(at("z"), BigDecimal.ONE);

        // Nothing bounds the third, so the rules alone leave the sum nowhere in particular.
        assertNull(rules.boundsOf(sum).min(), "the third can be as far below nothing as it likes");

        NumericDomain.Bounds withAFloorUnderTheThird = rules
                .within(Map.of(at("z"), new NumericDomain.Bounds(
                        Endpoint.inclusive(count(0)), null)))
                .boundsOf(sum);

        assertEquals(Endpoint.inclusive(count(1)), withAFloorUnderTheThird.min(),
                "two of them come to one and the third is never below nought");
    }

    /** And a fact about a coordinate these do not name settles nothing, which is the safe way. */
    @Test
    void aFactAboutACoordinateTheseDoNotNameChangesNothing() {
        FieldDomains.Settled rules = read(TWO_RELATED_AND_A_THIRD).given(Map.of());
        Map<FieldDomains.Coordinate, BigDecimal> sum = new LinkedHashMap<>();
        sum.put(at("x"), BigDecimal.ONE);

        assertEquals(rules.boundsOf(sum),
                rules.within(Map.of(new FieldDomains.Coordinate("nowhere", false),
                        new NumericDomain.Bounds(Endpoint.inclusive(count(3)), null)))
                        .boundsOf(sum));
    }

    private static FieldDomains.Coordinate at(String path) {
        return new FieldDomains.Coordinate(path, false);
    }

    private static Count count(int at) {
        return new Count(BigDecimal.valueOf(at));
    }

    private static FieldDomains read(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        Symbols symbols = Scopes.derived(compilation.db(), compilation.modules().get(0)).value();
        TypeSymbol name = TypeSymbols.declared(new TypeKey(symbols.module(), "P"));
        return FieldDomains.of(name,
                (Hir.Data) symbols.declarations().declaration(name.key()), symbols,
                ReadAs.THE_COMPILATION_DOES);
    }
}
