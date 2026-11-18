package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.TestDay;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.TypeCardinality;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A region says two numbers are related where what it holds of one may hold the other narrower:
 * a rule names both, or what one adds up to names the other, as a total of each element less one
 * is the total of the elements less how many there are. Numbers neither ties are free of one
 * another.
 */
class ARegionRelatesNumbersTheRulesOrAContainerTieTest {

    private static final Compilation MODEL = ACompiledModel.answered("""
            module example.related

            data Line = { a: Int }

            data P = { b: Int, c: Int, d: Int, xs: List<Line> }
                invariant ordered = b <= c

            data Taken

            behavior take : (p: P) -> Taken
            """);

    private static final RuleReadingSource RULES =
            RuleReadings.of(MODEL, MODEL.modules().get(0));

    private static final InputDomain INPUTS = inputs();

    private static final SearchRegion REGION = INPUTS.quantities(RULES).region();

    private static final TermPath XS = TermPath.of("p").then("xs");

    /** The elements' {@code a} less one, added up. */
    private static final NumericTerm LESS_ONE = NumericTerm.TakenOver.of(
            ValueName.Stdlib.operation("List", "sum"),
            new RunSource.ComputedOccurrences(XS.element(), new ElementValue.Affine(
                    new LinearForm<>(ExactRatio.ONE.negated(), Map.of(
                            ElementProjection.ofFields(List.of("a")), ExactRatio.ONE))),
                    Type.INT, null),
            Type.INT, RULES.inners(), RULES.symbols());

    private static final NumericTerm HOW_MANY = NumericTerm.TakenOf.asItStands(
            ValueName.Stdlib.operation("List", "length"), XS, INPUTS.typeAt(XS, RULES),
            RULES.inners(), RULES.symbols());

    private static InputDomain inputs() {
        RuleReadingContext reading =
                RuleReadingContext.unshared(RULES, ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        return InputDomain.of(MODEL.db()
                        .ask(new Bodies.DeclaredSignatures(MODEL.modules().get(0))).value()
                        .get("take"), reading,
                TypeCardinality.Counts.workedOutIn(reading),
                souther.compiler.carrier.Membership.none());
    }

    private static NumericTerm value(String field) {
        return new NumericTerm.ValueOf(TermPath.of("p").then(field));
    }

    @Test
    void numbersARuleNamesAreRelated() {
        assertTrue(REGION.relates(List.of(value("b")), List.of(value("c"))));
    }

    /** No rule names either: what the total adds up to is what ties them. */
    @Test
    void aTotalAndWhatItAddsUpToAreRelated() {
        assertTrue(REGION.relates(List.of(LESS_ONE), List.of(HOW_MANY)));
    }

    @Test
    void numbersNothingTiesAreFree() {
        assertFalse(REGION.relates(List.of(value("b")), List.of(value("d"))));
        assertFalse(REGION.relates(List.of(value("d")), List.of(HOW_MANY)));
    }
}
