package souther.compiler.inputs;

import souther.compiler.check.Carrier;
import souther.compiler.check.DeclarationAccess;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.ScopedDeclarations;
import souther.compiler.check.Symbols;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.observe.Limits;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A number computed of each element reads a field of the element, and where that field was not
 * read in full the reading says what stopped it, and not that the field is no number.
 *
 * <p>The two are told apart because a wider run settles one and nothing settles the other: a
 * {@code Text} where a number was expected is a position that does not fit, and a value cut short is
 * one nobody has seen.
 */
class AFieldOfAnElementThatWasNotReadInFullIsSaidAsThatTest {

    private static final String MODEL = """
            module g

            behavior decide : (scores: List<Int>) -> Int
            """;

    private static final TermPath SCORES = TermPath.of("scores");

    @Test
    void aFieldCutShortIsSaidAsWhatCutItShort() {
        for (ObservedValue stopped : List.of(new ObservedValue.Unknown("nothing read it"),
                new ObservedValue.Truncated(Limits.DEFAULT.nodesFigure()))) {
            NumericTerm.Reading read = overOneElementHolding(stopped);

            NumericTerm.Reading.Missing missing =
                    assertInstanceOf(NumericTerm.Reading.Missing.class, read, () -> stopped + ": " + read);
            assertEquals(Membership.unread(stopped).cause(), missing.cause());
        }
    }

    @Test
    void aFieldOfAnotherShapeIsNoNumber() {
        assertEquals(new NumericTerm.Reading.NotNumber(),
                overOneElementHolding(new ObservedValue.Text("x")));
    }

    private static NumericTerm.Reading overOneElementHolding(ObservedValue field) {
        Carrier whole = Carrier.ofValue(Type.Prim.INT, DeclarationAccess.NONE);
        RuleReadingSource rules = RuleReadings.ofSource(MODEL);
        Symbols symbols = rules.symbols();
        ElementProjection itself = new ElementProjection(List.of());
        NumericTerm.TakenOver scored = NumericTerm.TakenOver.of(
                ValueName.Stdlib.operation("List", "sum"),
                new RunSource.ComputedOccurrences(SCORES.element(), new ElementValue.Affine(
                        new LinearForm<>(ExactRatio.ZERO, Map.of(itself, ExactRatio.ONE))),
                        Type.Prim.INT, null),
                Type.Prim.INT, ScopedDeclarations.wrapsOf(symbols), symbols);
        TermOrders on = TermOrdersFixtures.computed(scored, whole, whole, Map.of(itself, whole));
        List<Function<ElementProjection, ObservedValue>> each = List.of(_ -> field);
        return on.readOverElements(each);
    }
}
