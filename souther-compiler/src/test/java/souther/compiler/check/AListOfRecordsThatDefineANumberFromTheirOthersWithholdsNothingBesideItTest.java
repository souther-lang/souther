package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.carrier.Membership;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.Position;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A record that defines one of its numbers from the others is a value whatever the others are, so
 * a list of them is a value of its rule, and a field beside that list is not withheld by it.
 *
 * <p>{@code net == round(quantity * price * (1 - discount))} states what {@code net} is and
 * restricts none of the three places it is made of, provided every number it comes to is one
 * {@code net} admits. Then any places the rules of their own leave have a {@code net} beside them,
 * and a line exists without anything having been built.
 */
class AListOfRecordsThatDefineANumberFromTheirOthersWithholdsNothingBesideItTest {

    private static String quote(String amount) {
        return """
                module demo

                data Amount = Decimal
                    invariant %s
                data Quantity = Int
                    invariant value >= 1
                data UnitPrice = Decimal
                    invariant value >= 0.0m
                data DiscountRate = Decimal
                    invariant value >= 0.0m && value <= 0.5m

                data ProductCode = String
                    invariant String.matches("[A-Z]{2}-[0-9]{4}", value)

                data Line =
                    { product: ProductCode
                    , quantity: Quantity
                    , listPrice: UnitPrice
                    , discount: DiscountRate
                    , net: Amount
                    }
                    invariant Decimal.compare(net.value,
                        Decimal.round(2, HALF_UP, Decimal.fromInt(quantity.value) * listPrice.value
                                      * (1.0m - discount.value))) == 0

                data Lines = List<Line>
                    invariant nonEmpty = List.length(value) >= 1
                    invariant uniqueProducts = List.allDistinctBy(.product, value)

                data Quote = { lines: Lines, subtotal: Amount, total: Amount }
                    invariant Decimal.compare(total.value, subtotal.value) <= 0

                data Ok

                behavior probe : (q: Quote) -> Ok
                let probe (q) = Ok
                """.formatted(amount);
    }

    private static boolean certified(String source, String path) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        String module = compilation.modules().get(0);
        RuleReadingContext reading = RuleReadingContext.unshared(
                RuleReadings.of(compilation, module), ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        for (Position each : InputDomain.of(
                        compilation.db().ask(new Bodies.DeclaredSignatures(module)).value()
                                .get("probe"),
                        reading, TypeCardinality.Counts.workedOutIn(reading),
                        Membership.none()).positions()) {
            if (each.path().toString().equals(path)) {
                return each.projection().isCertified();
            }
        }
        throw new AssertionError("no position " + path);
    }

    private static boolean lineHoldsAValue(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        String module = compilation.modules().get(0);
        TypeSymbol line = TypeSymbols.declared(new TypeKey(module, "Line"));
        return Rules.of(line, RuleReadingContext.unshared(RuleReadings.of(compilation, module),
                ReadAs.THE_COMPILATION_DOES, TestDay.TODAY)).bounds().shownToHoldAValue();
    }

    @Test
    void aLineWhoseNetIsDefinedFromItsOthersIsAValue() {
        assertTrue(lineHoldsAValue(quote("value >= 0.0m")));
    }

    @Test
    void theFieldsBesideAListOfSuchLinesAreNotWithheldByIt() {
        assertTrue(certified(quote("value >= 0.0m"), "q.subtotal"));
        assertTrue(certified(quote("value >= 0.0m"), "q.total"));
    }

    /** A net that stops at one is no number the product comes to: the definition restricts the
     *  places it is made of, and no line is shown. */
    @Test
    void aRuleThatSaysMoreThanTheDefinitionIsNotTakenForOne() {
        String source = quote("value >= 0.0m").replace("""
                                      * (1.0m - discount.value))) == 0
                """, """
                                      * (1.0m - discount.value))) == 0
                        && Decimal.compare(listPrice.value + 1.0m, 0.0m) > 0
                """);

        assertFalse(lineHoldsAValue(source));
    }

    @Test
    void aNetThatTheDefinitionCanComeToPastItsEndIsNoLine() {
        String capped = quote("value >= 0.0m && value <= 1.0m");

        assertFalse(lineHoldsAValue(capped));
        assertFalse(certified(capped, "q.subtotal"));
    }
}
