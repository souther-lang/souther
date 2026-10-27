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

    /** A rule that says more than the definition, and that no price meets, is not the definition:
     *  no line is shown. */
    @Test
    void aRuleThatSaysMoreThanTheDefinitionIsNotTakenForOne() {
        String source = quote("value >= 0.0m").replace("""
                                      * (1.0m - discount.value))) == 0
                """, """
                                      * (1.0m - discount.value))) == 0
                        && Decimal.compare(listPrice.value, 0.0m) < 0
                """);

        assertFalse(lineHoldsAValue(source));
    }

    private static final String NET = """
            Decimal.compare(n.value,
                Decimal.round(2, HALF_UP, Decimal.fromInt(q.value) * p.value)) == 0""";

    /** A record {@code R} defining {@code n} as the rounded product, beside two numbers held at
     *  the greatest whole number, whose product no run works out. */
    private static String recordWith(String helper, String rule) {
        return """
                module demo

                data Amount = Decimal
                    invariant value >= 0.0m
                data Quantity = Int
                    invariant value >= 1
                data UnitPrice = Decimal
                    invariant value >= 0.0m
                data Greatest = Int
                    invariant value >= 9223372036854775807
                %s
                data R = { q: Quantity, p: UnitPrice, n: Amount, a: Greatest, b: Greatest }
                    invariant %s

                data Ok
                behavior take : (r: R) -> Ok
                let take (r) = Ok
                """.formatted(helper, rule);
    }

    private static boolean recordHoldsAValue(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        String module = compilation.modules().get(0);
        TypeSymbol record = TypeSymbols.declared(new TypeKey(module, "R"));
        return Rules.of(record, RuleReadingContext.unshared(RuleReadings.of(compilation, module),
                ReadAs.THE_COMPILATION_DOES, TestDay.TODAY)).bounds().shownToHoldAValue();
    }

    /** The definition through a helper that only restates it is the same rule. */
    @Test
    void aHelperThatOnlyRestatesTheDefinitionIsTheDefinition() {
        assertTrue(recordHoldsAValue(recordWith("""
                let defines (n: Amount, q: Quantity, p: UnitPrice): Bool = %s
                """.formatted(NET), "defines(n, q, p)")));
    }

    /**
     * A value a binding is given is worked out whether or not the rule reads its name. The
     * definition is met at any places, and the product of two numbers held at the greatest whole
     * number is worked out by no run, so no record is.
     */
    @Test
    void aBindingThatNoRunWorksOutLeavesNoRecordHoweverTheDefinitionHolds() {
        assertFalse(recordHoldsAValue(recordWith("""
                let defines (n: Amount, q: Quantity, p: UnitPrice, a: Greatest, b: Greatest): Bool = {
                    let unused = a.value * b.value
                    %s
                }
                """.formatted(NET), "defines(n, q, p, a, b)")));
    }

    /** The same product in the number the place is defined as: no step of it stays inside the
     *  order it is worked out in, so the places are not free. */
    @Test
    void aProductNoRunWorksOutInsideTheNumberIsNoDefinitionOfFreePlaces() {
        assertFalse(recordHoldsAValue(recordWith("", """
                Decimal.compare(n.value, Decimal.round(2, HALF_UP,
                    Decimal.fromInt(q.value) * p.value + Decimal.fromInt(a.value * b.value))) == 0""")));
    }

    /** The definition comes to a net past the end for other places, so it restricts them; what
     *  leaves a line is one written down, a unit at no price, which comes to nothing. So the
     *  fields beside the list are not withheld, though the line is no value of the definition
     *  alone. */
    @Test
    void aNetThatTheDefinitionCanComeToPastItsEndLeavesALineByOneWrittenDown() {
        String capped = quote("value >= 0.0m && value <= 1.0m");

        assertTrue(lineHoldsAValue(capped));
        assertTrue(certified(capped, "q.subtotal"));
    }
}
