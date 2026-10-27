package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A declaration whose rules relate its numbers to one another holds a value where one is written
 * down that every rule folds to true over.
 *
 * <p>No bound says a relation, so the bounds of such a declaration are never the whole of what its
 * rules leave, and nothing about the declaration is shown by them. A value is: the least ones the
 * rules mention, tried in the order of how far each is from the first, and every rule folded over
 * them by the fold the discharge of a construction folds with. What is not shown is not refused —
 * a declaration only a value outside those tried holds is one nothing is shown of.
 */
class ARelationBetweenNumbersIsHeldByAValueWrittenDownTest {

    private static final String PRODUCT = """
            Decimal.compare(net.value, Decimal.round(2, HALF_UP,
                Decimal.fromInt(quantity) * price.value * (1.0m - discount.value))) == 0""";

    /** {@code fields} are the declaration's, and {@code rules} one invariant to a line. */
    private static boolean holdsAValue(String before, String fields, String... rules) {
        String source = """
                module example.relation

                %s

                data Subject = { %s }
                    %s

                data Ok

                behavior take : (n: Subject) -> Ok
                let take (n) = Ok
                """.formatted(before, fields, String.join("\n    ", rules));
        Compilation compilation = Compilation.ofSource(source, "Main");
        String module = compilation.modules().get(0);
        TypeSymbol subject = TypeSymbols.declared(new TypeKey(module, "Subject"));
        return Rules.of(subject, RuleReadingContext.unshared(RuleReadings.of(compilation, module),
                ReadAs.THE_COMPILATION_DOES, TestDay.TODAY)).bounds().shownToHoldAValue();
    }

    private static final String AMOUNTS = """
            data Amount = Decimal
                invariant value >= 0.0m

            data Rate = Decimal
                invariant value >= 0.0m && value <= 0.5m
            """;

    /** The net of a line is its quantity at its price less its discount, rounded: one such line
     *  is the quantity one at no price and no discount. */
    @Test
    void aProductRoundedToAPriceIsHeldByTheLeastValuesOfItsFactors() {
        assertTrue(holdsAValue(AMOUNTS, "quantity: Int, price: Amount, discount: Rate, net: Amount",
                "invariant quantity = quantity >= 1",
                "invariant net = " + PRODUCT.replace("\n", " ")));
    }

    /** A rule a value written down does not hold is a rule nothing is shown of. */
    @Test
    void aRuleOnlyAValueNoneOfTheLeastOnesIsHeldByIsNotShown() {
        assertFalse(holdsAValue("", "a: Int", "invariant square = a * a == 2401"),
                "49 is not a number the rule mentions or sits beside");
    }

    /** Written the other way, the number the rule names is the one tried. */
    @Test
    void aNumberARuleNamesIsTriedAtThatNumber() {
        assertTrue(holdsAValue("", "a: Int, b: Int",
                "invariant sum = a + b == 2401",
                "invariant order = a > b"));
    }

    @Test
    void rulesNoValueHoldsTogetherAreNotShown() {
        assertFalse(holdsAValue("", "a: Int, b: Int",
                "invariant low = a + b == 1",
                "invariant high = a + b == 2"));
    }

    /** A string a pattern holds is one the reading of the pattern proposes, and no short string
     *  is likely to be it. */
    @Test
    void aStringAPatternHoldsIsProposedByTheReadingOfThePattern() {
        assertTrue(holdsAValue("""
                data Code = String
                    invariant String.matches("[A-Z]{2}-[0-9]{4}", value)
                """, "code: Code, a: Int, b: Int", "invariant product = a * b == 6"));
    }

    /** A date is a place no value is written for. */
    @Test
    void aPlaceNoValueIsWrittenForLeavesTheDeclarationNotShown() {
        assertFalse(holdsAValue("", "on: Date, a: Int, b: Int",
                "invariant product = a * b == 6"));
    }
}
