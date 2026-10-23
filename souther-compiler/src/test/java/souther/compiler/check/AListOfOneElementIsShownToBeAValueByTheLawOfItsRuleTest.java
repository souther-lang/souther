package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.inputs.BlockReason;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Scopes;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.values.AdmissibleSet;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A field whose rules the bounds cannot hold, beside the amounts a relation is written over, is
 * shown to hold some value by the law of the operation its rule calls.
 *
 * <p>{@code List.allDistinctBy} is stated as its elements coming to as many different keys as there
 * are elements, which a list of one element satisfies whatever the key is. So where the length rule
 * leaves a list of one, and the element's own declaration is shown to hold a value, a list of one
 * line is a value of the field — and the amounts beside it, which nothing ties to it, are certified
 * at every value their own rules leave. What the field admits is not made any more exact by this:
 * one value being there is not every value.
 *
 * <p>Each control takes away one thing the proof stands on: a length rule leaving no list of one, an
 * element no value of which is shown, and a rule whose law turns on the element.
 */
class AListOfOneElementIsShownToBeAValueByTheLawOfItsRuleTest {

    private static final String DECLARED = """
            module example.quotes

            data Amount = Decimal
                invariant value >= 0.0m

            data Code = String
                invariant String.length(value) >= 1

            data Line = { product: Code, net: Amount }

            data Tangled = { product: Code, alt: Code }
                invariant String.matches("[a-z]+", product.value)
                    || String.matches("[0-9]+", alt.value)

            data Lines = List<Line>
                invariant nonEmpty = List.length(value) >= 1
                invariant uniqueProducts = List.allDistinctBy(.product, value)

            data Pairs = List<Line>
                invariant twoAtLeast = List.length(value) >= 2
                invariant uniqueProducts = List.allDistinctBy(.product, value)

            data TangledLines = List<Tangled>
                invariant nonEmpty = List.length(value) >= 1
                invariant uniqueProducts = List.allDistinctBy(.product, value)

            data PricedLines = List<Line>
                invariant nonEmpty = List.length(value) >= 1
                invariant priced = List.all(l -> Decimal.compare(l.net.value, 5.0m) > 0, value)

            data Quote = { lines: Lines, subtotal: Amount, total: Amount }
                invariant Decimal.compare(total.value, subtotal.value) <= 0

            data PairsQuote = { lines: Pairs, subtotal: Amount, total: Amount }
                invariant Decimal.compare(total.value, subtotal.value) <= 0

            data TangledQuote = { lines: TangledLines, subtotal: Amount, total: Amount }
                invariant Decimal.compare(total.value, subtotal.value) <= 0

            data PricedQuote = { lines: PricedLines, subtotal: Amount, total: Amount }
                invariant Decimal.compare(total.value, subtotal.value) <= 0
            """;

    @Test
    void aListOfOneLineIsAValueWhateverItsKeySoTheAmountsBesideItAreCertified() {
        FieldDomains read = readingOf("Quote");

        assertTrue(read.projectionAt(RuleKey.of("total")).isCertified(),
                () -> "a list of one line holds the rules on `lines`: "
                        + read.projectionAt(RuleKey.of("total")));
        assertInstanceOf(AdmissibleSet.Completeness.Wider.class,
                read.admits(RuleKey.of("lines")).completeness(),
                "and what `lines` admits is still wider than what is written: one value is not all");
        assertEquals(List.of(new BlockReason.ComparisonRelatingTwoValues()),
                reasonsAt(read, "total"),
                "so the relation over the amounts is read at every value they take");
    }

    @Test
    void aLengthRuleLeavingNoListOfOneShowsNothing() {
        assertFalse(readingOf("PairsQuote").projectionAt(RuleKey.of("total")).isCertified(),
                "two lines may share a key, and nothing says which two do not");
    }

    @Test
    void anElementNoValueOfWhichIsShownShowsNoListOfIt() {
        assertFalse(readingOf("TangledQuote").projectionAt(RuleKey.of("total")).isCertified(),
                "a list of one needs one element, and `Tangled`'s choice over two fields is not"
                        + " shown to leave one");
    }

    @Test
    void aRuleWhoseLawTurnsOnTheElementShowsNothing() {
        assertFalse(readingOf("PricedQuote").projectionAt(RuleKey.of("total")).isCertified(),
                "whether every line is priced past five turns on the line, not on how many there"
                        + " are");
    }

    private static List<BlockReason.RuleWithoutLineReason> reasonsAt(FieldDomains read,
                                                                     String field) {
        return read.noLineAt(RuleKey.of(field)).stream().map(FieldDomains.NoLine::why).toList();
    }

    private static FieldDomains readingOf(String type) {
        Compilation compilation = Compilation.ofSource(DECLARED, "Main");
        String module = compilation.modules().get(0);
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        assertNotNull(symbols, "the model under test compiles");
        TypeSymbol.AtModule named = TypeSymbols.declared(new TypeKey(module, type));
        assertNotNull(symbols.declaredNode(named.key()), "no `" + type + "` declared");
        return FieldDomains.of(named, RuleReadingContext.unshared(
                RuleReadings.of(compilation, module), ReadAs.THE_COMPILATION_DOES, TestDay.TODAY));
    }
}
