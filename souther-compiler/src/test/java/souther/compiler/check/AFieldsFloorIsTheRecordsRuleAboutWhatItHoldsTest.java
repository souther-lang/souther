package souther.compiler.check;

import souther.compiler.query.Scopes;
import souther.compiler.numeric.Count;
import souther.compiler.query.Compilation;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.TypeSymbol;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;

import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How much a field has to hold, where the record it sits in is what says so.
 *
 * <p>A rule counting a field — {@code List.length(xs) >= 2} — bounds the count and not the field, so
 * it reaches the domain under an atom of its own and a reader asking what the field can hold is told
 * nothing. That is a different question from {@link FieldDomains#at}, which answers what the value at
 * a position is, and the two are kept apart here because the same numbers stand for different things.
 */
class AFieldsFloorIsTheRecordsRuleAboutWhatItHoldsTest {

    private static FieldDomains domainsIn(String source, String type) {
        return domainsIn(source, type, java.util.Map.of());
    }

    private static FieldDomains domainsIn(String source, String type,
                                          java.util.Map<RuleKey, Count> settled) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        assertNotNull(symbols, "the model did not compile");
        TypeSymbol.AtModule named = TypeSymbols.declared(new TypeKey(module, type));
        assertNotNull(symbols.declaredNode(named.key()), "no `" + type + "` in " + module);
        return FieldDomains.of(named, RuleReadings.of(compilation, module),
                souther.compiler.query.ReadAs.THE_COMPILATION_DOES, settled);
    }

    private static final String AGAINST_A_SIBLING = """
            module example.bag

            data Bag =
                { n: Int
                , xs: List<Int>
                }
                invariant enough = List.length(xs) >= n
            """;

    /** A rule counting one field against another asks for nothing in particular until something says
     * what the other is: a count is never negative, and that is the whole of what is left of the
     * rule while {@code n} is open. */
    @Test
    void aFloorStatedAgainstASiblingAsksForNothingWhileTheSiblingIsOpen() {
        FieldDomains.Held held = domainsIn(AGAINST_A_SIBLING, "Bag").heldAt(RuleKey.of("xs"));

        assertNotNull(held, "a count of no less than none is still what the domain holds");
        assertEquals(0, BigDecimal.ZERO.compareTo(Count.number(held.bounds().min().at()).at()),
                "and none of them is a list any value meets");
    }

    /**
     * And is one once the sibling is settled, which is what settling a field is for.
     *
     * <p>The same projection {@link FieldDomains#at} has always made of a number beside a settled
     * number, asked of how much a value holds. A caller reading this without the settled fields gets
     * the answer above — no floor — for a position that has one.
     */
    @Test
    void aFloorStatedAgainstASettledSiblingIsAFloor() {
        FieldDomains.Held held = domainsIn(AGAINST_A_SIBLING, "Bag",
                java.util.Map.of(RuleKey.of("n"), Count.of(7L))).heldAt(RuleKey.of("xs"));

        assertNotNull(held, "seven is what the list has to hold once n is seven");
        assertEquals(0, BigDecimal.valueOf(7).compareTo(Count.number(held.bounds().min().at()).at()));
    }

    @Test
    void aRecordsCountRuleIsWhatItsFieldHasToHold() {
        FieldDomains domains = domainsIn("""
                module example.bag

                data Bag =
                    { xs: List<Int>
                    }
                    invariant atLeastTwo = List.length(xs) >= 2
                """, "Bag");

        FieldDomains.Held held = domains.heldAt(RuleKey.of("xs"));
        assertNotNull(held, "the record says how much the list holds");
        assertEquals(0, BigDecimal.valueOf(2).compareTo(Count.number(held.bounds().min().at()).at()),
                "two, which is what the rule counts");
        assertTrue(held.bounds().min().inclusive(), "and a list of two is one the rule admits");
    }

    /**
     * A field is in one of the two answers or in neither, and never in both.
     *
     * <p>The numbers are the same numbers, so a caller that could get both from one field would be a
     * caller that has to decide which of them a bound is about. What settles it is the position's own
     * type: a number is its own value and a list is counted by how much of it there is.
     */
    @Test
    void aFieldIsEitherANumberOrSomethingCountedAndNotBoth() {
        FieldDomains domains = domainsIn("""
                module example.mixed

                data Mixed =
                    { n: Int
                    , xs: List<Int>
                    }
                    invariant bigEnough = n >= 5
                    invariant atLeastTwo = List.length(xs) >= 2
                """, "Mixed");

        assertNotNull(domains.at(RuleKey.of("n")), "a number is bounded as the value it is");
        assertNull(domains.heldAt(RuleKey.of("n")), "and nothing counts what a number holds");
        assertNotNull(domains.heldAt(RuleKey.of("xs")),
                "a list is bounded by how much of it there is");
        assertNull(domains.at(RuleKey.of("xs")).bounds(), "and a list is no number to bound");
    }

}
