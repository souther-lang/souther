package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Scopes;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.values.AdmissibleSet;
import souther.compiler.values.UnreadReason;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule that no two elements of a container share a key is read whole, and the containers it
 * admits are still not a set of values.
 *
 * <p>{@code List.allDistinctBy(.id, value)} leaves every list whose elements' {@code id}s are
 * pairwise apart. The builders of the position keep that ({@link ElementsApart}), so which values
 * may stand there is answered: the containers built with their keys apart, each element taking
 * every value. What the values reading holds there is every list, and that stays what it is — a
 * set holding the rule would hold two lists apart by what is inside them, which no set here does.
 *
 * <p>Only the rule as stated. Denied, it says some two elements share a key, which no builder
 * makes; as one alternative of a choice, keeping it refuses containers the choice admits; and a
 * key nothing here reads is a rule nobody told the builders. Each of those is still a rule nothing
 * took in.
 */
class ARuleKeepingElementsApartIsTakenInWholeTest {

    private static final String ITEM = """
            module demo

            data Item = { id: Int }
            """;

    private static FieldDomains read(String declaration) {
        Compilation compilation = Compilation.ofSource(ITEM + "\n" + declaration, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.diagnostics().values().stream()
                .flatMap(List::stream)
                .map(each -> each.diagnostic().code())
                .toList(), "the model this reads has to be one somebody could write");
        Symbols symbols = Scopes.derived(compilation.db(), "demo").value();
        TypeSymbol.AtModule name = TypeSymbols.declared(new TypeKey(symbols.module(), "N"));
        return FieldDomains.of(name, RuleReadingContext.unshared(RuleReadings.of(compilation, "demo"),
                ReadAs.THE_COMPILATION_DOES));
    }

    /** Every reason a question of a rule of this value was left with, in the values' words. */
    private static Set<UnreadReason> leftStanding(FieldDomains read) {
        return Set.copyOf(read.accounting().values().stream()
                .flatMap(each -> each.answers().values().stream())
                .filter(RuleAccounting.Outcome.Unaccounted.class::isInstance)
                .map(each -> ((RuleAccounting.Outcome.Unaccounted) each).why())
                .filter(RuleAccounting.Why.TheValueReadingSays.class::isInstance)
                .flatMap(each -> ((RuleAccounting.Why.TheValueReadingSays) each).why().stream())
                .toList());
    }

    /** Whether any question of any rule of this value went unanswered. */
    private static boolean anyUnaccounted(FieldDomains read) {
        return read.accounting().values().stream().anyMatch(each -> !each.unaccounted().isEmpty());
    }

    @Test
    void aRuleThatNoTwoElementsShareAKeyIsAccountedFor() {
        FieldDomains read = read("""
                data N = List<Item>
                    invariant List.allDistinctBy(.id, value)
                """);

        assertEquals(1, read.accounting().size(), "one clause, so one rule to account for");
        assertFalse(anyUnaccounted(read), "the builders keep the keys apart");
    }

    /** The two answers stay two: the rule was read whole, and the set of lists is not narrowed. */
    @Test
    void andTheValuesHeldThereAreNotClaimedToBeTheRule() {
        AdmissibleSet admits = read("""
                data N = List<Item>
                    invariant List.allDistinctBy(.id, value)
                """).admits(RuleKey.THE_VALUE);

        assertNotEquals(AdmissibleSet.READ_IN_FULL, admits.completeness(),
                "every list is not what the rule leaves, so the set holding it is not exact");
    }

    @Test
    void theSameOfARunOfFieldsOfARecord() {
        FieldDomains read = read("""
                data N = { items: List<Item> }
                    invariant List.allDistinctBy(.id, items)
                """);

        assertFalse(anyUnaccounted(read));
    }

    /** Beside a rule another reading takes in, each is answered by its own. */
    @Test
    void besideALengthEachIsTakenInByItsOwnReading() {
        FieldDomains read = read("""
                data N = List<Item>
                    invariant List.allDistinctBy(.id, value) && List.length(value) <= 3
                """);

        assertFalse(anyUnaccounted(read));
    }

    @Test
    void deniedItIsARuleNothingTookIn() {
        FieldDomains read = read("""
                data N = List<Item>
                    invariant Bool.not(List.allDistinctBy(.id, value))
                """);

        assertTrue(anyUnaccounted(read), "no builder makes two elements share a key");
        assertEquals(Set.of(UnreadReason.FORM_NOT_READ), leftStanding(read));
    }

    @Test
    void asOneAlternativeOfAChoiceItIsARuleNothingTookIn() {
        FieldDomains read = read("""
                data N = List<Item>
                    invariant List.allDistinctBy(.id, value) || List.length(value) >= 4
                """);

        assertTrue(anyUnaccounted(read),
                "a builder keeping the keys apart refuses lists of four the choice admits");
    }

    /**
     * Taken in exactly where the builders are told, which is the claim the reading makes. A choice
     * one alternative of which nobody can be in is read like a conjunction, and the builders still
     * stop at the {@code ||}: credited there, the rule is accounted for by containers nothing
     * composes apart.
     */
    @Test
    void theRuleIsTakenInExactlyWhereTheBuildersAreTold() {
        List<String> models = List.of(
                "List.allDistinctBy(.id, items) && n >= 0",
                "n >= 0 && (List.allDistinctBy(.id, items) || n < 0)",
                "(List.allDistinctBy(.id, items) || n < 0) && n >= 0",
                "List.allDistinctBy(.id, items) || (n < 0 && n > 0)",
                "{\n        let xs = items\n        List.allDistinctBy(.id, xs) && n >= 0\n    }");
        for (String rule : models) {
            FieldDomains read = read("""
                    data N = { n: Int, items: List<Item> }
                        invariant %s
                    """.formatted(rule));
            FieldDomains.Held held = read.heldAt(RuleKey.of("items"));
            boolean told = held != null && !held.keptApart().isEmpty();

            assertEquals(told, !anyUnaccounted(read), rule);
        }
        FieldDomains.Held control = read("""
                data N = { n: Int, items: List<Item> }
                    invariant List.allDistinctBy(.id, items) && n >= 0
                """).heldAt(RuleKey.of("items"));
        assertEquals(List.of(List.of("id")), control.keptApart(),
                "the conjunction tells the builders, so the pairing above is not two absences");
    }

    @Test
    void aKeyNothingHereReadsIsARuleNothingTookIn() {
        FieldDomains read = read("""
                data N = List<Item>
                    invariant List.allDistinctBy(x -> x.id + 1, value)
                """);

        assertTrue(anyUnaccounted(read), "the builders are told no such key");
        assertEquals(Set.of(UnreadReason.FORM_NOT_READ), leftStanding(read));
    }
}
