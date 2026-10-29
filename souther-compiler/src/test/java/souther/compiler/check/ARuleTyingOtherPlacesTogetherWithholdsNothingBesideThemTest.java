package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.inputs.BlockReason;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule the bounds cannot hold, naming several places no part ties to a place asked about, does
 * not withhold that place's run.
 *
 * <p>{@code String.contains(a, b)} relates two strings and no number. Where nothing ties {@code a}
 * or {@code b} to {@code total}, the values of the record are every pair of a value of the two
 * strings and a value of the rest, so what the rest leave {@code total} is what the record does —
 * once some {@code a} and {@code b} are shown to hold together. That is shown by a value of the
 * two written down that every rule naming either holds of, since a value of each alone may be one
 * a rule about the other refuses.
 */
class ARuleTyingOtherPlacesTogetherWithholdsNothingBesideThemTest {

    private static FieldDomains readingOf(String rules) {
        return readingOf("", rules);
    }

    private static FieldDomains readingOf(String declarations, String rules) {
        Compilation compilation = Compilation.ofSource("""
                module example.prices

                data Yen = Int
                    invariant value >= 0
                %s
                data Priced = { total: Yen, subtotal: Yen, a: String, b: String, c: String }
                    invariant total.value <= subtotal.value
                %s
                """.formatted(declarations, rules), "Main");
        String module = compilation.modules().get(0);
        TypeSymbol.AtModule named = TypeSymbols.declared(new TypeKey(module, "Priced"));
        return FieldDomains.of(named, RuleReadingContext.unshared(RuleReadings.of(compilation, module),
                ReadAs.THE_COMPILATION_DOES, TestDay.TODAY));
    }

    private static List<BlockReason.RuleWithoutLineReason> reasonsAtTotal(FieldDomains read) {
        return read.noLineAt(RuleKey.of("total")).stream().map(FieldDomains.NoLine::why).toList();
    }

    @Test
    void aRuleOverTwoStringsLeavesTheNumbersBesideThemRead() {
        FieldDomains read = readingOf("    invariant String.contains(a, b)");

        assertTrue(read.projectionAt(RuleKey.of("total")).isCertified(),
                () -> "nothing ties `a` or `b` to `total`: " + read.projectionAt(RuleKey.of("total")));
        assertEquals(List.of(new BlockReason.ComparisonRelatingTwoValues()), reasonsAtTotal(read));
        assertTrue(read.shownToHoldAValue(), "`a` and `b` empty hold every rule");
    }

    /** And whichever call relates the two, where what it answers is worked out at the values
     *  written down. */
    @Test
    void soDoesAPrefixOrASuffix() {
        for (String rule : List.of("String.startsWith(a, b)", "String.endsWith(a, b)")) {
            FieldDomains read = readingOf("    invariant " + rule);

            assertTrue(read.projectionAt(RuleKey.of("total")).isCertified(),
                    () -> rule + ": " + read.projectionAt(RuleKey.of("total")));
        }
    }

    /** And of three, each tied to the next. */
    @Test
    void soDoesAChainOfThem() {
        FieldDomains read = readingOf("""
                    invariant String.contains(a, b)
                    invariant String.contains(b, c)
                """);

        assertTrue(read.projectionAt(RuleKey.of("total")).isCertified(),
                () -> read.projectionAt(RuleKey.of("total")).toString());
    }

    /** And of places inside another field, written as a value of that field's declaration. */
    @Test
    void soDoesOneInsideAFieldOfItsOwnDeclaration() {
        Compilation compilation = Compilation.ofSource("""
                module example.prices

                data Yen = Int
                    invariant value >= 0

                data Pair = { a: String, b: String }
                    invariant String.contains(a, b)

                data Priced = { total: Yen, subtotal: Yen, pair: Pair }
                    invariant total.value <= subtotal.value
                """, "Main");
        String module = compilation.modules().get(0);
        FieldDomains read = FieldDomains.of(TypeSymbols.declared(new TypeKey(module, "Priced")),
                RuleReadingContext.unshared(RuleReadings.of(compilation, module),
                        ReadAs.THE_COMPILATION_DOES, TestDay.TODAY));

        assertTrue(read.projectionAt(RuleKey.of("total")).isCertified(),
                () -> read.projectionAt(RuleKey.of("total")).toString());
    }

    /**
     * Not where the places are tied to the one asked about through another.
     *
     * <p>{@code b} is no longer than {@code total}, so {@code a}, which {@code b} holds, ties
     * {@code total} to every rule about the two: what the strings refuse can refuse a total.
     */
    @Test
    void notWhereAPartTiesThemToThePlaceAskedAbout() {
        FieldDomains read = readingOf("""
                    invariant String.contains(a, b)
                    invariant String.length(b) <= total.value
                """);

        assertFalse(read.projectionAt(RuleKey.of("total")).isCertified(),
                () -> read.projectionAt(RuleKey.of("total")).toString());
    }

    /**
     * Nor where no value of the places together is shown, though one of each alone is.
     *
     * <p>{@code a} is {@code "A"} and {@code b} is {@code "B"}, which does not hold it: every rule
     * refuses no value of the place it names alone, and together they refuse every value. A record
     * with no value has no total to reach.
     */
    @Test
    void norWhereNoValueOfThemTogetherIsShown() {
        FieldDomains read = readingOf("""
                    invariant String.contains(a, b)
                    invariant String.matches("A", a)
                    invariant String.matches("B", b)
                """);

        assertFalse(read.projectionAt(RuleKey.of("total")).isCertified(),
                () -> read.projectionAt(RuleKey.of("total")).toString());
        assertFalse(read.shownToHoldAValue());
    }

    /**
     * Nor where the rule is one no value written down is shown to hold of.
     *
     * <p>What {@code String.lowercase} answers is not worked out here, so no value of the two is
     * shown to hold the rule, and nothing is said of what it refuses.
     */
    @Test
    void norWhereTheRuleIsNotWorkedOutAtAnyValue() {
        FieldDomains read = readingOf("    invariant String.contains(String.lowercase(a), b)");

        assertEquals(List.of(new BlockReason.RelationNotShownToReachEveryValue()),
                reasonsAtTotal(read));
    }
}
