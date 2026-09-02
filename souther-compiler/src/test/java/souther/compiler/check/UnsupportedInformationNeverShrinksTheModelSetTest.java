package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Scopes;
import souther.compiler.ast.Hir;
import souther.compiler.query.Compilation;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a clause nothing could read is allowed to do to the answers a refusal rests on.
 *
 * <p>These readings decide that a type has no value, and a type said to have none is refused. So a
 * clause the seeding could not take in has to leave more values in than there are and may never leave
 * fewer out: dropping what was not understood widens the answer, and widening never refuses.
 *
 * <p>Held here rather than beside the check that consumes them, because it is the reading and not the
 * check that has to keep this. A rule added to the seeding that narrows on a guess would turn a
 * report with a row missing — which is what these answers cost today elsewhere — into a program
 * refused for having no value it can be shown to lack.
 *
 * <p>Each model is paired with one whose rules the seeding does read, so that an answer of "may" is
 * known to be the reading's and not the absence of anything to read.
 */
class UnsupportedInformationNeverShrinksTheModelSetTest {

    private static Hir.Data data(Compilation compilation, String name) {
        for (Hir.Def def : compilation.module("demo").defs().stream().map(each -> each.declaration().node()).toList()) {
            if (def instanceof Hir.Data found && found.name().equals(name)) {
                return found;
            }
        }
        throw new IllegalArgumentException("no such declaration: " + name);
    }

    private static FieldDomains domainsOf(String source, String name) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        Symbols symbols = Scopes.derived(compilation.db(), "demo").value();
        return FieldDomains.of(TypeSymbols.declared(new TypeKey(symbols.module(), name)),
                data(compilation, name), RuleReadings.of(compilation, "demo"),
                souther.compiler.query.ReadAs.THE_COMPILATION_DOES);
    }

    private static OccurrenceCounts countsOf(String source, String name) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        Symbols symbols = Scopes.derived(compilation.db(), "demo").value();
        return OccurrenceCounts.of(TypeSymbols.declared(new TypeKey(symbols.module(), name)),
                data(compilation, name), RuleReadings.of(compilation, "demo"),
                souther.compiler.query.ReadAs.THE_COMPILATION_DOES);
    }

    /** Two clauses that cannot both hold, both of them read. */
    @Test
    void rulesThatContradictLeaveNoValue() {
        assertTrue(domainsOf("""
                module demo

                data X = Int
                    invariant low = value >= 2
                    invariant high = value <= 1
                """, "X").infeasible(), "nothing is both at least two and at most one");
    }

    /**
     * The same contradiction as one side of a disjunction the other side settles. Read a disjunction
     * as though its first term were the rule and this type loses its only value.
     */
    @Test
    void aClauseWithAValuelessSideStillHasItsOtherSide() {
        assertFalse(domainsOf("""
                module demo

                data Seven = Int
                    invariant either = (value >= 2 && value <= 1) || value == 7
                """, "Seven").infeasible(), "seven is a value of it");
    }

    /** A floor the seeding reads, so the count at the name a set wears is one it can answer about. */
    @Test
    void aFloorLeavesNoRoomBelowIt() {
        OccurrenceCounts counts = countsOf("""
                module demo

                data Pair = Set<Int>
                    invariant two = Set.size(value) >= 2
                """, "Pair");
        assertFalse(counts.mayHoldAtMost(RuleKey.THE_VALUE, 1), "two will not fit in one");
        assertFalse(counts.mayHoldExactly(RuleKey.THE_VALUE, 0), "nor in none");
        assertTrue(counts.mayHoldAtLeast(RuleKey.THE_VALUE, 2), "and two is what it asks for");
    }

    /**
     * The same floor as one side of a disjunction whose other side is the empty set. The count has to
     * come back open at none, because the rule as written admits it.
     */
    @Test
    void aFloorWithAWayRoundItIsNoFloor() {
        OccurrenceCounts counts = countsOf("""
                module demo

                data Loose = Set<Int>
                    invariant either = Set.size(value) >= 2 || Set.size(value) == 0
                """, "Loose");
        assertTrue(counts.mayHoldAtMost(RuleKey.THE_VALUE, 0), "the empty set is one of these");
        assertTrue(counts.mayHoldAtMost(RuleKey.THE_VALUE, 1), "and so is nothing smaller");
        assertTrue(counts.mayHoldExactly(RuleKey.THE_VALUE, 0), "asked the other way as well");
    }

    /** A position no rule counts answers yes to every count, having nothing to say about any. */
    @Test
    void aPositionNothingCountsAdmitsEveryCount() {
        OccurrenceCounts counts = countsOf("""
                module demo

                data Bare = Set<Int>
                """, "Bare");
        assertTrue(counts.mayHoldAtMost(RuleKey.THE_VALUE, 0));
        assertTrue(counts.mayHoldExactly(RuleKey.THE_VALUE, 5));
        assertTrue(counts.mayHoldAtLeast(RuleKey.THE_VALUE, 5));
    }
}
