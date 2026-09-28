package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.types.TypeSymbol;

import java.util.HashSet;
import java.util.Set;

/**
 * What one declaration settles before a count of the types it sits among begins.
 *
 * <p>Two facts, and each of them is about the declaration alone. The counts its rules ask a
 * collection to hold are what the answers of a count have to tell apart, so they decide the
 * lattice the count rises through and have to be in hand before it starts
 * ({@link CardinalityCuts}). Whether every rule of it could be read is what says a count that
 * stopped short may have missed the rule that empties a type.
 *
 * <p>A value, and that is what it is for. Reading a declaration's rules is the whole of what a
 * count pays per declaration, and a count is taken again whenever anything in the module it is
 * about is edited. Answered per declaration and compared by what it says, an edit that leaves a
 * declaration's rules where they were leaves this equal, and the declaration is not read again.
 *
 * <p>Counts read off the domain rather than off the clauses. A floor arrives in more ways than a
 * number written at the position, and a count missed here is precision lost and nothing else: the
 * answers still tell apart everything the questions found.
 *
 * <p>Both off one reading, because it is one reading. Split, a second walk would read the
 * declaration again wherever no lender is answering.
 */
public record CardinalityPremise(Set<Long> counts, boolean everyRuleReached) {

    /** Nothing asked and nothing missed — what a declaration with no rules of its own to read
     *  contributes, and what a name no declaration answers for contributes. */
    public static final CardinalityPremise NOTHING = new CardinalityPremise(Set.of(), true);

    public CardinalityPremise {
        counts = Set.copyOf(counts);
    }

    /**
     * What {@code declared} settles, read in {@code reading}.
     *
     * <p>A data is the only declaration with a rule to be short of: what the language declares
     * answers with the clauses it has, and a sum's cases are declarations of their own and are
     * reached as those.
     */
    public static CardinalityPremise of(TypeSymbol named, Hir.Def declared,
                                        RuleReadingContext reading) {
        if (!(declared instanceof Hir.Data data) || !(named instanceof TypeSymbol.AtModule at)) {
            return NOTHING;
        }
        InvariantChecker.Seeded read = InvariantChecker.seedFields(at, reading);
        OccurrenceCounts held = OccurrenceCounts.of(read);
        Set<Long> counts = new HashSet<>();
        for (RuleKey path : paths(data, at, reading.source())) {
            long least = held.leastHeldAt(path);
            if (least > 0) {
                counts.add(least);
            }
        }
        return new CardinalityPremise(counts, !read.clausesNotExpanded());
    }

    /**
     * Where a rule of {@code data} can ask a collection to hold anything: the value of a newtype,
     * which is at no name of its own, and every field of anything else.
     *
     * <p>The fields asked of the source rather than walked here. What a declaration reaches through
     * its spreads is what the reading below is about to be given, so walking them again is the same
     * walk made twice — and where a compilation answers for the walk, the second one is made past
     * the answer.
     */
    private static Set<RuleKey> paths(Hir.Data data, TypeSymbol.AtModule at,
                                      RuleReadingSource source) {
        if (data.newtype()) {
            return Set.of(RuleKey.THE_VALUE);
        }
        Set<RuleKey> paths = new HashSet<>();
        for (String field : source.fieldTypes().of(at).keySet()) {
            paths.add(RuleKey.of(field));
        }
        return paths;
    }
}
