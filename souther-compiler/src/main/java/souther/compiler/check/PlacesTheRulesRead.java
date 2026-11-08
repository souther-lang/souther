package souther.compiler.check;

import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * The places the rules a value is held to read, as those rules name them.
 *
 * <p>The rules and not the value. A record with a field under a sum's cases has a place there
 * whether or not a rule says anything of it, and what a reader building a value asks is the
 * second: whether some rule reads under a place, so that a value built whole there would be built
 * without it. The places are what each declaration publishes its clauses as reading
 * ({@link ClauseMeaning.Stated#reads}), read once for every name the value wears — a name wrapping
 * a record names the record's fields as the record does, so their places are named alike.
 *
 * <p>A clause published with no form says nothing here. Nothing can build a value to hold a rule
 * this compiler cannot read, so a reader told it reads nowhere builds the value as it would have,
 * and the clause is the run-time check's to answer.
 *
 * @param at every place some clause reads
 */
public record PlacesTheRulesRead(Set<RuleKey> at) {

    public PlacesTheRulesRead {
        at = Set.copyOf(at);
    }

    /** No rule, so no place read. */
    public static final PlacesTheRulesRead NONE = new PlacesTheRulesRead(Set.of());

    /**
     * The places the rules of every name {@code value} wears read, and of the record it is.
     *
     * <p>Every name, because each is a declaration whose rules the value is held to — which is why
     * this reads them all rather than one.
     */
    public static PlacesTheRulesRead of(Type value, RuleReadingSource source) {
        Set<RuleKey> out = new LinkedHashSet<>();
        for (ClauseRead read : readsOf(value, source)) {
            out.add(read.at());
        }
        return new PlacesTheRulesRead(out);
    }

    /**
     * Every member a clause of a name {@code value} wears, or of the record it is, cannot be true
     * without its container holding ({@link ClauseRead.Kind#A_MEMBER_THE_CLAUSE_NEEDS}), where
     * what is looked for is a place of the value: each read naming its member.
     */
    public static List<ClauseRead> membersNeeded(Type value, RuleReadingSource source) {
        return readsOf(value, source).stream().filter(read -> read.member().isPresent()).toList();
    }

    /** What every clause of every name {@code value} wears, and of the record it is, reads, each
     *  read once. */
    private static List<ClauseRead> readsOf(Type value, RuleReadingSource source) {
        TypeView view = TypeView.of(value, source.inners(), source.symbols(), source.kinds(),
                source.sums());
        List<TypeSymbol> names = new ArrayList<>(view.wrappers());
        if (view.shape() instanceof Shape.Product product) {
            names.add(product.name());
        }
        Set<ClauseRead> out = new LinkedHashSet<>();
        for (TypeSymbol each : names) {
            if (!(each instanceof TypeSymbol.AtModule declared)) {
                continue;
            }
            for (ClauseMeaning clause : PublishedRules.governing(declared, source.published())
                    .reached()) {
                if (clause instanceof ClauseMeaning.Stated stated) {
                    out.addAll(stated.reads());
                }
            }
        }
        return List.copyOf(out);
    }

    /** Whether some clause reads a place strictly under {@code key}. */
    public boolean readUnder(RuleKey key) {
        for (RuleKey each : at) {
            if (!each.equals(key) && each.isAtOrUnder(key)) {
                return true;
            }
        }
        return false;
    }
}
