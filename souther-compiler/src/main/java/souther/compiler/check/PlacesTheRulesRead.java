package souther.compiler.check;

import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.LinkedHashSet;
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
        TypeView view = TypeView.of(value, source.inners(), source.symbols(), source.kinds(),
                source.sums());
        Set<RuleKey> out = new LinkedHashSet<>();
        for (TypeSymbol each : view.wrappers()) {
            readBy(each, source, out);
        }
        if (view.shape() instanceof Shape.Product product) {
            readBy(product.name(), source, out);
        }
        return new PlacesTheRulesRead(out);
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

    private static void readBy(TypeSymbol name, RuleReadingSource source, Set<RuleKey> out) {
        if (!(name instanceof TypeSymbol.AtModule declared)) {
            return;
        }
        for (ClauseMeaning clause : PublishedRules.governing(declared, source.published())
                .reached()) {
            if (clause instanceof ClauseMeaning.Stated stated) {
                for (ClauseRead read : stated.reads()) {
                    out.add(read.at());
                }
            }
        }
    }
}
