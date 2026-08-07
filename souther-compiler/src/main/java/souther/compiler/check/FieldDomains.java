package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.types.TypeName;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * What a record leaves each of its fields able to hold.
 *
 * <p>Not what the field's own type admits. A clause relating two fields — {@code startsAt < endsAt} —
 * is a rule about pairs, and what one field can hold is that rule projected onto it: with both ends
 * of a day bounded at 1440, {@code startsAt} stops at 1439, because a 1440 would need an
 * {@code endsAt} the day has no room for. Reading the field's type alone names values the record
 * refuses.
 *
 * <p>The projection is exact over the clauses the numeric domain could take, and only over those.
 * {@link #exact} says whether that was all of them: a clause outside the fragment — a call, a
 * pattern, a sum of three terms — narrows nothing here, so where one is present these bounds are
 * wider than what the declaration actually says. Wide is the safe direction for deciding a value is
 * impossible, and the wrong direction for deciding that the edge of the range can be written, which
 * is why the two answers are handed over together.
 */
public final class FieldDomains {

    /** Nothing known of any field. */
    public static final FieldDomains NONE = new FieldDomains(Map.of(), true);

    private final Map<String, NumericDomain.Bounds> byField;
    private final boolean exact;

    private FieldDomains(Map<String, NumericDomain.Bounds> byField, boolean exact) {
        this.byField = byField;
        this.exact = exact;
    }

    /** What {@code data}, declared as {@code named}, leaves its fields able to hold. */
    public static FieldDomains of(TypeName named, Ast.Data data, Symbols symbols) {
        if (data.newtype()) {
            return NONE;   // a newtype's value is the same position it is; there are no siblings
        }
        InvariantChecker.Seeded seeded = InvariantChecker.seedFields(named, data, symbols);
        Map<String, NumericDomain.Bounds> out = new LinkedHashMap<>();
        seeded.atoms().forEach((field, atom) -> {
            NumericDomain.Bounds bounds = seeded.numbers().boundsOf(atom);
            if (!bounds.isEmpty()) {
                out.put(field, bounds);
            }
        });
        return new FieldDomains(Map.copyOf(out),
                seeded.everyClauseRead() && seeded.numbers().everythingIsProjectable());
    }

    /** What {@code field} can hold, or {@code null} where nothing bounds it either way. */
    public NumericDomain.Bounds at(String field) {
        return byField.get(field);
    }

    /**
     * Whether every rule the declaration states was taken into these bounds.
     *
     * <p>Where this is false the bounds are an over-approximation: every value they exclude is truly
     * excluded, and a value they admit may still be one nothing can build.
     */
    public boolean exact() {
        return exact;
    }
}
