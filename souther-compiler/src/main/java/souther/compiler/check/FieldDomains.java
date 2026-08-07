package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.types.TypeName;

import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.function.BooleanSupplier;

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
    public static final FieldDomains NONE = new FieldDomains(Map.of(), () -> true);

    private final Map<String, NumericDomain.Bounds> byField;
    private final BooleanSupplier deriving;
    private Boolean exact;

    private FieldDomains(Map<String, NumericDomain.Bounds> byField, BooleanSupplier deriving) {
        this.byField = byField;
        this.deriving = deriving;
    }

    /** What {@code data}, declared as {@code named}, leaves its fields able to hold. */
    public static FieldDomains of(TypeName named, Ast.Data data, Symbols symbols) {
        return of(named, data, symbols, Map.of());
    }

    /**
     * The same, with some fields already settled at a value.
     *
     * <p>Projecting a range and completing an assignment are two questions of one rule set. A row at
     * {@code startsAt = 1439} needs an {@code endsAt} the record will accept beside it, and that is
     * not read off {@code endsAt}'s own range — which still runs from 1 — but off what is left of it
     * once the other end is fixed, which is 1440 and nothing else.
     */
    public static FieldDomains of(TypeName named, Ast.Data data, Symbols symbols,
                                  Map<String, BigDecimal> settled) {
        if (data.newtype()) {
            return NONE;   // a newtype's value is the same position it is; there are no siblings
        }
        InvariantChecker.Seeded seeded = InvariantChecker.seedFields(named, data, symbols, settled);
        Map<String, NumericDomain.Bounds> out = new LinkedHashMap<>();
        seeded.atoms().forEach((field, atom) -> {
            NumericDomain.Bounds bounds = seeded.numbers().boundsOf(atom);
            if (!bounds.isEmpty()) {
                out.put(field, bounds);
            }
        });
        // Classifying the rules is a second reading of every one of them, and the bounds are the
        // whole of what a caller filling a row needs. Asked when the answer is, and not before.
        return new FieldDomains(Map.copyOf(out),
                () -> seeded.everyClauseRead() && seeded.numbers().everythingIsProjectable()
                        && InvariantChecker.everyRuleIsDerivable(named, data, symbols));
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
        if (exact == null) {
            exact = deriving.getAsBoolean();
        }
        return exact;
    }
}
