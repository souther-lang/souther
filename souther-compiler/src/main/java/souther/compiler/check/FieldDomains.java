package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.types.TypeName;

import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;

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
    public static final FieldDomains NONE =
            new FieldDomains(Map.of(), false, Map.of(), NumericDomain.top(), () -> Set.of());

    private final Map<String, NumericDomain.Bounds> byField;
    private final boolean infeasible;
    private final Map<String, String> atoms;
    private final NumericDomain numbers;
    private final Supplier<Set<String>> unread;
    private volatile Set<String> unreadPositions;

    private FieldDomains(Map<String, NumericDomain.Bounds> byField, boolean infeasible,
                         Map<String, String> atoms, NumericDomain numbers,
                         Supplier<Set<String>> unread) {
        this.byField = byField;
        this.infeasible = infeasible;
        this.atoms = atoms;
        this.numbers = numbers;
        this.unread = unread;
    }

    /**
     * Whether the rules contradict, so that no value of this type exists at all.
     *
     * <p>A separate answer from a field nothing bounds. Both leave no bounds to read, and one of them
     * means every position here holds anything while the other means none of them holds anything: a
     * report that took the second for the first would ask for rows at edges of a value nobody can
     * build.
     */
    public boolean infeasible() {
        return infeasible;
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
        return new FieldDomains(Map.copyOf(out), seeded.numbers().isBottom(),
                seeded.atoms(), seeded.numbers(),
                // Classifying the rules is a second reading of every one of them. Asked when the
                // answer is, and not before: a caller filling a row wants the bounds and nothing
                // else.
                () -> InvariantChecker.positionsWithARuleUnread(named, data, symbols));
    }

    /**
     * What the position at {@code path} can hold, or {@code null} where nothing bounds it either way.
     *
     * <p>{@code path} is read from the value these are of: {@code startsAt} for a field, and
     * {@code interval.startsAt} for a field of a field. A clause on the outer record relates
     * positions at any depth it can name, so what it leaves them is read at the depth it left it at
     * rather than at the record each of them happens to sit in.
     */
    public NumericDomain.Bounds at(String path) {
        return byField.get(path);
    }

    /**
     * Whether every rule of this value was taken into these bounds.
     *
     * <p>Asked of the value and not of one position in it, because what it licenses is existential: a
     * row at an edge is a whole value with that edge in it, and a rule about some other position can
     * refuse to be part of any such value. Two labels on one record that cannot both be written leave
     * every number beside them with edges nothing can reach, however plainly the numbers themselves
     * were read.
     *
     * <p>The narrower question — whether the bound at one position was derived losslessly — is a
     * different one and has no caller. It would say that a bound is approximate; this says whether
     * anything can be written at it, and only the second decides whether a row is owed.
     *
     * <p>Where this is false the bounds still hold: every value they exclude is truly excluded, and a
     * value they admit may be one nothing can build. What settles such an edge is a witness.
     */
    public boolean allRulesRead() {
        if (!numbers.projectionIsLossless()) {
            return false;
        }
        // A relation is only a projection where both ends brought their ranges. A type declared in
        // another module is read here in the form its operations have already been settled into, so
        // its bound never arrives — and a rule relating such a position to another narrows nothing
        // while the derivation puts the type's own edges back, which is an edge nobody can write
        // rather than a narrowing missed.
        if (atom != null && numbers.isRelated(atom) && numbers.boundsOf(atom).isEmpty()) {
            return false;
        }
        Set<String> positions = unreadPositions;
        if (positions == null) {
            positions = unread.get();
            unreadPositions = positions;
        }
        return positions.isEmpty();
    }
}
