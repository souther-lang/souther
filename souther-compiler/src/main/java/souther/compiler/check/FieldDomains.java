package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Granularity;
import souther.compiler.types.TypeName;
import souther.compiler.types.ValueName;
import souther.compiler.types.Type;

import souther.compiler.numeric.Count;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
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
 * <p>The bounds are as wide as what the rules could be read as, and only that. {@link #allRulesRead}
 * says whether that was all of them: a clause outside the fragment — a call, a pattern, a sum of
 * three terms — narrows nothing here, so where one is present these bounds admit values nothing can
 * build. Wide is the safe direction for deciding a value is impossible and the wrong direction for
 * deciding that an edge can be written, which is why the two answers are handed over together.
 */
public final class FieldDomains {

    /**
     * Where a newtype's own value sits, which is where the newtype sits.
     *
     * <p>A name worn is not a step of the path ({@link Location#isStep}), so the value under one is
     * at no path of its own and its fields are the first step there is. Spelled here rather than as
     * {@code ""} at each caller, which reads as a path nobody meant.
     */
    public static final String THE_VALUE = "";

    /** Nothing known of any field. */
    public static final FieldDomains NONE =
            new FieldDomains(Map.of(), Map.of(), List.of(), Map.of(), false, true,
                    NumericDomain.top(), null, null, null, Map.of(), () -> true);

    private final Map<String, NumericDomain.Bounds> byField;
    /** The ends the record's own clauses place, which is a different question from the range they
     * leave — see {@link #placedAt}. */
    private final List<InvariantChecker.Direct> directs;
    /** Which declarations relate each coordinate to something else, and so could have moved where it
     * stops — see {@link #narrowedBy}. */
    private final Map<String, List<TypeName>> narrowers;
    /** What each field has to hold, kept apart from what each field is. Same numbers, different
     * question — see {@link Held}. */
    private final Map<String, NumericDomain.Bounds> heldByField;
    private final boolean infeasible;
    /** Whether the reading that produced these bounds ran to the end. Kept because it is what that
     * reading knows about itself: a walk that fell over produces the same empty domain as a value
     * with no rules, and a second reading asked afterwards does not take the same path. */
    private final boolean seeded;
    private final NumericDomain numbers;
    /** What this was read from, so that it can be read again without one declaration's clauses. */
    private final TypeName named;
    private final Ast.Data data;
    private final Symbols symbols;
    private final Map<String, Count> settled;
    private final java.util.function.BooleanSupplier reading;
    private volatile Boolean everyRuleRead;

    private FieldDomains(Map<String, NumericDomain.Bounds> byField,
                         Map<String, NumericDomain.Bounds> heldByField,
                         List<InvariantChecker.Direct> directs,
                         Map<String, List<TypeName>> narrowers, boolean infeasible,
                         boolean seeded, NumericDomain numbers, TypeName named, Ast.Data data,
                         Symbols symbols, Map<String, Count> settled,
                         java.util.function.BooleanSupplier reading) {
        this.byField = byField;
        this.heldByField = heldByField;
        this.directs = directs;
        this.narrowers = narrowers;
        this.infeasible = infeasible;
        this.seeded = seeded;
        this.numbers = numbers;
        this.named = named;
        this.data = data;
        this.symbols = symbols;
        this.settled = settled;
        this.reading = reading;
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
                                  Map<String, Count> settled) {
        return of(named, data, symbols, settled, _ -> false);
    }

    /** The same, with one declaration's own clauses left out — see {@link #narrowedBy}. */
    private static FieldDomains of(TypeName named, Ast.Data data, Symbols symbols,
                                   Map<String, Count> settled,
                                   java.util.function.Predicate<TypeName> without) {
        // A newtype is read the same way, and only its bounds are not worth handing back: its value
        // is the same position it is, so there are no siblings to relate. Everything else is the same
        // question — its own rules can hold a hole no range keeps, and they can contradict, and both
        // answers were being given away by treating it as a value with nothing to say.
        InvariantChecker.Seeded seeded =
                InvariantChecker.seedFields(named, data, symbols, settled, without);
        Map<String, NumericDomain.Bounds> out = new LinkedHashMap<>();
        seeded.atoms().forEach((field, atom) -> {
            // The value itself is at no path, and its range is the one thing not worth handing back:
            // it is the same position this is of, so there is no sibling to relate it to. What sits
            // under it is another matter — a record inside a newtype has fields, and they are
            // positions with ranges like any other.
            if (field.isEmpty()) {
                return;
            }
            NumericDomain.Bounds bounds = seeded.numbers().boundsOf(atom);
            if (!bounds.isEmpty()) {
                out.put(field, bounds);
            }
        });
        // Resolved here rather than handed over as atoms. An atom is a name the seeding gave a shape
        // and means nothing once the reading that named it is gone, so a caller holding one could
        // only ask the domain it came from — which is this one, while it is still here.
        Map<String, NumericDomain.Bounds> holds = new LinkedHashMap<>();
        seeded.held().forEach((field, atom) -> {
            if (field.isEmpty()) {
                return;
            }
            NumericDomain.Bounds bounds = seeded.numbers().boundsOf(atom);
            if (!bounds.isEmpty()) {
                holds.put(field, bounds);
            }
        });
        // Classifying the rules is a second reading of every one of them, and the bounds are the
        // whole of what a caller filling a row needs. Asked when the answer is, and not before.
        return new FieldDomains(Map.copyOf(out), Map.copyOf(holds), seeded.reading().directs(),
                seeded.reading().narrowers(), seeded.numbers().isBottom(),
                seeded.everyClauseRead(), seeded.numbers(), named, data, symbols, settled,
                // Classifying the rules is a second reading of every one of them. Asked when the
                // answer is, and not before: a caller filling a row wants the bounds and nothing
                // else.
                () -> InvariantChecker.everyRuleRead(named, data, symbols));
    }

    /**
     * An end one clause of this record places on one coordinate of it, and the declaration that
     * placed it.
     *
     * <p>Not a bound the range happens to have. {@link #at} answers what a position can hold, which
     * every rule reaching it takes part in; this answers which clause said where it stops, which only
     * a clause naming that one coordinate and a constant does. A line may be drawn at one of these
     * and at nothing else (ADR-0090), so handing back the range instead would make a relational rule
     * into a partition of a position it never mentioned.
     *
     * @param path     where the coordinate sits, read from the value these are of
     * @param measured whether the coordinate is a count taken of the position rather than its value
     * @param from     the declaration the clause is written on, which is what names the line
     * @param lower    whether this bounds the coordinate below; otherwise above
     */
    public record Placed(String path, boolean measured, TypeName from, boolean lower, Endpoint end) {}

    /**
     * The declaration whose clause could have moved where the coordinate at {@code path} stops, or
     * null where none did.
     *
     * <p>Which declaration wrote the relation, and not which value the position sits in. The same
     * relation can be written on the record, on a record inside it, or on a name wrapped round
     * either, and an edge said to have been taken in by a declaration holding no clause about the
     * pair sends a reader to a line that is not there.
     *
     * <p>Several where several hold it, in one order whoever found them. Which of them settled the
     * number is not always a question this can answer — a bound arrives along a path through the
     * differences and clauses can reach an end only together — and where it cannot, the set is what
     * is known and is handed over as it is.
     */
    public List<TypeName> narrowedBy(String path, boolean lower) {
        List<TypeName> candidates = narrowers.get(path);
        if (candidates == null || candidates.isEmpty()) {
            return List.of();
        }
        NumericDomain.Bounds here = byField.get(path);
        Endpoint end = here == null ? null : lower ? here.min() : here.max();
        if (end == null) {
            return List.of();
        }
        // Which of them is holding this end, asked by taking each away. A candidate is a declaration
        // that wrote a relation about this coordinate, which is not the same as one that decided
        // where it stops: a second relation reaching a value the first has already passed changes
        // nothing, and naming it would make an edge's identity turn on a clause that moved it
        // nowhere.
        List<TypeName> held = new ArrayList<>();
        for (TypeName each : candidates) {
            if (!ends(end, without(each::equals), path, lower)) {
                held.add(each);
            }
        }
        if (!held.isEmpty()) {
            return byName(held);
        }
        // None on its own: two or more of them say what the edge says, and taking away any one
        // leaves the others saying it. Which is not a reason to name one — each is as much the
        // answer as the others — and not a reason to name all of them either. A candidate that
        // moves this end nowhere when it is the only one left moved it nowhere here, and it is out
        // whatever the rest of them are doing.
        Endpoint bare = endOf(without(candidates::contains), path, lower);
        List<TypeName> saying = new ArrayList<>();
        for (TypeName each : candidates) {
            if (!ends(bare, without(name -> candidates.contains(name) && !name.equals(each)),
                    path, lower)) {
                saying.add(each);
            }
        }
        return byName(saying.isEmpty() ? candidates : saying);
    }

    /** In one order, whoever found them. Several of these are one answer and the answer is what a
     * line is told apart by, so an order read off the walk that collected them would make two
     * readings of one edge into two lines. */
    private static List<TypeName> byName(List<TypeName> found) {
        return found.stream().sorted(java.util.Comparator.comparing(TypeName::name)).toList();
    }

    private Endpoint endOf(FieldDomains read, String path, boolean lower) {
        NumericDomain.Bounds bounds = read.byField.get(path);
        return bounds == null ? null : lower ? bounds.min() : bounds.max();
    }

    /** Whether {@code end} is where {@code other} leaves this coordinate on the side asked for. */
    private boolean ends(Endpoint end, FieldDomains other, String path, boolean lower) {
        return java.util.Objects.equals(end, endOf(other, path, lower));
    }

    /** This value read again without the clauses of the declarations {@code skip} names. */
    private FieldDomains without(java.util.function.Predicate<TypeName> skip) {
        return of(named, data, symbols, settled, skip);
    }

    /** Every end the rules place, wherever it is. */
    public List<Placed> placed() {
        return directs.stream()
                .map(each -> new Placed(each.path(), each.measured(), each.from(),
                        each.bound().lower(), each.bound().end()))
                .toList();
    }

    /** The ends the rules place on the coordinates at {@code path}, in the order they were read. */
    public List<Placed> placedAt(String path) {
        return placed().stream().filter(each -> each.path().equals(path)).toList();
    }

    /**
     * Whether the rules leave the value at {@code path} in {@code data} able to hold nothing.
     *
     * <p>Asked of the domain the rules seed rather than read off the clauses. A rule removes the
     * empty value in more ways than a floor written at the position: {@code List.length(kids.value)}
     * counts the same thing under another spelling, {@code >= least} beside {@code least >= 1} says
     * it through a second field, and an equality says it without stating an end a range would keep.
     * Reading the clauses for the shapes one reader thought of leaves the rest of them saying
     * nothing, and there is no end to the shapes. The seeding already relates all of them, so the
     * question goes there: settle the count at none and see whether anything is left.
     *
     * <p>Both the record's rules and the field's own type's reach the same domain — the seeding puts
     * each field's type in beside the clauses — so this is one reading and not two agreeing.
     *
     * <p>Yes where the seeding could not read the rules, and yes where the position is counted by
     * nothing. Wide is the safe direction: what this decides is that a recursion has nowhere to
     * bottom out, and a reader that guessed would refuse a type somebody can write.
     *
     */
    public static boolean mayHoldNothingAt(TypeName named, Ast.Data data, String path,
                                           Symbols symbols) {
        InvariantChecker.Seeded seeded = InvariantChecker.seedFields(named, data, symbols);
        String counted = seeded.held().get(path);
        if (counted == null) {
            return true;   // nothing counts what is there, so no rule here is about how much it holds
        }
        NumericDomain.LinearForm none = NumericDomain.LinearForm.atom(counted);
        // A count is never below none, so leaving it no room above none is leaving it at none.
        return !seeded.numbers()
                .assume(none, NumericDomain.Rel.LE, Map.of(counted, Granularity.DISCRETE))
                .isBottom();
    }

    /**
     * How much a value at a position has to hold, which is not what the value there is.
     *
     * <p>Its own type because the numbers are the same numbers. {@code >= 2} at a field is a range of
     * that field's values where the field is a number, and a count of what it holds where a rule
     * counts it — and a caller handed a bare {@link NumericDomain.Bounds} has nothing to stop it
     * reading one as the other. There is one such mistake in this already: the atom a size rule
     * bounds is the size's, and writing it under the field is how a list would come to be told it
     * must be at least 2.
     */
    public record Held(NumericDomain.Bounds bounds) {

        public Held {
            if (bounds == null) {
                throw new IllegalArgumentException("a floor with no bounds is no floor");
            }
        }
    }

    /**
     * What the rules say the value at {@code path} holds, or {@code null} where they count it in no
     * way this read.
     *
     * <p>Read off the measure the position's own type names ({@link NumericMeasures#takenOf}), so a
     * field this can answer for is one whose values are counted by something. A field of a number has
     * no such measure and is answered by {@link #at} instead; the two never speak about one field.
     */
    public Held heldAt(String path) {
        NumericDomain.Bounds bounds = heldByField.get(path);
        return bounds == null ? null : new Held(bounds);
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
        // What the reading that made these bounds knows about itself comes first. A second reading
        // asked afterwards walks the declarations and not the same path, so it can come back clean
        // about a projection that was never computed.
        if (!seeded || !numbers.projectionIsLossless()) {
            return false;
        }
        Boolean read = everyRuleRead;
        if (read == null) {
            read = reading.getAsBoolean();
            everyRuleRead = read;
        }
        return read;
    }
}
