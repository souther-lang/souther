package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.types.TypeSymbol;
import souther.compiler.values.AdmissibleSet;
import souther.compiler.values.AdmissibleValues;
import souther.compiler.values.UnreadReason;
import souther.compiler.values.ValueSet;

import souther.compiler.numeric.Count;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Optional;
import java.util.SequencedMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What a record leaves each of its fields able to hold.
 *
 * <p>Not what the field's own type admits. A clause relating two fields — {@code startsAt < endsAt} —
 * is a rule about pairs, and what one field can hold is that rule projected onto it: with both ends
 * of a day bounded at 1440, {@code startsAt} stops at 1439, because a 1440 would need an
 * {@code endsAt} the day has no room for. Reading the field's type alone names values the record
 * refuses.
 *
 * <p>The bounds are as wide as what the rules could be read as, and only that. {@link #projection}
 * says how much of them that was: a clause outside the fragment — a call, a pattern, a sum of three
 * terms — narrows nothing here, so where one is present these bounds admit values nothing can build.
 * Wide is the safe direction for deciding a value is impossible and the wrong direction for deciding
 * that an edge can be written, which is why the two answers are handed over together.
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

    /** No position anywhere, for the reading that reached none. Unmodifiable, as every other part
     * of {@link #NONE} is: a shared constant handing out a map anybody could add to is a value one
     * caller can change under the rest. */
    private static final SequencedMap<FactSubject, String> NO_POSITIONS =
            java.util.Collections.unmodifiableSequencedMap(new LinkedHashMap<>());

    /**
     * Nothing known of any field.
     *
     * <p>Which is not the same as a value with nothing written about it, and answers as the first:
     * no clause of anything was gathered here, so {@link #admits} says of every position that the
     * reading never reached the rules about it ({@link UnreadReason#NOT_REACHED}). A caller holding
     * this holds it because it chose not to read a declaration or had none to read, and neither of
     * those is a reading that found no rules.
     */
    public static final FieldDomains NONE =
            new FieldDomains(Map.of(), Map.of(), Map.of(), Map.of(), List.of(), List.of(), Map.of(),
                    new ReadingEvidence(), Map.of(), Set.of(THE_VALUE), NO_POSITIONS,
                    ConstraintState.top(), null, null, null, Map.of(), Set.of(THE_VALUE), Map.of(),
                    Map.of(), Map.of(), List.of());

    private final Map<String, NumericDomain.Bounds> byField;
    /** The ends the record's own clauses place, which is a different question from the range they
     * leave — see {@link #placedAt}. */
    private final List<InvariantChecker.Direct> directs;
    /** The rules saying where a coordinate's values stop that no end came out of — see
     * {@link #unreadAt}. */
    private final List<Unread> unread;
    /** What each clause reaching this value raises, keyed on the rule it is. */
    private final Map<RuleRef, Required> raised;
    /** Which readings took each clause in, as each of them said so. */
    private final ReadingEvidence took;
    /** The accounting, worked out once. Every position of a value asks the same question of it. */
    private volatile Map<RuleRef, RuleAccounting> accounting;
    /** Which declarations relate each coordinate to something else, and so could have moved where it
     * stops — see {@link #narrowedBy}. */
    private final Map<String, List<TypeSymbol>> narrowers;
    /** What each field has to hold, kept apart from what each field is. Same numbers, different
     * question — see {@link Held}. */
    private final Map<String, NumericDomain.Bounds> heldByField;
    /** Which values each position may hold — see {@link #admits}. */
    private final Map<String, ValueSet> admittedByField;
    /** What stopped the reading from speaking for a position, for the ones it could not speak for.
     * A position not here is one the reading took every rule about into the set — see
     * {@link #admits}. */
    private final Map<String, UnreadReason> unreadByField;
    /** Where a clause of this value did not reach the readings at all, as the paths the stops
     * happened at — see {@link #admits}. */
    private final Set<String> notGathered;
    /** And of those, the positions a construction has to make a value at. What a position admits is
     *  short wherever a rule about it went unread; whether an edge of it may be promised is about
     *  what every value of this has to satisfy, and a rule inside an optional is not that. */
    private final Set<String> unreadOfEveryValue;
    /** Where each position of this value sits, in the order the value declares them. What a domain
     * holds is what a reading called a position; which place in the value that is, is known here. */
    private final SequencedMap<FactSubject, String> positions;
    /** Everything the clauses were read as, kept whole. Whether any value of this exists is a
     * question about all of it and is asked of it; the numbers are read out of it where a bound is
     * what a caller is after. */
    private final ConstraintState constraints;
    /** What this was read from, so that it can be read again without one declaration's clauses. */
    private final TypeSymbol named;
    private final Hir.Data data;
    private final Symbols symbols;
    private final Map<String, Count> settled;
    /** The atom a range is taken of at each position: the position's own value, and the count of
     *  one where a count is taken. A position with neither has no range to be exact about. */
    private final Map<String, FactSubject> atomAt;
    private final Map<String, FactSubject> countAt;
    /** The atoms the reading that builds the bounds was handed a form for, per part of each rule.
     *  Per part, because a rule is represented where every part of it is. */
    private final Map<RuleRef, Map<Core, Set<FactSubject>>> narrowedBy;
    /** What the interval algebra dropped at the step it dropped it, and what it was handed there.
     *  Whether the projection ends up holding the rule all the same is asked of the state it ends
     *  in — see {@link #projection}. */
    private final List<InvariantChecker.Dropped> lost;

    private FieldDomains(Map<String, NumericDomain.Bounds> byField,
                         Map<String, NumericDomain.Bounds> heldByField,
                         Map<String, ValueSet> admittedByField,
                         Map<String, UnreadReason> unreadByField,
                         List<InvariantChecker.Direct> directs, List<Unread> unread,
                         Map<RuleRef, Required> raised, ReadingEvidence took,
                         Map<String, List<TypeSymbol>> narrowers,
                         Set<String> notGathered,
                         SequencedMap<FactSubject, String> positions,
                         ConstraintState constraints, TypeSymbol named,
                         Hir.Data data, Symbols symbols, Map<String, Count> settled,
                         Set<String> unreadOfEveryValue,
                         Map<String, FactSubject> atomAt, Map<String, FactSubject> countAt,
                         Map<RuleRef, Map<Core, Set<FactSubject>>> narrowedBy,
                         List<InvariantChecker.Dropped> lost) {
        this.byField = byField;
        this.heldByField = heldByField;
        this.admittedByField = admittedByField;
        this.unreadByField = unreadByField;
        this.directs = directs;
        this.unread = unread;
        this.raised = raised;
        this.took = took;
        this.narrowers = narrowers;
        this.notGathered = notGathered;
        this.positions = positions;
        this.constraints = constraints;
        this.named = named;
        this.data = data;
        this.symbols = symbols;
        this.settled = settled;
        this.unreadOfEveryValue = unreadOfEveryValue;
        this.atomAt = atomAt;
        this.countAt = countAt;
        this.narrowedBy = narrowedBy;
        this.lost = lost;
    }

    /**
     * Whether the rules contradict, so that no value of this type exists at all.
     *
     * <p>A separate answer from a field nothing bounds. Both leave no bounds to read, and one of them
     * means every position here holds anything while the other means none of them holds anything: a
     * report that took the second for the first would ask for rows at edges of a value nobody can
     * build.
     *
     * <p>Asked of the whole state and not of the numbers in it. A rule reaches whichever domain has
     * a word for it, so a contradiction can be held entirely by a domain that has nothing to do with
     * intervals — and a reading that asked the numbers alone answered that a value exists because
     * the domain it asked had never heard of the rules.
     */
    public boolean infeasible() {
        return constraints.isBottom();
    }

    /**
     * Why the rules leave no value, or empty where they may leave one.
     *
     * <p>{@link #infeasible} with the answer instead of the fact. Asked of the same state and never
     * assembled beside it: a caller reading one of them and deciding the other for itself would have
     * two accounts of one reading to keep in step.
     *
     * <p>The places are this value's, in the order it declares them. What a state holds is what its
     * readings call a position, and where in the value that sits is known here and nowhere else.
     */
    public Optional<Emptiness> holdsNothing() {
        return constraints.holdsNothing(positions);
    }

    /** What {@code data}, declared as {@code named}, leaves its fields able to hold. */
    public static FieldDomains of(TypeSymbol named, Hir.Data data, Symbols symbols) {
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
    public static FieldDomains of(TypeSymbol named, Hir.Data data, Symbols symbols,
                                  Map<String, Count> settled) {
        return of(named, data, symbols, settled, InvariantChecker.Reach.EVERYTHING);
    }

    /**
     * The same, with the declarations {@code granted} names supposed to hold values.
     *
     * <p>What a reader asking "would this hold anything if that one did" needs. A value said to have
     * none is one whose rules say so, and those rules are read wherever it is reached — its own and
     * the ones under whatever it wraps — so supposing it has a value is not reading it at all. A
     * record holding it is otherwise told it holds nothing by the very rules the supposing was
     * about.
     */
    static FieldDomains granting(TypeSymbol named, Hir.Data data, Symbols symbols,
                                 java.util.function.Predicate<TypeSymbol> granted) {
        return of(named, data, symbols, Map.of(), InvariantChecker.Reach.stoppingAt(granted));
    }

    /** The same, reading only as far as {@code reach} says — see {@link #narrowedBy}. */
    private static FieldDomains of(TypeSymbol named, Hir.Data data, Symbols symbols,
                                   Map<String, Count> settled,
                                   InvariantChecker.Reach reach) {
        // A newtype is read the same way, and only its bounds are not worth handing back: its value
        // is the same position it is, so there are no siblings to relate. Everything else is the same
        // question — its own rules can hold a hole no range keeps, and they can contradict, and both
        // answers were being given away by treating it as a value with nothing to say.
        InvariantChecker.Seeded seeded =
                InvariantChecker.seedFields(named, data, symbols, settled, reach);
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
            if (!bounds.saysNothing()) {
                out.put(field, bounds);
            }
        });
        // Which values each position may hold, resolved onto paths for the same reason the bounds
        // are. Every position and not only the fields: what a name wraps is at no path of its own,
        // and it is the position a reader of a newtype asks about.
        Map<String, ValueSet> admitted = new LinkedHashMap<>();
        Map<String, UnreadReason> unread = new LinkedHashMap<>();
        // Every position that answers to either name. A number is called one thing by the interval
        // algebra and another by everything else, and the two are filed as they are found — so a
        // reading keyed by one of the maps would leave a position held only by the other answering
        // from a default, which is the widest thing there is to say and is said about a position a
        // clause may well have narrowed.
        Set<String> positions = new LinkedHashSet<>(seeded.keys().keySet());
        positions.addAll(seeded.atoms().keySet());
        positions.forEach(field -> {
            AdmissibleValues<FactSubject> values = seeded.constraints().values();
            // Both names of the position, since a number has one of each and a clause reaching it
            // is filed under whichever the reading recognised. Both are about the same values, so
            // what holds of it is what both leave.
            ValueSet here = ValueSet.ANY;
            UnreadReason why = null;
            for (FactSubject name : named(seeded, field)) {
                here = here.meet(values.at(name));
                // The first that stopped it. Two names of one position are two ways the same rules
                // were filed, so a second reason is another account of a position already known to
                // be short of its rules rather than a further thing wrong with it.
                if (why == null) {
                    why = values.whyUnread(name);
                }
            }
            admitted.put(field, here);
            if (why != null) {
                unread.put(field, why);
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
            if (!bounds.saysNothing()) {
                holds.put(field, bounds);
            }
        });
        // Classifying the rules is a second reading of every one of them, and the bounds are the
        // whole of what a caller filling a row needs. Asked when the answer is, and not before.
        // Every name a position answers to, filed under the place it sits at, in the order the
        // value declares its positions. A proof that names a place is settled by this order: read
        // off a domain's own map, the place named would be the one whose clause was read first.
        //
        // The order is the walk's, and the walk's is the declaration's. `positions` is the keys
        // followed by the atoms, and that is the keys: an atom is named from a body key, so a
        // position with an atom has a key and the second pass adds nothing. A size has no key and
        // is not one of these — it is a number taken of a position rather than a position.
        SequencedMap<FactSubject, String> placeOf = new LinkedHashMap<>();
        positions.forEach(field ->
                named(seeded, field).forEach(term -> placeOf.putIfAbsent(term, field)));
        return new FieldDomains(Map.copyOf(out), Map.copyOf(holds), Map.copyOf(admitted),
                Map.copyOf(unread), seeded.reading().directs(), seeded.reading().unread(),
                seeded.reading().raised(), seeded.took(), seeded.reading().narrowers(),
                seeded.notGathered(), placeOf,
                seeded.constraints(), named, data, symbols, settled,
                seeded.unreadOfEveryValue(), seeded.atoms(), seeded.held(),
                seeded.narrowedBy(), seeded.lost());
    }

    /**
     * An end one clause of this record places on one coordinate of it, and the rule that placed
     * it.
     *
     * <p>Not a bound the range happens to have. {@link #at} answers what a position can hold, which
     * every rule reaching it takes part in; this answers which clause said where it stops, which only
     * a clause naming that one coordinate and a constant does. A line may be drawn at one of these
     * and at nothing else (ADR-0090), so handing back the range instead would make a relational rule
     * into a partition of a position it never mentioned.
     *
     * @param path     where the coordinate sits, read from the value these are of
     * @param measured whether the coordinate is a count taken of the position rather than its value
     * @param from     the rule that placed the end, which is what names the line. An invariant's,
     *                 and said so: these are the ends the clauses of a declaration place, and no
     *                 other kind of rule reaches this reading
     * @param lower    whether this bounds the coordinate below; otherwise above
     */
    public record Placed(String path, boolean measured, RuleRef.Invariant from,
                         boolean lower, Endpoint end) {}

    /**
     * A rule about where one coordinate's values stop that this reading placed no end from, and
     * what stopped it.
     *
     * <p>The other half of {@link Placed} and produced by the same reading of the same clause, which
     * is what keeps the two from disagreeing about what a rule is. Read by a walk of its own, a
     * second reader answered for the clauses on a position's own type and knew nothing of the ones
     * written on the value it sits in — so a clause of a record was dropped without a word while a
     * {@code guard} of the same shape named both the positions it compared (ADR-0090).
     *
     * <p>One per position the rule names, since a rule relating two coordinates is filed under
     * neither of them alone.
     *
     * @param path where the coordinate sits, read from the value these are of
     * @param from the rule that says where the values stop, which is what a reader is sent to look
     *             at
     * @param why  what would have to change before this rule could be a line, in this compiler's
     *             own terms
     */
    public record Unread(String path, RuleRef.Invariant from,
                         souther.compiler.inputs.BlockReason why) {}

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
    public List<TypeSymbol> narrowedBy(String path, boolean lower) {
        List<TypeSymbol> candidates = narrowers.get(path);
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
        List<TypeSymbol> held = new ArrayList<>();
        for (TypeSymbol each : candidates) {
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
        List<TypeSymbol> saying = new ArrayList<>();
        for (TypeSymbol each : candidates) {
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
    private static List<TypeSymbol> byName(List<TypeSymbol> found) {
        return found.stream().sorted(java.util.Comparator.comparing(TypeSymbol::name)).toList();
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
    private FieldDomains without(java.util.function.Predicate<TypeSymbol> skip) {
        return of(named, data, symbols, settled, InvariantChecker.Reach.withoutClausesOf(skip));
    }

    /**
     * What each clause reaching this value raises, keyed on the rule it is.
     *
     * <p>Questions and not answers. A clause is here whether or not anything took it in, which is
     * what makes it a list of what has to be settled rather than a list of what this compiler
     * managed — the second is what a completeness written per reader amounts to, and it says the
     * model was read in full for exactly as long as nobody adds a reader.
     */
    public Map<RuleRef, Required> required() {
        return raised;
    }

    /**
     * Every rule reaching this value, every question it raises, and what answered each.
     *
     * <p>The questions come from the rules and the answers from whichever reading took the rule in.
     * Which is the whole arrangement: an ordering bound and an equality raise the same question
     * about which values may stand at a position, and it is answered by the reading of ends in the
     * first case and by the reading of values in the second — so a completeness read off either
     * reading alone reports a model that was read in full as one this compiler could not read.
     */
    public Map<RuleRef, RuleAccounting> accounting() {
        Map<RuleRef, RuleAccounting> had = accounting;
        if (had != null) {
            return had;
        }
        Map<RuleRef, RuleAccounting> out = new LinkedHashMap<>();
        raised.forEach((rule, required) ->
                out.put(rule,
                        RuleAccounting.of(rule, required, owed -> answered(rule, owed))));
        // Insertion order, which is the order the declaration writes its clauses. `Map.copyOf`
        // iterates in an order salted once per JVM run, and these reach a checked-in document.
        accounting = java.util.Collections.unmodifiableMap(out);
        return accounting;
    }

    /** What answered one question of one rule. */
    private RuleAccounting.Outcome answered(RuleRef rule, Owed owed) {
        return switch (owed.obligation()) {
            case ADMITTED_VALUES -> admissionAnswered(rule, owed.subject());
            // Raised only where an end was read off the rule, so the reading that raised it is the
            // one that answered it.
            case BOUNDARY ->
                    new RuleAccounting.Outcome.Accounted(RuleAccounting.Reader.THE_END_READING);
        };
    }

    /**
     * What answered "which values may stand here" for one rule at one position.
     *
     * <p>Any reading that took the rule in will do, and that is the whole of it. A question is
     * unanswered exactly where no reading adopted the clause — not where the reading that names the
     * question was short of the position's rules, which is a fact about that reading and is true at
     * every numeric position an invariant bounds.
     *
     * <p>Asked per rule and never per position. One clause's failure is not the account of the
     * clause beside it: {@code value >= 1} leaves the reading of values short at a position, and
     * {@code value == 7} written beside it was taken in whole.
     */
    private RuleAccounting.Outcome admissionAnswered(RuleRef rule, Owed.Subject where) {
        List<FactSubject> named = named(where.path());
        // A part of the rule nothing took in outranks everything else about it. An end placed by
        // one conjunct is not an account of the conjunct written beside it.
        if (took.anyLeftStanding(rule, named)) {
            return new RuleAccounting.Outcome.Unaccounted(
                    unreadByField.getOrDefault(where.path(), UnreadReason.FORM_NOT_READ));
        }
        // The reading that turns this clause into where the values stop, said by the end it placed.
        if (directs.stream()
                .anyMatch(d -> d.from().equals(rule) && d.path().equals(where.path()))) {
            return new RuleAccounting.Outcome.Accounted(RuleAccounting.Reader.THE_END_READING);
        }
        // And the readings that hold what a clause says about the values themselves, each said by
        // that reading at the point it adopted the clause.
        if (took.tookIn(rule, named)) {
            return new RuleAccounting.Outcome.Accounted(RuleAccounting.Reader.THE_VALUE_READING);
        }
        UnreadReason why = unreadByField.get(where.path());
        return new RuleAccounting.Outcome.Unaccounted(
                why == null ? UnreadReason.FORM_NOT_READ : why);
    }

    /** Every name the position at {@code path} answers to. */
    private java.util.List<FactSubject> named(String path) {
        return positions.entrySet().stream().filter(e -> e.getValue().equals(path))
                .map(Map.Entry::getKey).toList();
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
     * The rules about where the coordinates at {@code path} stop that no end came out of, in the
     * order they were read.
     *
     * <p>Beside {@link #placedAt} and not instead of it. A position carries more than one
     * statement, so a rule here says nothing about whether an end was placed at the same position
     * and an end there says nothing about this — read as one answer, a bound on a field's own type
     * silenced the record's clause about the same field.
     */
    public List<Unread> unreadAt(String path) {
        return unread.stream().filter(each -> each.path().equals(path)).toList();
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
    public static boolean mayHoldNothingAt(TypeSymbol named, Hir.Data data, String path,
                                           Symbols symbols) {
        // A count is never below none, so leaving it no room above none is leaving it at none.
        return OccurrenceCounts.of(named, data, symbols).mayHoldAtMost(path, 0);
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
     * Which values the position at {@code path} may hold, and how much of its rules was read.
     *
     * <p>{@link ValueSet#ANY} where the rules leave it open, which is also what a position nothing
     * was written about comes to — told apart from a position this could not read by the
     * completeness beside it, which is why the two are handed over as one value
     * ({@link AdmissibleSet}).
     *
     * <p>{@code path} is read from the value these are of, as {@link #at} is, and what a name wraps
     * is at {@link #THE_VALUE}. A range is not handed back there and this is: a newtype's value is
     * the position the newtype is, so it is the position a reader of one asks about.
     *
     * <p>The position's own reason comes first where there is one. A rule written about this
     * position that could not be read is what an author would act on; that the gathering stopped
     * somewhere else in the value is true as well and is the coarser of the two.
     */
    public AdmissibleSet admits(String path) {
        ValueSet values = admittedByField.getOrDefault(path, ValueSet.ANY);
        UnreadReason here = unreadByField.get(path);
        if (here != null) {
            return AdmissibleSet.partial(values, here);
        }
        // A clause that never reached the readings cannot have spoiled the position it was about,
        // because no reading here ever saw which position that was. A walk that fell over and a
        // clause nothing could type are both that, and both leave maps that read exactly like a
        // value with no rules — so what the gathering knows about itself is asked, rather than
        // guessed from the maps being empty.
        //
        // Not `projection`, which is what the bounds state of the rules. A clause the interval
        // algebra holds nothing of may be one this reading took in whole, so borrowing that answer
        // would settle this reading's completeness by a reading that is not this one.
        return everyRuleReachedAt(path) ? AdmissibleSet.complete(values)
                : AdmissibleSet.partial(values, UnreadReason.NOT_REACHED);
    }

    /**
     * Whether the gathering reached whatever rules are written about the position at {@code path}.
     *
     * <p>A stop reaches the position it happened at and everything under it, and no further. A rule
     * that narrows a position names it, and a clause written inside one field names no position
     * outside that field — so a walk that declined to enter a regex-bounded code has said nothing
     * about the plain {@code Int} beside it.
     *
     * <p>A stop at {@link #THE_VALUE} is different in kind and is why the paths are compared rather
     * than counted: the declaration's own clause can name any position of it, so a clause of it
     * that never arrived leaves every position short of its rules.
     *
     * <p>Asked here rather than read off what a reading came back short of. A position can be both
     * — a rule that arrived and could not be read, beside a subtree the walk never entered — and
     * {@link #admits} answers with the first of the two because it has one slot to answer in, so
     * reach taken from there is lost wherever another reason won it. A caller that wants to know
     * whether anything is out of sight wants this.
     */
    public boolean everyRuleReachedAt(String path) {
        for (String stopped : notGathered) {
            if (stopped.equals(THE_VALUE) || path.equals(stopped)
                    || path.startsWith(stopped + ".")) {
                return false;
            }
        }
        return true;
    }

    /** Both names the position at {@code path} answers to. A number has one of each and everything
     * else has the second, and a clause is filed under whichever the reading recognised. */
    private static List<FactSubject> named(InvariantChecker.Seeded seeded, String path) {
        List<FactSubject> names = new ArrayList<>();
        FactSubject atom = seeded.atoms().get(path);
        if (atom != null) {
            names.add(atom);
        }
        FactSubject key = seeded.keys().get(path);
        if (key != null) {
            names.add(key);
        }
        return names;
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
     * What every rule reaching this value leaves the position at {@code path}, the value's own
     * position included.
     *
     * <p>A different question from {@link #at}, which is what the value a position sits in projects
     * onto it — a sibling's business, and a newtype's value has no siblings, which is why that one
     * has nothing to say about it. This is where the position stops once everything written about it
     * has been taken in, and a caller that has to know where a line actually falls wants this: a
     * clause placing an end at 0 beside one that takes the 0 away leaves a position whose first
     * value is 1, and the end as written is not where the position starts.
     */
    public NumericDomain.Bounds leftAt(String path, boolean measured) {
        // The axis the caller is on, and not whichever of the two this position happens to have. A
        // `String` is measured two ways — its own order, and the length of it — and answering with
        // the wrong one clamps a line drawn on one axis by the range of the other.
        FactSubject atom = measured ? countAt.get(path) : atomAt.get(path);
        return atom == null ? null : constraints.numbers().boundsOf(atom);
    }

    /**
     * How much of what the rules say these bounds are able to state.
     *
     * <p>Asked of the value and not of one position in it, because what it licenses is existential:
     * a row at an edge is a whole value with that edge in it, and a rule about some other position
     * can refuse to be part of any such value. Two labels on one record that cannot both be written
     * leave every number beside them with edges nothing can reach, however plainly the numbers
     * themselves were read.
     *
     * <p>Read off the reading that made the bounds and not off a second walk of the declarations.
     * A walk classifying each rule by its shape asks what could have become a bound, which is an
     * answer about this compiler's interval algebra wearing the model's words — and it went on
     * saying a rule was unread where the algebra had taken it in whole.
     *
     * <p>Where this is not exact the bounds still hold: every value they exclude is truly excluded,
     * and a value they admit may be one nothing can build. What settles such an edge is a witness.
     */
    public ProjectionEvidence projection() {
        List<ProjectionEvidence.Cause> causes = new ArrayList<>();
        // A rule that never arrived first. Which rule it was is not known here and there is nothing
        // to say: what a stop leaves is a position and everything under it.
        for (String stopped : unreadOfEveryValue) {
            causes.add(new ProjectionEvidence.Cause.Unavailable(stopped));
        }
        // Every position of this value, by the atom a range of it is taken under. A rule that
        // narrowed one of these is in the bounds; a rule that narrowed only an atom standing for an
        // arithmetic this cannot carry narrowed nothing anybody reads off them.
        Set<FactSubject> ranged = new LinkedHashSet<>(atomAt.values());
        ranged.addAll(countAt.values());
        // Asked of every rule the reading was handed, and not of the questions the rules raise. A
        // pattern raises none — which values may stand somewhere and where a line falls are not what
        // it is about — and it is still a way the value can be refused at an edge of the number
        // beside it.
        narrowedBy.forEach((rule, byPart) -> {
            // A part at a time, and any one of them is enough. A conjunct the bounds hold nothing of
            // leaves the range wider than the rule however well the conjunct written beside it went,
            // and a set unioned over the whole clause answers for the failing half with the other
            // one — which is the same shape as reading a clause's evidence for one of its parts.
            Set<String> said = new LinkedHashSet<>();
            byPart.forEach((part, narrowable) -> {
                // A conjunction says what its conjuncts say, and they are here beside it. Asked of
                // the conjunction as well, a rule whose halves are each held in a language of their
                // own — a date bounded at both ends, read by the comparison rather than by the
                // interval algebra — answers for neither half and fails on the node above them.
                if (part instanceof Core.Binary b && b.op() == Hir.BinOp.AND
                        && byPart.containsKey(b.left()) && byPart.containsKey(b.right())) {
                    return;
                }
                if (narrowable.stream().anyMatch(ranged::contains)) {
                    return;
                }
                // Or the end this part placed, which is the same part in the bounds said by the
                // other reading of it: an ordered value that is not a number takes its range from
                // the comparison rather than from the interval algebra, and counting only the
                // algebra calls a bounded `Date` a rule the bounds do not hold — and takes every
                // boundary beside it down with it.
                if (directs.stream().anyMatch(d -> d.part() == part)) {
                    return;
                }
                // What the rule is about, where it raised a question naming a position. A rule that
                // raises none is about the value it is written on, which is the empty path.
                Required required = raised.get(rule);
                if (required != null) {
                    required.obligations().forEach(owed -> said.add(owed.subject().path()));
                }
                if (said.isEmpty()) {
                    said.add(THE_VALUE);
                }
            });
            said.forEach(path ->
                    causes.add(new ProjectionEvidence.Cause.Unrepresented(rule, path)));
        });
        // And what the algebra was given and the state it ended in does not hold. A loss is a fact
        // about the step it happened at: `value /= 0` written before `value >= 1` drops a hole that
        // the bound put outside the range a clause later, and the projection has no hole in it.
        // Read off the step, the same two rules answer one way in one order and another in the
        // other.
        for (InvariantChecker.Dropped dropped : lost) {
            boolean held = !dropped.stated().isEmpty() && dropped.stated().stream().allMatch(
                    each -> constraints.numbers().entails(each.form(), each.rel()));
            if (!held) {
                causes.add(new ProjectionEvidence.Cause.Lossy(
                        dropped.rule(), dropped.atom(), dropped.losses()));
            }
        }
        return causes.isEmpty() ? new ProjectionEvidence.Exact()
                : new ProjectionEvidence.Approximate(causes);
    }

}
