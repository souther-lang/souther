package souther.compiler.proof;

import souther.compiler.core.TheWalk;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.semantics.SideAnswered;
import souther.compiler.semantics.Unsayable;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Function;

/**
 * Statements about the operations the library writes in the language, proved against their bodies.
 *
 * <p>Two rules, and the reading both stand on ({@link Reading}). Where the body walks nothing, the
 * statement is what the body comes to, case by case, read through the laws of what it calls. Where
 * the body walks a list, what the walk carries is stated with the lemma ({@link Lemma#carries}) and
 * proved by induction over the list: it holds of where the walk starts, with nothing walked, and a
 * step from where it holds — what is carried and the part walked so far — ends where it holds of
 * what the step answers and the part walked one element further. Where the walk ends, the part
 * walked is the whole list, and what it holds of there is what the statement is shown from.
 *
 * <p>Each step follows, or does not, as {@link Validity} finds, given what is stated of kernels
 * beside one another wherever the values it is about are made by them ({@link Library#relations}).
 * A statement holding of every value is taken of the values a step is about and shown of one that
 * stands for any. Nothing here knows any operation's name, and nothing is taken of another operation
 * but a law it was handed as settled or a relation stated of a kernel.
 */
public final class LibraryProver {

    /** What proving a statement came to. */
    public sealed interface Outcome {

        /** It is proved, as {@code proof} says. */
        record Proved(Proof proof) implements Outcome {}

        /** What the body comes to is something the domain has no words for, for {@code why}. */
        record Unsaid(Unsayable why) implements Outcome {}

        /** It is not proved, for {@code why}. */
        record Open(Unproved why) implements Outcome {}
    }

    /** How deep relations are taken of the values relations name. */
    private static final int RELATED = 2;

    /** How many values a statement holding of every value is taken of, at most. */
    private static final int TAKEN_OF = 8;

    private final Library library;
    private final Set<ValueName.Stdlib.Operation> readThrough;

    /**
     * @param readThrough the operations whose bodies are read where they are called: the walks the
     *                    library writes as another walk over what they were handed
     */
    public LibraryProver(Library library, Set<ValueName.Stdlib.Operation> readThrough) {
        this.library = library;
        this.readThrough = Set.copyOf(readThrough);
    }


    /** Whether {@code lemma}, a statement about {@code operation}, is proved against its body. */
    public Outcome prove(ValueName.Stdlib.Operation operation, Lemma lemma) {
        Reading reading = new Reading(library, readThrough);
        try {
            List<Value> params = arguments(operation);
            List<Reading.Case> cases = reading.cases(reading.bodyOf(operation),
                    new Reading.Frame(params, Map.of()));
            Set<Value.Made> walks = new LinkedHashSet<>();
            cases.forEach(each -> walksIn(each.is(), walks));
            Induction induction = null;
            if (!walks.isEmpty()) {
                if (lemma.carries().isEmpty()) {
                    return new Outcome.Open(new Unproved.NoInvariantGiven());
                }
                if (walks.size() != 1) {
                    return new Outcome.Open(new Unproved.NotOverItsArguments());
                }
                induction = new Induction(operation, lemma.carries(), reading, params,
                        walks.iterator().next());
                if (!induction.overItsArguments()) {
                    return new Outcome.Open(new Unproved.NotOverItsArguments());
                }
                Failed failed = induction.prove();
                if (failed != null) {
                    return outcomeOf(failed, reading);
                }
            }
            Failed failed = stated(operation, lemma.states(), cases, reading, params, induction);
            if (failed != null) {
                return outcomeOf(failed, reading);
            }
            Set<Proof.Used> used = reading.used();
            return new Outcome.Proved(walks.isEmpty() ? new Proof.ByTheBody(operation, used)
                    : new Proof.ByInduction(operation, lemma.carries(), used));
        } catch (Reading.Stopped stopped) {
            return stoppedAt(stopped);
        }
    }

    /**
     * Whether the number {@code operation} answers stands as {@code states} says to {@code other},
     * a number of its arguments by place, wherever {@code where} holds of them — a bound on what it
     * answers, or, stated as equal to an argument, that it answers that argument there.
     */
    public Outcome answers(ValueName.Stdlib.Operation operation, Rel states,
                           LinearForm<LawNumber<Integer>> other, LawProposition<Integer> where) {
        Reading reading = new Reading(library, readThrough);
        try {
            List<Value> params = arguments(operation);
            LawProposition<Value> given = reading.proposition(where, operation, params);
            LinearForm<LawNumber<Value>> than = reading.form(other, operation, params);
            for (Reading.Case each : reading.cases(reading.bodyOf(operation),
                    new Reading.Frame(params, Map.of()))) {
                LawProposition<Value> goal = Props.compared(reading.number(each.is()), states,
                        than);
                if (!follows(reading, List.of(given, each.when()), goal,
                        spacing(operation, Map.of()))) {
                    return outcomeOf(new Failed(Unproved.Obligation.THE_CASES, goal), reading);
                }
            }
            return new Outcome.Proved(new Proof.ByTheBody(operation, reading.used()));
        } catch (Reading.Stopped stopped) {
            return stoppedAt(stopped);
        }
    }

    /**
     * Whether how many {@code operation} answers holds is {@code size}, a number of its arguments,
     * wherever {@code proved} — a statement of its answer beside what others answer, proved of its
     * body — holds: the two say one thing, in other words, and nothing of the body is read again.
     */
    public boolean sizeFollows(ValueName.Stdlib.Operation operation,
                               LinearForm<LawNumber<Integer>> size, LawProposition<Slot> proved) {
        // One about its arguments and its answer alone: a statement of every value, or of a walk,
        // says something else.
        boolean[] another = {false};
        Collect.slots(proved, slot -> another[0] |= !(slot instanceof Slot.Place
                || slot instanceof Slot.Answer));
        if (another[0]) {
            return false;
        }
        Reading reading = new Reading(library, readThrough);
        try {
            List<Value> params = arguments(operation);
            Value answer = new Value.Made(operation, params);
            LawProposition<Value> given = reading.proposition(
                    TheAnswer.named(proved, operation, params.size()), operation,
                    slot -> switch (slot) {
                        case Slot.Place(int position) -> params.get(position);
                        case Slot.Answer _ -> answer;
                        case Slot.Every _, Slot.Carried _, Slot.Walked _ -> null;
                    }, Reading.Elements.none());
            return follows(reading, List.of(given), Props.compared(
                    LinearForm.atom(new LawNumber.SizeOf<>(new LawSubject.Argument<>(answer))),
                    Rel.EQ, reading.form(size, operation, params)), spacing(operation, Map.of()));
        } catch (Reading.Stopped stopped) {
            return false;
        }
    }

    /**
     * Whether {@code holds}, a statement about what {@code operation} answers beside what it was
     * handed and what kernels answer, is proved against its body: of every case the body answers
     * by, where a walk in the body ends as one of {@code carries} says it carries.
     *
     * <p>The statement names the answer as the operation's answer handed its own arguments, which
     * is how it is read where the operation is called; here that answer is what the body comes to.
     * Each of {@code carries} is a statement of what the walk carries, proved on its own of where
     * the walk starts and of each step; the first under which the statement follows is the proof.
     */
    public Outcome relates(ValueName.Stdlib.Operation operation, LawProposition<Slot> holds,
                           List<List<LawProposition<Slot>>> carries) {
        LawProposition<Slot> statement = TheAnswer.named(holds, operation,
                library.takes(operation).size());
        Outcome last = new Outcome.Open(new Unproved.NoInvariantGiven());
        for (List<LawProposition<Slot>> carried : walking(carries)) {
            Reading reading = new Reading(library, readThrough);
            try {
                List<Value> params = arguments(operation);
                List<Reading.Case> cases = reading.cases(reading.bodyOf(operation),
                        new Reading.Frame(params, Map.of()));
                Set<Value.Made> walks = new LinkedHashSet<>();
                cases.forEach(each -> walksIn(each.is(), walks));
                if (walks.size() > 1) {
                    return new Outcome.Open(new Unproved.NotOverItsArguments());
                }
                List<Universal> ends = List.of();
                if (!walks.isEmpty()) {
                    if (carried.isEmpty()) {
                        continue;
                    }
                    Induction induction = new Induction(operation, carried, reading, params,
                            walks.iterator().next());
                    if (!induction.overItsArguments()) {
                        return new Outcome.Open(new Unproved.NotOverItsArguments());
                    }
                    Failed failed = induction.prove();
                    if (failed != null) {
                        last = outcomeOf(failed, reading);
                        continue;
                    }
                    ends = induction.whereItEnds();
                }
                Failed failed = null;
                for (Reading.Case each : cases) {
                    LawProposition<Value> goal = reading.proposition(statement, operation,
                            slot -> switch (slot) {
                                case Slot.Place(int position) -> params.get(position);
                                case Slot.Answer _ -> each.is();
                                case Slot.Every(int which) -> new Value.Fresh(100 + which,
                                        "any value");
                                case Slot.Carried _, Slot.Walked _ -> throw new IllegalStateException(
                                        "a statement about an answer names no walk");
                            }, Reading.Elements.none());
                    if (!follows(reading, List.of(each.when()), ends, goal,
                            spacing(operation, Map.of()))) {
                        failed = new Failed(Unproved.Obligation.THE_STATEMENT, goal);
                        break;
                    }
                }
                if (failed == null) {
                    Set<Proof.Used> used = reading.used();
                    return new Outcome.Proved(walks.isEmpty()
                            ? new Proof.ByTheBody(operation, used)
                            : new Proof.ByInduction(operation, carried, used));
                }
                last = outcomeOf(failed, reading);
            } catch (Reading.Stopped stopped) {
                last = stoppedAt(stopped);
            }
        }
        return last;
    }

    /** The statements of what a walk carries to try, in order, with none at all first for a body
     *  that walks nothing. */
    private static List<List<LawProposition<Slot>>> walking(
            List<List<LawProposition<Slot>>> carries) {
        List<List<LawProposition<Slot>>> out = new ArrayList<>();
        out.add(List.of());
        for (List<LawProposition<Slot>> each : carries) {
            if (!each.isEmpty() && !out.contains(each)) {
                out.add(each);
            }
        }
        return out;
    }

    /**
     * Whether {@code operation}'s answer holds no fewer than its argument at {@code container}, as
     * what is settled of it says — the law of how many it holds, or how that stands beside what
     * kernels answer, each proved of the body.
     */
    public Outcome noSmallerThan(ValueName.Stdlib.Operation operation, int container) {
        Reading reading = new Reading(library, readThrough);
        try {
            List<Value> params = arguments(operation);
            LawProposition<Value> goal = Props.compared(
                    reading.size(new Value.Made(operation, params)), Rel.GE,
                    reading.size(params.get(container)));
            return follows(reading, List.of(), goal, spacing(operation, Map.of()))
                    ? new Outcome.Proved(new Proof.ByTheBody(operation, reading.used()))
                    : outcomeOf(new Failed(Unproved.Obligation.THE_STATEMENT, goal), reading);
        } catch (Reading.Stopped stopped) {
            return stoppedAt(stopped);
        }
    }

    static Outcome stoppedAt(Reading.Stopped stopped) {
        return switch (stopped.why()) {
            case Library.Settled.Unsaid(Unsayable why) -> new Outcome.Unsaid(why);
            case Library.Settled.Open(Unproved why) -> new Outcome.Open(why);
            case Library.Settled.ByALaw _ -> throw new IllegalStateException(
                    "a reading stopped on a law, which is no reason to stop");
        };
    }

    /** The operation's own arguments, by place. */
    private List<Value> arguments(ValueName.Stdlib.Operation operation) {
        List<Value> params = new ArrayList<>();
        for (int at = 0; at < library.takes(operation).size(); at++) {
            params.add(new Value.Argument(at));
        }
        return params;
    }

    /** An obligation a proof did not meet: which, and the statement that did not follow. */
    private record Failed(Unproved.Obligation which, LawProposition<Value> goal) {}

    /**
     * What a failed obligation comes to: the domain having no words for something the statement
     * turned on, a law the proof needed not being settled, or the statement simply not following.
     */
    private static Outcome outcomeOf(Failed failed, Reading reading) {
        return switch (reading.unsettledIn(failed.goal())) {
            case Library.Settled.Unsaid(Unsayable why) -> new Outcome.Unsaid(why);
            case Library.Settled.Open(Unproved why) -> new Outcome.Open(why);
            case null, default -> new Outcome.Open(new Unproved.DoesNotFollow(failed.which()));
        };
    }

    /** The obligation that what the body comes to, case by case, is what {@code states} says —
     *  null where it is met, with what a walk in it carries where it ends known. */
    private Failed stated(ValueName.Stdlib.Operation operation, OperationLaw<Integer> states,
                          List<Reading.Case> cases, Reading reading, List<Value> params,
                          Induction induction) {
        Function<Value, Granularity> spacing = spacing(operation, Map.of());
        return switch (states) {
            case OperationLaw.Observation<Integer>(AnswerAspect aspect,
                                                   LawProposition<Integer> holds) -> {
                List<LawProposition<Value>> ways = new ArrayList<>();
                for (Reading.Case each : cases) {
                    ways.add(Props.both(each.when(), reading.side(each.is(), aspect)));
                }
                LawProposition<Value> goal = Props.same(
                        reading.proposition(holds, operation, params), Props.any(ways));
                List<Universal> ends = induction == null ? List.of() : induction.whereItEnds();
                yield follows(reading, List.of(), ends, goal, spacing) ? null
                        : new Failed(Unproved.Obligation.THE_STATEMENT, goal);
            }
            case OperationLaw.Size<Integer>(var sized) -> {
                List<Universal> ends = induction == null ? List.of() : induction.whereItEnds();
                // Every way the arguments stand is one of the cases, and in each, whichever case
                // of the body is taken, the body answers as many as the case says.
                List<LawProposition<Value>> where = new ArrayList<>();
                sized.forEach(each -> where.add(reading.proposition(each.where(), operation,
                        params)));
                LawProposition<Value> covered = Props.any(where);
                if (!follows(reading, List.of(), ends, covered, spacing)) {
                    yield new Failed(Unproved.Obligation.THE_STATEMENT, covered);
                }
                for (int at = 0; at < sized.size(); at++) {
                    LinearForm<LawNumber<Value>> stated = reading.form(sized.get(at).equalTo(),
                            operation, params);
                    for (Reading.Case each : cases) {
                        LawProposition<Value> goal = Props.compared(reading.size(each.is()),
                                Rel.EQ, stated);
                        if (!follows(reading, List.of(each.when(), where.get(at)), ends, goal,
                                spacing)) {
                            yield new Failed(Unproved.Obligation.THE_STATEMENT, goal);
                        }
                    }
                }
                yield null;
            }
        };
    }

    /**
     * A statement holding wherever {@code place} reads its words, of every value where it names
     * one ({@link Slot.Every}): a statement of what a walk carries, or a relation of a kernel to
     * what it was handed.
     */
    private record Universal(ValueName.Stdlib.Operation operation, LawProposition<Slot> statement,
                             Function<Slot, Value> place) {}

    /** {@code follows} with nothing held of every value. */
    private boolean follows(Reading reading, List<LawProposition<Value>> given,
                            LawProposition<Value> goal, Function<Value, Granularity> spacing) {
        return follows(reading, given, List.of(), goal, spacing);
    }

    /**
     * Whether {@code goal} follows from {@code given}, from {@code universal} taken of the values
     * the statements are about, and from what is known of the values the operations made: the laws
     * of the operations that made them, and what is stated of the kernels among them beside one
     * another — each taken again of what the last round brought in, a few rounds deep.
     */
    private boolean follows(Reading reading, List<LawProposition<Value>> given,
                            List<Universal> universal, LawProposition<Value> goal,
                            Function<Value, Granularity> spacing) {
        List<LawProposition<Value>> known = new ArrayList<>(given);
        Set<LawProposition<Value>> taken = new LinkedHashSet<>(given);
        List<Universal> holding = new ArrayList<>(universal);
        Set<Value.Made> related = new LinkedHashSet<>();
        for (int round = 0; round <= RELATED; round++) {
            List<LawProposition<Value>> about = new ArrayList<>(known);
            about.add(goal);
            Set<Value.Made> made = new LinkedHashSet<>();
            about.forEach(each -> Collect.values(each).forEach(value -> {
                if (value instanceof Value.Made one) {
                    made.add(one);
                }
            }));
            // And the ones read as what their operation's law says, which no statement names any
            // more and which are made all the same.
            made.addAll(reading.readByALaw());
            for (Value.Made one : made) {
                if (related.add(one)) {
                    known.addAll(linked(reading, one));
                    for (LawProposition<Slot> relation : library.relations(one.operation())) {
                        holding.add(new Universal(one.operation(), relation, slot -> switch (slot) {
                            case Slot.Place(int position) -> one.args().get(position);
                            case Slot.Every _, Slot.Carried _, Slot.Walked _, Slot.Answer _ -> null;
                        }));
                    }
                }
            }
            Set<Value> handed = new LinkedHashSet<>();
            about.forEach(each -> handed.addAll(Collect.alike(each)));
            Set<LawNumber<Value>> counts = new LinkedHashSet<>();
            about.forEach(each -> counts.addAll(Collect.counts(each)));
            boolean more = false;
            for (Universal each : holding) {
                for (Map<Integer, Value> way : everyWay(each.statement(), made, handed, counts)) {
                    LawProposition<Value> instance = reading.proposition(each.statement(),
                            each.operation(), slot -> slot instanceof Slot.Every(int which)
                                    ? way.get(which) : each.place().apply(slot),
                            Reading.Elements.none());
                    if (countsOnlyWhatIsCounted(each.statement(), way, instance, counts)
                            && taken.add(instance)) {
                        known.add(instance);
                        more = true;
                    }
                }
            }
            if (!more && round > 0) {
                break;
            }
        }
        return Validity.follows(known, goal, spacing);
    }

    /**
     * What the laws of the operation that made {@code made} say of it, as statements about the
     * value itself: that it holds something exactly where its law says, and holds as many as its
     * law says. A value is an atom wherever it is named as one, inside a statement about some
     * element of it among others, and this is what ties the atom to the law.
     */
    private List<LawProposition<Value>> linked(Reading reading, Value.Made made) {
        List<LawProposition<Value>> out = new ArrayList<>();
        for (AnswerAspect aspect : AnswerAspect.values()) {
            if (library.settled(made.operation(), OperationLaw.Observed.of(aspect))
                    instanceof Library.Settled.ByALaw) {
                out.add(Props.same(new LawProposition.Observed<>(
                        new LawSubject.Argument<>((Value) made), new SideAnswered(aspect, true)),
                        reading.side(made, aspect)));
            }
        }
        if (library.settled(made.operation(), OperationLaw.Observed.SIZE)
                instanceof Library.Settled.ByALaw(OperationLaw<Integer> law)) {
            LinearForm<LawNumber<Value>> itsSize = LinearForm.atom(new LawNumber.SizeOf<>(
                    new LawSubject.Argument<>((Value) made)));
            if (law instanceof OperationLaw.Size<Integer> size && size.unconditional() == null) {
                // As many as one of its cases says, where the arguments stand as that case does.
                List<LawProposition<Value>> cases = new ArrayList<>();
                for (OperationLaw.Size.Case<Integer> each : size.cases()) {
                    cases.add(Props.both(reading.proposition(each.where(), made.operation(),
                            made.args()), Props.compared(itsSize, Rel.EQ,
                            reading.form(each.equalTo(), made.operation(), made.args()))));
                }
                reading.took(Proof.Used.law(made.operation(), OperationLaw.Observed.SIZE));
                out.add(Props.any(cases));
            } else {
                out.add(Props.compared(itsSize, Rel.EQ, reading.size(made)));
            }
        }
        return out;
    }

    /**
     * Every way of taking each value {@code statement} holds of every one of: where the statement
     * counts its elements, as a container the statements it is asked among already count; as a
     * value handed, there, to an operation the statement names an answer of at that value's place;
     * or, where it names none there, as any of {@code handed}.
     */
    private static List<Map<Integer, Value>> everyWay(LawProposition<Slot> statement,
                                                      Set<Value.Made> made, Set<Value> handed,
                                                      Set<LawNumber<Value>> counts) {
        Set<Integer> every = new TreeSet<>();
        Collect.slots(statement, slot -> {
            if (slot instanceof Slot.Every(int which)) {
                every.add(which);
            }
        });
        Map<Integer, Set<Value>> taken = new HashMap<>();
        for (int which : every) {
            Set<Value> candidates = new LinkedHashSet<>();
            if (Triggers.counts(statement, which)) {
                counts.forEach(count -> {
                    if (count instanceof LawNumber.HowManyMeet<Value>(Value container, var _)) {
                        candidates.add(container);
                    }
                });
                taken.put(which, candidates);
                continue;
            }
            Triggers.of(statement, which).forEach((operation, at) -> made.forEach(one -> {
                if (one.operation().equals(operation) && at < one.args().size()) {
                    candidates.add(one.args().get(at));
                }
            }));
            if (candidates.isEmpty()) {
                handed.stream().limit(TAKEN_OF).forEach(candidates::add);
            }
            taken.put(which, candidates);
        }
        return everyWay(every, taken);
    }

    /**
     * Whether {@code instance}, {@code statement} taken {@code way}, counts the elements of a
     * value it was taken of only as the statements it is asked among already do: what it says of
     * such a count is worth saying of that count, and a count it would bring in is one nothing
     * asked about.
     */
    private static boolean countsOnlyWhatIsCounted(LawProposition<Slot> statement,
                                                   Map<Integer, Value> way,
                                                   LawProposition<Value> instance,
                                                   Set<LawNumber<Value>> counts) {
        Set<Value> countedOver = new LinkedHashSet<>();
        way.forEach((which, value) -> {
            if (Triggers.counts(statement, which)) {
                countedOver.add(value);
            }
        });
        if (countedOver.isEmpty()) {
            return true;
        }
        for (LawNumber<Value> count : Collect.counts(instance)) {
            if (count instanceof LawNumber.HowManyMeet<Value>(Value container, var _)
                    && countedOver.contains(container) && !counts.contains(count)) {
                return false;
            }
        }
        return true;
    }

    /** Every way of taking each value {@code statement} holds of every one of as one of
     *  {@code candidates}. */
    private static List<Map<Integer, Value>> everyWay(LawProposition<Slot> statement,
                                                      Set<Value> candidates) {
        Set<Integer> every = new TreeSet<>();
        Collect.slots(statement, slot -> {
            if (slot instanceof Slot.Every(int which)) {
                every.add(which);
            }
        });
        Map<Integer, Set<Value>> taken = new HashMap<>();
        every.forEach(which -> taken.put(which, candidates));
        return everyWay(every, taken);
    }

    private static List<Map<Integer, Value>> everyWay(Set<Integer> every,
                                                      Map<Integer, Set<Value>> candidates) {
        List<Map<Integer, Value>> ways = new ArrayList<>();
        ways.add(Map.of());
        for (int which : every) {
            List<Map<Integer, Value>> wider = new ArrayList<>();
            for (Map<Integer, Value> way : ways) {
                for (Value value : candidates.get(which).stream().limit(TAKEN_OF).toList()) {
                    Map<Integer, Value> one = new HashMap<>(way);
                    one.put(which, value);
                    wider.add(one);
                }
            }
            ways = wider;
        }
        return ways;
    }

    /** Every call of the library's walk {@code value} is made of. */
    private void walksIn(Value value, Set<Value.Made> into) {
        switch (value) {
            case Value.Made made when made.operation().equals(library.stdlib().walk().operation())
                    -> into.add(made);
            case Value.Made made -> made.args().forEach(arg -> walksIn(arg, into));
            case Value.Component(Value tuple, var _) -> walksIn(tuple, into);
            case Value.Tupled(List<Value> elements) -> elements.forEach(each -> walksIn(each, into));
            case Value.Listed(List<Value> elements) -> elements.forEach(each -> walksIn(each, into));
            case Value.Joined(Value left, Value right) -> {
                walksIn(left, into);
                walksIn(right, into);
            }
            case Value.Arithmetic(var _, Value left, Value right) -> {
                walksIn(left, into);
                walksIn(right, into);
            }
            case Value.AppliedTo(Value function, List<Value> args) -> {
                walksIn(function, into);
                args.forEach(arg -> walksIn(arg, into));
            }
            default -> { }
        }
    }

    /**
     * How the numbers a value can be are spaced: an argument as its type says, a part of what a
     * walk carries as the part of where it started does, and anything else as though it could be
     * any number at all — which is no less than it can be, so nothing is proved of it that is not
     * so.
     */
    private Function<Value, Granularity> spacing(ValueName.Stdlib.Operation operation,
                                                 Map<Value, Value> startedAs) {
        List<Type> takes = library.takes(operation);
        return new Function<>() {
            @Override
            public Granularity apply(Value value) {
                return switch (value) {
                    case Value.Argument(int at) -> Type.INT.equals(takes.get(at))
                            ? Granularity.DISCRETE : Granularity.DENSE;
                    case Value.Whole _ -> Granularity.DISCRETE;
                    case Value.Component _, Value.Fresh _ when startedAs.containsKey(value) ->
                            apply(startedAs.get(value));
                    default -> Granularity.DENSE;
                };
            }
        };
    }

    /** One walk in a body, and the proof of what it carries. */
    private final class Induction {

        private final ValueName.Stdlib.Operation operation;
        private final List<LawProposition<Slot>> carries;
        private final Reading reading;
        private final List<Value> params;
        private final Value.Made walk;
        private final TheWalk shape;

        Induction(ValueName.Stdlib.Operation operation, List<LawProposition<Slot>> carries,
                  Reading reading, List<Value> params, Value.Made walk) {
            this.operation = operation;
            this.carries = carries;
            this.reading = reading;
            this.params = params;
            this.walk = walk;
            this.shape = library.stdlib().walk();
        }

        private Value seed() {
            return walk.args().get(shape.seed());
        }

        private Value list() {
            return walk.args().get(shape.container());
        }

        /** Whether the walk starts at the head of a list the operation's arguments make, with a
         *  step written in the body: the walk the lemma's clauses can be about. */
        boolean overItsArguments() {
            return walk.args().get(shape.index()) instanceof Value.Whole(long from) && from == 0
                    && walk.args().get(shape.step()) instanceof Value.Lambda
                    && walked(list()) >= 0;
        }

        /** The obligation of the induction that is not met, or null where both are. */
        Failed prove() {
            LawProposition<Value> base = carried(seed(), view(new Value.NothingYet()),
                    anyValue());
            if (!follows(reading, List.of(), base, spacing(operation, Map.of()))) {
                return new Failed(Unproved.Obligation.THE_SEED, base);
            }
            Value carried = new Value.Fresh(1, "what the walk carries");
            Value walked = new Value.Fresh(2, "what the walk has walked");
            Value next = new Value.Fresh(3, "the element the walk is handed next");
            List<Value> handed = new ArrayList<>(List.of(next, next));
            handed.set(shape.accumulator(), carried);
            handed.set(shape.element(), next);
            Value step = walk.args().get(shape.step());
            for (Reading.Case each : reading.applied(step, handed)) {
                LawProposition<Value> goal = carried(each.is(),
                        view(new Value.OneMore(walked, next)), anyValue());
                List<LawProposition<Value>> given = new ArrayList<>();
                given.add(each.when());
                LawProposition<Value> different = neverTwice(walked, next);
                if (different != null) {
                    given.add(different);
                }
                if (!follows(reading, given, universal(carried, view(walked)), goal,
                        spacing(operation, startedAs(carried)))) {
                    return new Failed(Unproved.Obligation.A_STEP, goal);
                }
            }
            return null;
        }

        /** What the lemma's statements hold of where the walk ends, the whole list walked. */
        List<Universal> whereItEnds() {
            return universal(walk, view(list()));
        }

        /** The lemma's statements of {@code carried} with {@code walked} walked so far, each
         *  holding of every value. */
        private List<Universal> universal(Value carried, Value walked) {
            List<Universal> out = new ArrayList<>();
            for (LawProposition<Slot> clause : carries) {
                out.add(new Universal(operation, clause, slot -> switch (slot) {
                    case Slot.Place(int position) -> params.get(position);
                    case Slot.Carried(List<Integer> path) -> at(carried, path);
                    case Slot.Walked _ -> walked;
                    case Slot.Every _, Slot.Answer _ -> null;
                }));
            }
            return out;
        }

        /** Every statement of the lemma, of {@code carried} with {@code walked} walked so far,
         *  where a statement of every value is of {@code every}. */
        private LawProposition<Value> carried(Value carried, Value walked,
                                              Function<Integer, Value> every) {
            List<LawProposition<Value>> clauses = new ArrayList<>();
            for (LawProposition<Slot> clause : carries) {
                clauses.add(of(clause, carried, walked, every));
            }
            return Props.all(clauses);
        }

        private LawProposition<Value> of(LawProposition<Slot> clause, Value carried, Value walked,
                                         Function<Integer, Value> every) {
            return reading.proposition(clause, operation, slot -> switch (slot) {
                case Slot.Place(int position) -> params.get(position);
                case Slot.Carried(List<Integer> path) -> at(carried, path);
                case Slot.Walked _ -> walked;
                case Slot.Every(int which) -> every.apply(which);
                case Slot.Answer _ -> throw new IllegalStateException(
                        "what a walk carries is stated of the walk, and names no answer");
            }, Reading.Elements.none());
        }

        /** A value standing for any one, for a statement of every value to be shown of. */
        private Function<Integer, Value> anyValue() {
            return which -> new Value.Fresh(100 + which, "any value");
        }

        /**
         * That {@code next} is no element the walk has already walked, where the list walked is one
         * whose elements are each different — the elements of a set, the keys of a map's entries —
         * or null where it is not.
         */
        private LawProposition<Value> neverTwice(Value walked, Value next) {
            if (!(list() instanceof Value.Made(ValueName.Stdlib.Operation lists, var _))) {
                return null;
            }
            return switch (library.listing(lists)) {
                case AppliedClosures.Listing.EveryElementOf(var _, boolean eachDifferent)
                        when eachDifferent -> reading.some(walked,
                        each -> Reading.same(each.value(), next)).denied();
                case AppliedClosures.Listing.EveryEntryOf _ -> reading.some(walked,
                        each -> Reading.same(Reading.componentOf(each.value(), 0),
                                Reading.componentOf(next, 0))).denied();
                case null, default -> null;
            };
        }

        /** The operation's arguments with the walked one read as {@code walked}. */
        private Value view(Value part) {
            return entries(list()) ? new Value.AsEntries(part) : part;
        }

        /** Whether {@code list} lists a map's entries. */
        private boolean entries(Value list) {
            return list instanceof Value.Made(ValueName.Stdlib.Operation lists, var _)
                    && library.listing(lists) instanceof AppliedClosures.Listing.EveryEntryOf;
        }

        /** Which of the operation's arguments {@code list} lists, or -1 where it lists none. */
        private int walked(Value list) {
            return switch (list) {
                case Value.Argument(int at) -> at;
                case Value.Made(ValueName.Stdlib.Operation lists, List<Value> args) ->
                        switch (library.listing(lists)) {
                            case AppliedClosures.Listing.EveryElementOf(int argument, var _) ->
                                    walked(args.get(argument));
                            case AppliedClosures.Listing.EveryEntryOf(int argument) ->
                                    walked(args.get(argument));
                            case null, default -> -1;
                        };
                default -> -1;
            };
        }

        /** The part of {@code carried} at {@code path}. */
        private static Value at(Value carried, List<Integer> path) {
            Value part = carried;
            for (int index : path) {
                part = Reading.componentOf(part, index);
            }
            return part;
        }

        /** Which part of what the walk carries at a step started as which part of the seed: every
         *  part a statement of the lemma names. */
        private Map<Value, Value> startedAs(Value carried) {
            Map<Value, Value> out = new HashMap<>();
            for (LawProposition<Slot> clause : carries) {
                Collect.slots(clause, slot -> {
                    if (slot instanceof Slot.Carried(List<Integer> path)) {
                        out.put(at(carried, path), at(seed(), path));
                    }
                });
            }
            return out;
        }
    }
}
