package souther.compiler.proof;

import souther.compiler.core.TheWalk;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
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
import souther.compiler.types.BinOp;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.IdentityHashMap;
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

        /** It is not proved, for {@code why} — however far the proof got, a value it met that
         *  the domain has no words for among the reasons. */
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

    /**
     * Whether {@code observed} of what {@code operation} answers is something the domain has no
     * words for, for {@code why}: in every case of its body the answer is what an operation
     * answers whose {@code observed} is closed for that reason, so what it comes to on that
     * observation is that answer's, and lacks words for the same reason.
     *
     * <p>Only the answer itself. A body meeting such a value somewhere — under a guard, beside
     * another value, inside a walk — comes to something that may well have words, and a proof that
     * stopped there has not shown it does not.
     */
    public Outcome closes(ValueName.Stdlib.Operation operation, OperationLaw.Observed observed,
                          Unsayable why) {
        Reading reading = new Reading(library, readThrough);
        try {
            for (Reading.Case each : reading.cases(reading.bodyOf(operation),
                    new Reading.Frame(arguments(operation), Map.of()))) {
                if (!(each.is() instanceof Value.Made(ValueName.Stdlib.Operation answering,
                        var _) && library.settled(answering, observed)
                        instanceof Library.Settled.Unsaid(Unsayable closed) && closed == why)) {
                    return new Outcome.Open(new Unproved.DoesNotFollow(
                            Unproved.Obligation.THE_CASES));
                }
                reading.took(Proof.Used.law(answering, observed));
            }
            return new Outcome.Proved(new Proof.ByTheBody(operation, reading.used()));
        } catch (Reading.Stopped stopped) {
            return stoppedAt(stopped);
        }
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

    /**
     * The type of what each operator of {@code operation}'s body, {@code body}, answers, read off
     * what it is handed: an argument as the operation's signature says, a number written out as
     * its own, what an operation answers as that operation's signature says, and what a walk
     * carries as where it started. An operator handed values of no type said here, or answering
     * values of more than one type where it is met, is not among them.
     *
     * <p>Only where a reading meets it: an operator in a closure the body never applies is met
     * nowhere, and nor is one in a body this reading stops in.
     */
    public Map<LibraryTerm, Type> typesOf(ValueName.Stdlib.Operation operation, LibraryTerm body) {
        Reading reading = new Reading(library, readThrough);
        List<Type> takes = library.takes(operation);
        try {
            List<Value> params = arguments(operation);
            List<Reading.Case> cases = reading.cases(body, new Reading.Frame(params, Map.of()));
            Set<Value.Made> walks = new LinkedHashSet<>();
            cases.forEach(each -> walksIn(each.is(), walks));
            Map<Value, Type> startedAs = new HashMap<>();
            for (Value.Made walk : walks) {
                TheWalk shape = library.stdlib().walk();
                if (!(walk.args().get(shape.step()) instanceof Value.Lambda)) {
                    continue;
                }
                Value carried = new Value.Fresh(10 + startedAs.size(), "what a walk carries");
                startedAs.put(carried, typeOf(walk.args().get(shape.seed()), takes, Map.of()));
                List<Value> handed = new ArrayList<>(List.of(carried, carried));
                handed.set(shape.accumulator(), carried);
                handed.set(shape.element(), new Value.ElementOf(walk.args().get(shape.container())));
                reading.applied(walk.args().get(shape.step()), handed);
            }
            Map<LibraryTerm, Type> out = new IdentityHashMap<>();
            reading.met().forEach((term, met) -> {
                Set<Type> types = new LinkedHashSet<>();
                for (Reading.Case each : met) {
                    types.add(typeOf(ofTheSameType(term, each.is()), takes, startedAs));
                }
                if ((term instanceof LibraryTerm.Operator || term instanceof LibraryTerm.Negated)
                        && types.size() == 1 && types.iterator().next() != null) {
                    out.put(term, types.iterator().next());
                }
            });
            return out;
        } catch (Reading.Stopped stopped) {
            return Map.of();
        }
    }

    /** A value of the type what {@code term} came to, {@code value}, is of: a negation is read as
     *  nought less the number, whose type the number says. */
    private static Value ofTheSameType(LibraryTerm term, Value value) {
        return term instanceof LibraryTerm.Negated
                && value instanceof Value.Arithmetic(var _, var _, Value negated) ? negated : value;
    }

    /**
     * The type {@code value} is a value of, where what made it says: or null where nothing here
     * says. {@code startedAs} is the type each value standing for what a walk carries started as.
     */
    private Type typeOf(Value value, List<Type> takes, Map<Value, Type> startedAs) {
        return switch (value) {
            case Value.Argument(int at) -> takes.get(at);
            case Value.Whole _ -> Type.INT;
            case Value.Decimal _ -> Type.DECIMAL;
            case Value.Truth _, Value.Statement _ -> Type.BOOL;
            case Value.Listed(List<Value> elements) -> new Type.ListOf(elements.isEmpty()
                    ? new Type.Nothing() : typeOf(elements.getFirst(), takes, startedAs));
            case Value.Tupled(List<Value> elements) -> {
                List<Type> each = new ArrayList<>();
                for (Value element : elements) {
                    each.add(typeOf(element, takes, startedAs));
                }
                yield each.contains(null) ? null : new Type.TupleOf(each);
            }
            case Value.Component(Value tuple, int index) ->
                    typeOf(tuple, takes, startedAs) instanceof Type.TupleOf(List<Type> elements)
                            && index < elements.size() ? elements.get(index) : null;
            case Value.Made(ValueName.Stdlib.Operation made, var _) ->
                    library.stdlib().entry(made).signature().result();
            case Value.Arithmetic(BinOp op, Value left, Value right) -> {
                Type one = typeOf(left, takes, startedAs);
                Type other = typeOf(right, takes, startedAs);
                yield op == BinOp.DIV || Type.RATIONAL.equals(one) || Type.RATIONAL.equals(other)
                        ? Type.RATIONAL : one != null && one.equals(other) ? one : null;
            }
            case Value.Joined(Value left, Value right) -> {
                Type one = typeOf(left, takes, startedAs);
                yield one != null ? one : typeOf(right, takes, startedAs);
            }
            case Value.PayloadOf(Value option) ->
                    typeOf(option, takes, startedAs) instanceof Type.OptionOf(Type element)
                            ? element : null;
            case Value.ElementOf(Value container) -> switch (typeOf(container, takes, startedAs)) {
                case Type.ListOf(Type element) -> element;
                case Type.SetOf(Type element) -> element;
                case null, default -> null;
            };
            case Value.Fresh _ -> startedAs.get(value);
            default -> null;
        };
    }

    /**
     * How much the collections an operation's body builds at the sites {@code asked} names hold on
     * the way to its answer, and whether the whole numbers it works out at the others lie where
     * {@code asked} says, where no collection holds more than it says ({@link AskedOnTheWay}).
     *
     * <p>Each site is asked of every case a reading of the body meets it in, under the way the body
     * went to reach it. A walk in the body is read by induction, over what it carries part by part:
     * a collection holding no more than it started with and one element, or the elements of one
     * element, for each element walked, and a whole number no further from where it started than
     * what one step adds to it for each. The first such statement proved of the walk is what a site
     * in its step is asked under, with the part walked so far, and the element the step is handed,
     * a part of the list ({@link Induction}). A site holds no more than some collection handed to
     * the operation where it holds no more than one of them, or no more than what a part of the
     * walk is proved to carry once the element it is handed is walked, where that is no more than
     * one of them at the end of the list. Otherwise no more than a number of the arguments: all
     * the collections handed together, how many the operation's answer holds, where its law says
     * that whatever it is handed, or one of {@code alsoNoMoreThan}, what the asker's owners say a
     * site holds over the arguments.
     *
     * <p>A site met nowhere — under a closure the body never applies — and a body this reading
     * stops in, or one walking more than once, are not shown.
     */
    public HeldOnTheWay heldOnTheWay(AskedOnTheWay asked) {
        ValueName.Stdlib.Operation operation = asked.operation();
        LibraryTerm body = asked.body();
        Set<LibraryTerm> collections = asked.collections();
        Set<LibraryTerm> numbers = asked.numbers();
        BigInteger least = asked.least();
        BigInteger greatest = asked.greatest();
        BigInteger mostElements = asked.mostElements();
        Reading reading = new Reading(library, readThrough);
        try {
            List<Value> params = arguments(operation);
            List<Reading.Case> cases = reading.cases(body, new Reading.Frame(params, Map.of()));
            Map<LibraryTerm, List<Reading.Case>> outside = new IdentityHashMap<>(reading.met());
            Set<Value.Made> walks = new LinkedHashSet<>();
            cases.forEach(each -> walksIn(each.is(), walks));
            if (walks.size() > 1) {
                return new HeldOnTheWay.NotShown();
            }
            List<Integer> handed = new ArrayList<>();
            List<Type> takes = library.takes(operation);
            for (int at = 0; at < takes.size(); at++) {
                if (aCollection(takes.get(at))) {
                    handed.add(at);
                }
            }
            List<LawProposition<Value>> fitting = new ArrayList<>();
            for (int at : handed) {
                fitting.add(Props.compared(reading.size(params.get(at)), Rel.LE,
                        LinearForm.constant(ExactRatio.of(mostElements))));
            }
            Walked walked = walks.isEmpty() ? null
                    : walked(operation, reading, params, walks.iterator().next(), mostElements);
            Map<LibraryTerm, List<Reading.Case>> inside =
                    walked == null ? Map.of() : walked.met();
            List<Universal> ended = walked == null ? List.of()
                    : walked.induction().whereItEnds();
            Function<Value, Granularity> spaced = spacing(operation, Map.of());
            // Every number in range, wherever it is met.
            for (LibraryTerm site : numbers) {
                boolean atAStep = !outside.containsKey(site);
                List<Reading.Case> met = atAStep ? inside.get(site) : outside.get(site);
                if (met == null) {
                    return new HeldOnTheWay.NotShown();
                }
                for (Reading.Case each : met) {
                    LinearForm<LawNumber<Value>> number = reading.number(each.is());
                    LawProposition<Value> goal = Props.both(
                            Props.compared(number, Rel.GE,
                                    LinearForm.constant(ExactRatio.of(least))),
                            Props.compared(number, Rel.LE,
                                    LinearForm.constant(ExactRatio.of(greatest))));
                    if (!(atAStep ? walked.follows(each, fitting, goal)
                            : follows(reading, given(each, fitting), ended, goal, spaced))) {
                        return new HeldOnTheWay.NotShown();
                    }
                }
            }
            // What each collection is no more than: a collection handed, or what it is no more
            // than at the end of the list.
            List<LinearForm<LawNumber<Value>>> singles = new ArrayList<>();
            handed.forEach(at -> singles.add(reading.size(params.get(at))));
            List<List<LinearForm<LawNumber<Value>>>> owed = new ArrayList<>();
            boolean withinWhatItIsHanded = true;
            for (LibraryTerm site : collections) {
                boolean atAStep = !outside.containsKey(site);
                List<Reading.Case> met = atAStep ? inside.get(site) : outside.get(site);
                if (met == null) {
                    return new HeldOnTheWay.NotShown();
                }
                for (Reading.Case each : met) {
                    LinearForm<LawNumber<Value>> size = reading.size(each.is());
                    List<LinearForm<LawNumber<Value>>> noMoreThan = new ArrayList<>();
                    if (atAStep) {
                        for (Walked.Part part : walked.parts()) {
                            if (walked.follows(each, fitting, Props.compared(size, Rel.LE,
                                    part.most(walked.induction().walkedOneFurther())))) {
                                noMoreThan.add(part.most(walked.induction().walkedToTheEnd()));
                            }
                        }
                    } else {
                        noMoreThan.add(size);
                    }
                    if (noMoreThan.isEmpty()) {
                        return new HeldOnTheWay.NotShown();
                    }
                    withinWhatItIsHanded &= noMoreThan.stream().anyMatch(most -> singles.stream()
                            .anyMatch(one -> follows(reading, given(each, fitting), ended,
                                    Props.compared(most, Rel.LE, one), spaced)));
                    owed.add(noMoreThan);
                }
            }
            if (withinWhatItIsHanded) {
                return new HeldOnTheWay.WithinWhatItIsHanded();
            }
            List<LinearForm<LawNumber<Integer>>> candidates =
                    new ArrayList<>(noMoreThan(operation, handed));
            candidates.addAll(asked.alsoNoMoreThan());
            for (LinearForm<LawNumber<Integer>> most : candidates) {
                LinearForm<LawNumber<Value>> read = reading.form(most, operation, params::get,
                        Reading.Elements.none());
                if (owed.stream().allMatch(one -> one.stream().anyMatch(each -> follows(reading,
                        fitting, ended, Props.compared(each, Rel.LE, read), spaced)))) {
                    return new HeldOnTheWay.NoMoreThan(most);
                }
            }
            return new HeldOnTheWay.NotShown();
        } catch (Reading.Stopped stopped) {
            return new HeldOnTheWay.NotShown();
        }
    }

    /** {@code also}, and that the way to {@code met} was taken. */
    private static List<LawProposition<Value>> given(Reading.Case met,
                                                     List<LawProposition<Value>> also) {
        List<LawProposition<Value>> out = new ArrayList<>(also);
        out.add(met.when());
        return out;
    }

    /** Whether a value of {@code type} is a collection, counted by how many it holds. */
    private static boolean aCollection(Type type) {
        return type instanceof Type.ListOf || type instanceof Type.SetOf
                || type instanceof Type.MapOf;
    }

    /**
     * The numbers of {@code operation}'s arguments a collection it builds may be held to, in
     * order: every collection it is handed together, and how many its answer holds where its law
     * says that whatever it is handed.
     */
    private List<LinearForm<LawNumber<Integer>>> noMoreThan(ValueName.Stdlib.Operation operation,
                                                            List<Integer> handed) {
        List<LinearForm<LawNumber<Integer>>> out = new ArrayList<>();
        if (!handed.isEmpty()) {
            LinearForm<LawNumber<Integer>> together = Props.constant(0);
            for (int at : handed) {
                together = Props.plus(together, LinearForm.atom(
                        new LawNumber.SizeOf<>(new LawSubject.Argument<>(at))));
            }
            out.add(together);
        }
        if (library.settled(operation, OperationLaw.Observed.SIZE)
                instanceof Library.Settled.ByALaw(OperationLaw<Integer> law)
                && law instanceof OperationLaw.Size<Integer> size && size.unconditional() != null) {
            out.add(size.unconditional());
        }
        return out;
    }

    /**
     * The walk of a body proved to carry no more than it started with and a bounded growth for
     * each element, part by part, with every site its step was met at under that.
     */
    private final class Walked {

        /** One part of what a walk carries, by where it is in it, and how much it is proved to
         *  hold at most: a number of the operation's arguments and of the part walked. */
        record Part(List<Integer> path, LinearForm<LawNumber<Slot>> held,
                    ValueName.Stdlib.Operation operation, List<Value> params, Reading reading) {

            /** How much it holds at most where {@code walked} is the part walked. */
            LinearForm<LawNumber<Value>> most(Value walked) {
                return reading.form(held, operation, slot -> switch (slot) {
                    case Slot.Place(int position) -> params.get(position);
                    case Slot.Walked _ -> walked;
                    case Slot.Carried _, Slot.Every _, Slot.Answer _ -> null;
                }, Reading.Elements.none());
            }
        }

        private final Induction induction;
        private final List<Part> parts;
        private final Map<LibraryTerm, List<Reading.Case>> met;
        private final Reading reading;
        private final BigInteger mostElements;

        Walked(Induction induction, List<Part> parts, Map<LibraryTerm, List<Reading.Case>> met,
               Reading reading, BigInteger mostElements) {
            this.induction = induction;
            this.parts = List.copyOf(parts);
            this.met = met;
            this.reading = reading;
            this.mostElements = mostElements;
        }

        Induction induction() {
            return induction;
        }

        List<Part> parts() {
            return parts;
        }

        Map<LibraryTerm, List<Reading.Case>> met() {
            return met;
        }

        /** Whether {@code goal} follows at a step where {@code each} was met: from what the walk
         *  is proved to carry there, and from the part walked with the element it is handed being
         *  a part of the list, which a collection holds. */
        boolean follows(Reading.Case each, List<LawProposition<Value>> also,
                        LawProposition<Value> goal) {
            List<LawProposition<Value>> given = given(each, also);
            LinearForm<LawNumber<Value>> further = reading.size(induction.walkedOneFurther());
            given.add(Props.compared(further, Rel.LE, reading.size(induction.walkedToTheEnd())));
            given.add(Props.compared(further, Rel.LE,
                    LinearForm.constant(ExactRatio.of(mostElements))));
            return LibraryProver.this.follows(reading, given, induction.atAStep(), goal,
                    induction.spacedAtAStep());
        }
    }

    /**
     * {@code walk}, the one walk of {@code operation}'s body, with the first statement of what it
     * carries that is proved of it — or null where none is.
     */
    private Walked walked(ValueName.Stdlib.Operation operation, Reading reading,
                          List<Value> params, Value.Made walk, BigInteger mostElements) {
        TheWalk shape = library.stdlib().walk();
        Value seed = walk.args().get(shape.seed());
        List<List<Integer>> paths = new ArrayList<>();
        if (seed instanceof Value.Tupled(List<Value> elements)) {
            for (int at = 0; at < elements.size(); at++) {
                paths.add(List.of(at));
            }
        } else {
            paths.add(List.of());
        }
        // For each part, what it may be proved to carry, each with how much it then holds.
        List<List<Carrying>> ways = new ArrayList<>();
        for (List<Integer> path : paths) {
            ways.add(carrying(operation, reading, params, walk, path));
        }
        for (List<Carrying> chosen : everyChoice(ways)) {
            List<LawProposition<Slot>> carries = new ArrayList<>();
            List<Walked.Part> parts = new ArrayList<>();
            for (int at = 0; at < paths.size(); at++) {
                Carrying one = chosen.get(at);
                if (one == null) {
                    continue;
                }
                carries.addAll(one.clauses());
                if (one.held() != null) {
                    parts.add(new Walked.Part(paths.get(at), one.held(), operation, params,
                            reading));
                }
            }
            Induction induction = new Induction(operation, carries, reading, params, walk);
            if (!induction.overItsArguments()) {
                return null;
            }
            reading.forgetWhatWasMet();
            try {
                if (!carries.isEmpty() && induction.prove() == null) {
                    Map<LibraryTerm, List<Reading.Case>> met = new IdentityHashMap<>(reading.met());
                    return new Walked(induction, parts, met, reading, mostElements);
                }
                if (carries.isEmpty()) {
                    induction.stepped();
                    return new Walked(induction, parts, new IdentityHashMap<>(reading.met()),
                            reading, mostElements);
                }
            } catch (Reading.Stopped stopped) {
                // Not this statement: the next may be read further.
            }
        }
        return null;
    }

    /** A statement of what one part of a walk carries, and how much it then holds at most, or
     *  null where it is a number. */
    private record Carrying(List<LawProposition<Slot>> clauses, LinearForm<LawNumber<Slot>> held) {}

    /**
     * What the part at {@code path} of what {@code walk} carries may be proved to be: where it
     * starts as a whole number written out, no lower than that and no higher than what a step adds
     * at most for each element walked; where it starts as a collection whose size is a number of
     * the arguments, holding no more than that and one for each element walked, or than that and
     * what each element walked holds. Nothing (a choice of no statement) where it is neither.
     */
    private List<Carrying> carrying(ValueName.Stdlib.Operation operation, Reading reading,
                                    List<Value> params, Value.Made walk, List<Integer> path) {
        TheWalk shape = library.stdlib().walk();
        Value started = Induction.at(walk.args().get(shape.seed()), path);
        LawNumber<Slot> part = started instanceof Value.Whole
                ? new LawNumber.AnArgument<>(new Slot.Carried(path))
                : new LawNumber.SizeOf<>(new LawSubject.Argument<>(new Slot.Carried(path)));
        LinearForm<LawNumber<Slot>> walkedSize = LinearForm.atom(
                new LawNumber.SizeOf<>(new LawSubject.Argument<>(new Slot.Walked())));
        List<Carrying> out = new ArrayList<>();
        if (started instanceof Value.Whole(long from)) {
            BigInteger most = mostAddedInAStep(reading, walk, path);
            if (most != null) {
                LinearForm<LawNumber<Slot>> held = Props.plus(Props.constant(from),
                        Props.held(walkedSize.times(ExactRatio.of(most))));
                out.add(new Carrying(List.of(
                        Props.compared(LinearForm.atom(part), Rel.GE, Props.constant(from)),
                        Props.compared(LinearForm.atom(part), Rel.LE, held)), null));
            }
        } else {
            LinearForm<LawNumber<Slot>> from = sizeAsItStarts(reading, started);
            if (from != null) {
                LinearForm<LawNumber<Slot>> oneEach = Props.plus(from, walkedSize);
                LinearForm<LawNumber<Slot>> theirs = Props.plus(from, LinearForm.atom(
                        new LawNumber.SumOver<>(new Slot.Walked(), new LawNumber.SizeOf<>(
                                new LawSubject.ElementOf<>(new Slot.Walked())))));
                out.add(new Carrying(List.of(Props.compared(LinearForm.atom(part), Rel.LE,
                        oneEach)), oneEach));
                out.add(new Carrying(List.of(Props.compared(LinearForm.atom(part), Rel.LE,
                        theirs)), theirs));
            }
        }
        out.add(null);
        return out;
    }

    /** How many a collection that starts as {@code started} holds, as a number of the
     *  operation's arguments, or null where it is not one. */
    private static LinearForm<LawNumber<Slot>> sizeAsItStarts(Reading reading, Value started) {
        if (started instanceof Value.Argument(int at)) {
            return LinearForm.atom(new LawNumber.SizeOf<>(new LawSubject.Argument<>(
                    new Slot.Place(at))));
        }
        LinearForm<LawNumber<Value>> size = reading.size(started);
        return size.coefs().isEmpty() ? LinearForm.constant(size.constant()) : null;
    }

    /**
     * The most a step of {@code walk} adds to the whole number at {@code path} of what it carries,
     * where in every case it comes to that number with a whole number not below nought written
     * out added — or null where it is anything else.
     */
    private static BigInteger mostAddedInAStep(Reading reading, Value.Made walk,
                                               List<Integer> path) {
        // A reading of its own, so that what this meets is not taken for what the proof meets.
        Reading apart = new Reading(reading.library(), Set.of());
        TheWalk shape = reading.library().stdlib().walk();
        List<Value> handed = new ArrayList<>(List.of(NEXT, NEXT));
        handed.set(shape.accumulator(), CARRIED);
        handed.set(shape.element(), NEXT);
        LinearForm<LawNumber<Value>> before = apart.number(Induction.at(CARRIED, path));
        BigInteger most = BigInteger.ZERO;
        for (Reading.Case each : apart.applied(walk.args().get(shape.step()), handed)) {
            LinearForm<LawNumber<Value>> added = Props.minus(
                    apart.number(Induction.at(each.is(), path)), before);
            if (!added.coefs().isEmpty() || added.constant().signum() < 0
                    || !(added.constant().ceiling() instanceof ExactAnswer.Held<BigInteger>(
                            var whole))
                    || !added.constant().equals(ExactRatio.of(whole))) {
                return null;
            }
            most = most.max(whole);
        }
        return most;
    }

    /** Every way of taking one of each list, in order. */
    private static <T> List<List<T>> everyChoice(List<List<T>> each) {
        List<List<T>> out = new ArrayList<>();
        out.add(List.of());
        for (List<T> one : each) {
            List<List<T>> wider = new ArrayList<>();
            for (List<T> before : out) {
                for (T chosen : one) {
                    List<T> next = new ArrayList<>(before);
                    next.add(chosen);
                    wider.add(next);
                }
            }
            out = wider;
        }
        return out;
    }

    static Outcome stoppedAt(Reading.Stopped stopped) {
        return switch (stopped.why()) {
            case Library.Settled.Unsaid(Unsayable why) ->
                    new Outcome.Open(new Unproved.TurnsOnWhatIsNotSaid(why));
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
     * turned on, a law the proof needed not being settled, or the statement simply not following
     * — each of them a statement not proved.
     */
    private static Outcome outcomeOf(Failed failed, Reading reading) {
        return switch (reading.unsettledIn(failed.goal())) {
            case Library.Settled.Unsaid(Unsayable why) ->
                    new Outcome.Open(new Unproved.TurnsOnWhatIsNotSaid(why));
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

    /** What the walk carries at a step, read as any value it may be. */
    private static final Value CARRIED = new Value.Fresh(1, "what the walk carries");
    /** The part of the list a step's walk has walked before the element it is handed. */
    private static final Value WALKED = new Value.Fresh(2, "what the walk has walked");
    /** The element a step is handed. */
    private static final Value NEXT = new Value.Fresh(3, "the element the walk is handed next");

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
                    Induction::anyValue);
            if (!follows(reading, List.of(), base, spacing(operation, Map.of()))) {
                return new Failed(Unproved.Obligation.THE_SEED, base);
            }
            Value carried = CARRIED;
            Value walked = WALKED;
            Value next = NEXT;
            for (Reading.Case each : stepped()) {
                LawProposition<Value> goal = carried(each.is(),
                        view(new Value.OneMore(walked, next)), Induction::anyValue);
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

        /** The cases the step comes to, handed what the walk carries so far and the next element
         *  as values standing for any. */
        List<Reading.Case> stepped() {
            List<Value> handed = new ArrayList<>(List.of(NEXT, NEXT));
            handed.set(shape.accumulator(), CARRIED);
            handed.set(shape.element(), NEXT);
            return reading.applied(walk.args().get(shape.step()), handed);
        }

        /** What the lemma's statements hold of what the walk carries at a step, with the part
         *  walked before the element it is handed. */
        List<Universal> atAStep() {
            return universal(CARRIED, view(WALKED));
        }

        /** The part walked once the step has taken the element it is handed. */
        Value walkedOneFurther() {
            return view(new Value.OneMore(WALKED, NEXT));
        }

        /** The whole list walked, as the lemma's statements read it. */
        Value walkedToTheEnd() {
            return view(list());
        }

        /** How the numbers a value standing for what the walk carries can be are spaced. */
        Function<Value, Granularity> spacedAtAStep() {
            return spacing(operation, startedAs(CARRIED));
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

        /** A value standing for any one, the {@code which}th of a statement of every value to be
         *  shown of. */
        private static Value anyValue(int which) {
            return new Value.Fresh(100 + which, "any value");
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
