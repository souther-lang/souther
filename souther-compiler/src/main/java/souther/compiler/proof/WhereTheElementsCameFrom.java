package souther.compiler.proof;

import souther.compiler.core.TheWalk;
import souther.compiler.numeric.LinearForm;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.BuiltFrom;
import souther.compiler.semantics.ClosurePositions;
import souther.compiler.semantics.Combinator;
import souther.compiler.semantics.ElementLineage;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.semantics.SizeAgainstItsSource;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.UnaryOperator;

/**
 * Where the elements of what an operation the library writes answers came from, and how many of
 * them there are, proved against its body.
 *
 * <p>What a lineage states is read for what it is ({@link ElementLineage}): each element of the
 * answer is one of the source's own, or the closure's answer on one, or a value inside that answer
 * — and, for the first two, on a different element of the source each time. The body shows it by
 * how it builds the answer. A walk over the source's elements that starts from nothing and, at each
 * element it is handed, keeps what it carries or puts one value in shows that every element came
 * from one element of the source, and none came from two; what that value is, at each step, is
 * what the lineage says it is or the walk is not that lineage. The source as it stands is every one
 * of its elements, each once. And what another operation is settled to build is what the body
 * builds where it calls that operation, read through.
 *
 * <p>How many there are is the second statement and is shown apart. As many as the source is the
 * operation's size law, proved of the body on its own; no more than the source is that law, or a
 * building that puts in at most one value for each element of the source.
 *
 * <p>Read by structure and nothing else: no statement about a value is weighed here, and nothing
 * here knows any operation's name. What a kernel puts in, lists or builds is what it is declared to,
 * and an operation the library writes builds what its own proof showed.
 */
public final class WhereTheElementsCameFrom {

    /** How many elements of an answer one element of its source accounts for. */
    private enum Accounts {
        /** One at most: each element of the answer is from a different element of the source. */
        AT_MOST_ONE,
        /** Any number: what the answer holds is said and how many of the source's is not. */
        ANY_NUMBER
    }

    private final Library library;
    private final Set<ValueName.Stdlib.Operation> readThrough;

    /**
     * @param readThrough the operations whose bodies are read where they are called, as the
     *                    proofs of what the library's operations come to read them
     */
    public WhereTheElementsCameFrom(Library library, Set<ValueName.Stdlib.Operation> readThrough) {
        this.library = library;
        this.readThrough = Set.copyOf(readThrough);
    }

    /** Whether {@code built}, stated of {@code operation} over its arguments by place, is what its
     *  body builds. */
    public LibraryProver.Outcome prove(ValueName.Stdlib.Operation operation,
                                       BuiltFrom<Integer> built) {
        if (built.outputs().size() != 1 || !built.outputs().getFirst().at()
                .equals(ElementLineage.ResultPath.elements())) {
            return new LibraryProver.Outcome.Open(new Unproved.NotOverItsArguments());
        }
        return prove(operation, built.lineage(), built.size());
    }

    /** Whether every element of {@code operation}'s answer came from its source as {@code wanted}
     *  says, how many there are being no part of the statement. */
    public LibraryProver.Outcome proveWhereTheyCameFrom(ValueName.Stdlib.Operation operation,
                                                        ElementLineage<Integer> wanted) {
        return prove(operation, wanted, null);
    }

    /** As {@link #prove(ValueName.Stdlib.Operation, BuiltFrom)}, with the count held to
     *  {@code size} where there is one and left alone where it is null. */
    private LibraryProver.Outcome prove(ValueName.Stdlib.Operation operation,
                                        ElementLineage<Integer> wanted,
                                        SizeAgainstItsSource size) {
        ElementLineage.Source<Integer> source = wanted.source();
        if (source == null || source.elements() != 1) {
            return new LibraryProver.Outcome.Open(new Unproved.NotOverItsArguments());
        }
        Reading reading = new Reading(library, readThrough);
        try {
            List<Value> params = new ArrayList<>();
            for (int at = 0; at < library.takes(operation).size(); at++) {
                params.add(new Value.Argument(at));
            }
            Building building = new Building(operation, source, reading);
            boolean atMostOneEach = true;
            for (Reading.Case each : reading.cases(reading.bodyOf(operation),
                    new Reading.Frame(params, Map.of()))) {
                Accounts accounts = building.explained(each.is(), wanted);
                if (accounts == null) {
                    return new LibraryProver.Outcome.Open(new Unproved.DoesNotFollow(
                            Unproved.Obligation.WHERE_ITS_ELEMENTS_CAME_FROM));
                }
                atMostOneEach &= accounts == Accounts.AT_MOST_ONE;
            }
            boolean asMany = size != null && asManyAs(operation, source.argument(), reading);
            boolean holds = size == null || switch (size) {
                case SAME -> asMany;
                case AT_MOST -> asMany || atMostOneEach;
            };
            if (!holds) {
                return new LibraryProver.Outcome.Open(new Unproved.DoesNotFollow(
                        Unproved.Obligation.HOW_MANY_IT_HOLDS));
            }
            return new LibraryProver.Outcome.Proved(
                    new Proof.ByWhatItsBodyBuilds(operation, reading.used()));
        } catch (Reading.Stopped stopped) {
            return LibraryProver.stoppedAt(stopped);
        }
    }

    /**
     * Whether the elements of {@code operation}'s answer stand in the order of the elements of its
     * argument at {@code source} they came from: its body is a walk over that argument as it stands,
     * from its first element, started from nothing, every step of which keeps what it carries or
     * puts one value after all of it.
     *
     * <p>A walk is handed a list's elements in the list's order, so what each step puts after the
     * rest stands after everything put for the elements before it. Nothing about which values are
     * put is read here; that is where the elements came from, and is proved apart.
     */
    public LibraryProver.Outcome inOrder(ValueName.Stdlib.Operation operation, int source) {
        Reading reading = new Reading(library, readThrough);
        try {
            List<Value> params = new ArrayList<>();
            for (int at = 0; at < library.takes(operation).size(); at++) {
                params.add(new Value.Argument(at));
            }
            TheWalk walk = library.stdlib().walk();
            for (Reading.Case each : reading.cases(reading.bodyOf(operation),
                    new Reading.Frame(params, Map.of()))) {
                List<Integer> path = new ArrayList<>();
                Value at = each.is();
                while (at instanceof Value.Component(Value tuple, int index)) {
                    path.addFirst(index);
                    at = tuple;
                }
                if (!(at instanceof Value.Made(ValueName.Stdlib.Operation walks, List<Value> args))
                        || !walks.equals(walk.operation())
                        || !(args.get(walk.index()) instanceof Value.Whole(long from)) || from != 0
                        || !args.get(walk.container()).equals(new Value.Argument(source))
                        || !(Building.at(args.get(walk.seed()), path)
                                instanceof Value.Listed(List<Value> seeded))
                        || !seeded.isEmpty()
                        || !appendsAtTheEnd(args.get(walk.step()), walk, path, reading)) {
                    return new LibraryProver.Outcome.Open(new Unproved.DoesNotFollow(
                            Unproved.Obligation.WHERE_ITS_ELEMENTS_CAME_FROM));
                }
            }
            return new LibraryProver.Outcome.Proved(
                    new Proof.ByWhatItsBodyBuilds(operation, reading.used()));
        } catch (Reading.Stopped stopped) {
            return LibraryProver.stoppedAt(stopped);
        }
    }

    /** Whether every case of {@code step} keeps what is carried at {@code path} or puts one value
     *  after all of it. */
    private static boolean appendsAtTheEnd(Value step, TheWalk walk, List<Integer> path,
                                           Reading reading) {
        Value carried = new Value.Fresh(1, "what the walk carries");
        Value next = new Value.Fresh(3, "the element the walk is handed next");
        List<Value> handed = new ArrayList<>(List.of(next, next));
        handed.set(walk.accumulator(), carried);
        handed.set(walk.element(), next);
        Value before = Building.at(carried, path);
        for (Reading.Case each : reading.applied(step, handed)) {
            Value after = Building.at(each.is(), path);
            if (!after.equals(before) && !(after instanceof Value.Joined(Value left, Value right)
                    && left.equals(before) && right instanceof Value.Listed(List<Value> one)
                    && one.size() == 1)) {
                return false;
            }
        }
        return true;
    }

    /** Whether {@code operation}'s answer is settled to hold as many as its argument at
     *  {@code source}. */
    private boolean asManyAs(ValueName.Stdlib.Operation operation, int source, Reading reading) {
        if (library.settled(operation, OperationLaw.Observed.SIZE)
                instanceof Library.Settled.ByALaw(OperationLaw.Size<Integer> size)
                && LinearForm.atom(new LawNumber.SizeOf<>(
                        new LawSubject.Argument<>(source))).equals(size.unconditional())) {
            reading.took(Proof.Used.law(operation, OperationLaw.Observed.SIZE));
            return true;
        }
        return false;
    }

    /** What one operation's body builds, against the argument whose elements it is about. */
    private final class Building {

        private final ValueName.Stdlib.Operation operation;
        private final Value source;
        /** The source's elements as they stand, which is what a closure that made an element was
         *  handed. */
        private final ElementLineage<Integer> asTheyStand;
        private final Reading reading;
        private final TheWalk walk;

        Building(ValueName.Stdlib.Operation operation, ElementLineage.Source<Integer> source,
                 Reading reading) {
            this.operation = operation;
            this.source = new Value.Argument(source.argument());
            this.asTheyStand = new ElementLineage.SameAs<>(source);
            this.reading = reading;
            this.walk = library.stdlib().walk();
        }

        /**
         * How many of {@code run}'s elements one element of the source accounts for, where every
         * one of them came from the source as {@code wanted} says — or null where that is not
         * shown.
         */
        Accounts explained(Value run, ElementLineage<Integer> wanted) {
            if (run.equals(source)) {
                return permits(wanted, Kind.ITSELF) ? Accounts.AT_MOST_ONE : null;
            }
            if (empty(run)) {
                return Accounts.AT_MOST_ONE;
            }
            List<Integer> path = new ArrayList<>();
            Value at = run;
            while (at instanceof Value.Component(Value tuple, int index)) {
                path.addFirst(index);
                at = tuple;
            }
            if (at instanceof Value.Made made && made.operation().equals(walk.operation())) {
                return walked(made, path, wanted);
            }
            if (!path.isEmpty() || !(run instanceof Value.Made(
                    ValueName.Stdlib.Operation called, List<Value> args))) {
                return null;
            }
            if (library.listing(called) instanceof AppliedClosures.Listing.EveryElementOf(
                    int argument, var _)) {
                reading.took(new Proof.Used(called, Proof.Taken.WHAT_IT_LISTS));
                return explained(args.get(argument), wanted);
            }
            Accounts through = throughWhatItBuilds(called, args, wanted);
            if (through != null) {
                return through;
            }
            return putOutsideAWalk(called, args, wanted);
        }

        /**
         * A walk's answer, or the part of it at {@code path}: started from nothing, over the
         * source's elements from the first, each step keeping what it carries there or putting one
         * value in that came from the element it is handed.
         */
        private Accounts walked(Value.Made made, List<Integer> path,
                                ElementLineage<Integer> wanted) {
            List<Value> args = made.args();
            if (!(args.get(walk.index()) instanceof Value.Whole(long from)) || from != 0
                    || !empty(at(args.get(walk.seed()), path))) {
                return null;
            }
            UnaryOperator<Reading.Element> handedAs = elementsOf(args.get(walk.container()));
            if (handedAs == null) {
                return null;
            }
            Value carried = new Value.Fresh(1, "what the walk carries");
            Value next = new Value.Fresh(3, "the element the walk is handed next");
            List<Value> handed = new ArrayList<>(List.of(next, next));
            handed.set(walk.accumulator(), carried);
            handed.set(walk.element(), next);
            Value before = at(carried, path);
            Reading.Element element = handedAs.apply(new Reading.Element(next,
                    new Value.KeyOf(next)));
            Accounts accounts = Accounts.AT_MOST_ONE;
            for (Reading.Case each : reading.applied(args.get(walk.step()), handed)) {
                Value after = at(each.is(), path);
                if (after.equals(before)) {
                    continue;
                }
                if (joinsTheClosuresAnswer(after, before, element, wanted)) {
                    accounts = Accounts.ANY_NUMBER;
                    continue;
                }
                Value put = putIn(after, before);
                if (put == null || !allows(put, element, wanted)) {
                    return null;
                }
            }
            return accounts;
        }

        /**
         * Whether {@code after} is {@code before} with the closure's whole answer on
         * {@code element} joined to it, and {@code wanted} says an element may be inside that
         * answer.
         *
         * <p>Any number of the answer's elements come of the one element of the source, which is
         * why this is not a value put in.
         */
        private boolean joinsTheClosuresAnswer(Value after, Value before, Reading.Element element,
                                               ElementLineage<Integer> wanted) {
            return permits(wanted, Kind.INSIDE_THE_CLOSURES_ANSWER)
                    && after instanceof Value.Joined(Value left, Value right)
                    && left.equals(before) && theClosuresAnswer(right, element);
        }

        /** How an element {@code list} hands a walk reads as an element of the source, or null
         *  where what the walk is handed is not the source's elements. */
        private UnaryOperator<Reading.Element> elementsOf(Value list) {
            if (list.equals(source)) {
                return UnaryOperator.identity();
            }
            if (!(list instanceof Value.Made(ValueName.Stdlib.Operation lists, List<Value> args))) {
                return null;
            }
            return switch (library.listing(lists)) {
                case AppliedClosures.Listing.EveryElementOf(int argument, var _)
                        when args.get(argument).equals(source) -> {
                    reading.took(new Proof.Used(lists, Proof.Taken.WHAT_IT_LISTS));
                    yield UnaryOperator.identity();
                }
                case AppliedClosures.Listing.EveryEntryOf(int argument)
                        when args.get(argument).equals(source) -> {
                    reading.took(new Proof.Used(lists, Proof.Taken.WHAT_IT_LISTS));
                    yield entry -> new Reading.Element(Reading.componentOf(entry.value(), 1),
                            Reading.componentOf(entry.value(), 0));
                }
                case null, default -> null;
            };
        }

        /** The value {@code after} is {@code before} with put in, or null where it is not
         *  {@code before} with one value put in. */
        private Value putIn(Value after, Value before) {
            if (after instanceof Value.Joined(Value left, Value right) && left.equals(before)
                    && right instanceof Value.Listed(List<Value> one) && one.size() == 1) {
                return one.getFirst();
            }
            if (after instanceof Value.Joined(Value left, Value right) && right.equals(before)
                    && left instanceof Value.Listed(List<Value> one) && one.size() == 1) {
                return one.getFirst();
            }
            if (after instanceof Value.Made(ValueName.Stdlib.Operation puts, List<Value> args)
                    && library.puts(puts) instanceof Library.Put(int value, int into)
                    && args.get(into).equals(before)) {
                reading.took(new Proof.Used(puts, Proof.Taken.WHAT_IT_PUTS_IN));
                return args.get(value);
            }
            return null;
        }

        /**
         * What another operation is settled to build, read through: the elements of what it was
         * handed are the source's as {@code wanted} says, where what it builds of them keeps them,
         * or answers the closure this operation was handed on each of them.
         */
        private Accounts throughWhatItBuilds(ValueName.Stdlib.Operation called, List<Value> args,
                                             ElementLineage<Integer> wanted) {
            BuiltFrom<Integer> built = library.builtFrom(called);
            if (built == null || built.outputs().size() != 1 || !built.outputs().getFirst().at()
                    .equals(ElementLineage.ResultPath.elements())) {
                return null;
            }
            ElementLineage.Source<Integer> from = built.lineage().source();
            if (from == null || from.elements() != 1) {
                return null;
            }
            reading.took(new Proof.Used(called, Proof.Taken.WHAT_IT_BUILDS));
            Value inner = args.get(from.argument());
            return switch (built.lineage()) {
                case ElementLineage.SameAs<Integer> _ -> explained(inner, wanted);
                case ElementLineage.ClosureResult<Integer> _ ->
                        permits(wanted, Kind.THE_CLOSURES_ANSWER) && handsOnTheClosure(called, args)
                                ? explained(inner, asTheyStand) : null;
                case ElementLineage.InsideClosureResult<Integer> _ ->
                        permits(wanted, Kind.INSIDE_THE_CLOSURES_ANSWER)
                                && handsOnTheClosure(called, args)
                                && explained(inner, asTheyStand) != null
                                ? Accounts.ANY_NUMBER : null;
                case ElementLineage.OneOf<Integer> _ -> null;
            };
        }

        /**
         * A value put in what came from the source, outside a walk: the answer holds what came from
         * the source and that value, and which of the source's the value took the place of is not
         * read. So it is a statement of what each element is and not of how many, and only a
         * lineage that says nothing more is shown by it.
         */
        private Accounts putOutsideAWalk(ValueName.Stdlib.Operation called, List<Value> args,
                                         ElementLineage<Integer> wanted) {
            if (!(wanted instanceof ElementLineage.OneOf<Integer>)
                    || !(library.puts(called) instanceof Library.Put(int value, int into))
                    || explained(args.get(into), wanted) == null) {
                return null;
            }
            reading.took(new Proof.Used(called, Proof.Taken.WHAT_IT_PUTS_IN));
            Value put = args.get(value);
            for (Value element : candidates(put)) {
                Reading.Element got = anElementOfTheSource(element);
                if (got != null && allows(put, got, wanted)) {
                    return Accounts.ANY_NUMBER;
                }
            }
            return null;
        }

        /** The values {@code put} could have been made of an element as: itself, or what the
         *  closure was handed where it is the closure's answer. */
        private List<Value> candidates(Value put) {
            List<Value> out = new ArrayList<>(List.of(put));
            ClosurePositions positions = library.positions(operation);
            if (positions != null && put instanceof Value.AppliedTo(var _, List<Value> args)
                    && positions.elementParam() < args.size()) {
                out.add(args.get(positions.elementParam()));
            }
            return out;
        }

        /** {@code value} as an element of the source, where it is the one value an operation
         *  answers of the source's elements; null where it is not. */
        private Reading.Element anElementOfTheSource(Value value) {
            if (value instanceof Value.PayloadOf(Value.Made(ValueName.Stdlib.Operation gets,
                    List<Value> args))
                    && library.listing(gets) instanceof AppliedClosures.Listing.AtMostOneElementOf(
                            int argument)
                    && args.get(argument).equals(source)) {
                reading.took(new Proof.Used(gets, Proof.Taken.WHAT_IT_LISTS));
                return new Reading.Element(value, null);
            }
            return null;
        }

        /** Whether {@code called}, handed {@code args}, hands the closure this operation was
         *  handed what this operation hands it: the same parameter for the element and the key. */
        private boolean handsOnTheClosure(ValueName.Stdlib.Operation called, List<Value> args) {
            ClosurePositions mine = library.positions(operation);
            ClosurePositions theirs = library.positions(called);
            return mine != null && theirs != null
                    && args.get(theirs.closureArg()).equals(new Value.Argument(mine.closureArg()))
                    && mine.elementParam() == theirs.elementParam()
                    && mine.keyParam() == theirs.keyParam();
        }

        /** Whether {@code put}, put in for {@code element}, is what {@code wanted} says an element
         *  of the answer is. */
        private boolean allows(Value put, Reading.Element element, ElementLineage<Integer> wanted) {
            return switch (wanted) {
                case ElementLineage.SameAs<Integer> _ -> put.equals(element.value());
                case ElementLineage.ClosureResult<Integer> _ -> theClosuresAnswer(put, element);
                case ElementLineage.InsideClosureResult<Integer> _ ->
                        put instanceof Value.PayloadOf(Value answer)
                                && theClosuresAnswer(answer, element);
                case ElementLineage.OneOf<Integer>(var alternatives) -> alternatives.stream()
                        .anyMatch(each -> allows(put, element, each));
            };
        }

        /** Whether {@code value} is the closure this operation was handed, applied with
         *  {@code element} where it takes an element and with its key where it takes a key. */
        private boolean theClosuresAnswer(Value value, Reading.Element element) {
            ClosurePositions positions = library.positions(operation);
            if (positions == null || !(value instanceof Value.AppliedTo(Value function,
                    List<Value> args))
                    || !function.equals(new Value.Argument(positions.closureArg()))
                    || positions.elementParam() >= args.size()
                    || !args.get(positions.elementParam()).equals(element.value())) {
                return false;
            }
            return positions.keyParam() == Combinator.NO_KEY
                    || (positions.keyParam() < args.size() && element.key() != null
                            && args.get(positions.keyParam()).equals(element.key()));
        }

        /** Whether {@code value} holds nothing whatever it was made of: written empty, or the
         *  answer of an operation whose law says it holds nothing. */
        private boolean empty(Value value) {
            if (value instanceof Value.Listed(List<Value> elements)) {
                return elements.isEmpty();
            }
            if (value instanceof Value.Made(ValueName.Stdlib.Operation made, var _)
                    && library.settled(made, OperationLaw.Observed.EMPTINESS)
                    instanceof Library.Settled.ByALaw(OperationLaw.Observation<Integer>(
                            AnswerAspect aspect, LawProposition.Always<Integer>(boolean holds)))
                    && aspect == AnswerAspect.EMPTINESS && !holds) {
                reading.took(Proof.Used.law(made, OperationLaw.Observed.EMPTINESS));
                return true;
            }
            return false;
        }

        private static Value at(Value value, List<Integer> path) {
            Value part = value;
            for (int index : path) {
                part = Reading.componentOf(part, index);
            }
            return part;
        }
    }

    /** What an element of an answer may be, as a lineage names it. */
    private enum Kind { ITSELF, THE_CLOSURES_ANSWER, INSIDE_THE_CLOSURES_ANSWER }

    /** Whether {@code lineage} says an element may be of {@code kind}. */
    private static boolean permits(ElementLineage<Integer> lineage, Kind kind) {
        return switch (lineage) {
            case ElementLineage.SameAs<Integer> _ -> kind == Kind.ITSELF;
            case ElementLineage.ClosureResult<Integer> _ -> kind == Kind.THE_CLOSURES_ANSWER;
            case ElementLineage.InsideClosureResult<Integer> _ ->
                    kind == Kind.INSIDE_THE_CLOSURES_ANSWER;
            case ElementLineage.OneOf<Integer>(var alternatives) -> alternatives.stream()
                    .anyMatch(each -> permits(each, kind));
        };
    }
}
