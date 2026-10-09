package souther.compiler.proof;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.ClosurePositions;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.semantics.SideAnswered;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.Function;

/**
 * A library operation's body read for what it comes to over its arguments, and what is known of a
 * value read through the laws of whatever made it.
 *
 * <p>Two halves of one reading. A body comes to values, one for each case its forks and matches
 * answer by ({@link #cases}); a value is known by what a law of the operation that made it says of
 * it, over what that operation was handed ({@link #side}, {@link #size}, {@link #number}). Each
 * step is one of a few: a binding is what it is bound to, a closure written out and applied is its
 * body over what it is handed, a fork is two cases, and an operation's answer is what its law says
 * of it. Where no step applies, the reading stops and says why ({@link Stopped}).
 */
final class Reading {

    /** One way a body comes out: what it comes to where {@code when} holds. */
    record Case(LawProposition<Value> when, Value is) {}

    /** What the names a part of a body reads are: the operation's arguments, and what is bound. */
    record Frame(List<Value> params, Map<BindingId, Value> bound) {

        Frame {
            params = List.copyOf(params);
            bound = Map.copyOf(bound);
        }

        Frame with(BindingId binding, Value value) {
            Map<BindingId, Value> more = new HashMap<>(bound);
            more.put(binding, value);
            return new Frame(params, more);
        }
    }

    /** An element a statement about the elements of a container is about, and the key it is filed
     *  under, where it is filed under one. */
    record Element(Value value, Value key) {}

    /** Why a reading went no further: a side of something settled as the domain having no words
     *  for it, or a proof that could not be made. */
    static final class Stopped extends RuntimeException {

        private static final long serialVersionUID = 1L;

        private final transient Library.Settled why;

        Stopped(Library.Settled why) {
            super(null, null, false, false);
            this.why = why;
        }

        Library.Settled why() {
            return why;
        }
    }

    private final Library library;
    /** The operations whose bodies are read where they are called rather than their answers
     *  observed: the walks the library writes over other walks. */
    private final Set<ValueName.Stdlib.Operation> readThrough;
    private final Map<ValueName.Stdlib.Operation, LibraryTerm> bodies = new LinkedHashMap<>();
    /** What this reading has taken of other operations, which is what a proof made of it rests on. */
    private final Set<Proof.Used> used = new LinkedHashSet<>();
    /** The values made by an operation something was asked of that nothing settles, with why: each
     *  is known of nothing but itself where it is read. */
    private final Map<Value, Library.Settled> unsettled = new LinkedHashMap<>();

    Reading(Library library, Set<ValueName.Stdlib.Operation> readThrough) {
        this.library = library;
        this.readThrough = Set.copyOf(readThrough);
    }

    /** What this reading has taken of other operations so far. */
    Set<Proof.Used> used() {
        return Set.copyOf(used);
    }

    /** That what is read rests on {@code taken} as well, where a proof took it beside the
     *  reading. */
    void took(Proof.Used taken) {
        used.add(taken);
    }

    Library library() {
        return library;
    }

    LibraryTerm bodyOf(ValueName.Stdlib.Operation operation) {
        return bodies.computeIfAbsent(operation, op -> LibraryTerms.of(library.stdlib(),
                library.stdlib().helpers().get(op)));
    }

    // --- what a body comes to ------------------------------------------------------------------

    /** The cases {@code term} comes out by, read in {@code frame}. */
    List<Case> cases(LibraryTerm term, Frame frame) {
        return switch (term) {
            case LibraryTerm.Parameter(int position) ->
                    one(frame.params().get(position));
            case LibraryTerm.Bound(BindingId binding) -> {
                Value value = frame.bound().get(binding);
                if (value == null) {
                    throw new Stopped(new Library.Settled.Open(new Unproved.ReadShort(
                            LibraryTerm.Unwritten.A_NAME_OF_NOTHING_HERE)));
                }
                yield one(value);
            }
            case LibraryTerm.WholeNumber(long value) -> one(new Value.Whole(value));
            case LibraryTerm.DecimalNumber(var value) -> one(new Value.Decimal(value));
            case LibraryTerm.Truth(boolean value) -> one(new Value.Truth(value));
            case LibraryTerm.ListOf(List<LibraryTerm> elements) ->
                    each(elements, frame, Value.Listed::new);
            case LibraryTerm.TupleOf(List<LibraryTerm> elements) ->
                    each(elements, frame, Value.Tupled::new);
            case LibraryTerm.Component(LibraryTerm tuple, int index) ->
                    mapped(cases(tuple, frame), value -> componentOf(value, index));
            case LibraryTerm.Negated(LibraryTerm operand) ->
                    mapped(cases(operand, frame), Reading::negated);
            case LibraryTerm.Closure closure ->
                    one(new Value.Lambda(closure, frame.params(), frame.bound()));
            case LibraryTerm.Let(BindingId binding, LibraryTerm value, LibraryTerm body) -> {
                List<Case> out = new ArrayList<>();
                for (Case bound : cases(value, frame)) {
                    for (Case inside : cases(body, frame.with(binding, bound.is()))) {
                        out.add(new Case(Props.both(bound.when(), inside.when()), inside.is()));
                    }
                }
                yield out;
            }
            case LibraryTerm.Call(ValueName.Stdlib.Operation operation, List<LibraryTerm> args) ->
                    flatEach(args, frame, values -> called(operation, values));
            case LibraryTerm.Applied(LibraryTerm function, List<LibraryTerm> args) -> {
                List<LibraryTerm> all = new ArrayList<>();
                all.add(function);
                all.addAll(args);
                yield flatEach(all, frame, values -> applied(values.get(0),
                        values.subList(1, values.size())));
            }
            case LibraryTerm.Fork(LibraryTerm condition, LibraryTerm then, LibraryTerm otherwise,
                                  var _) -> {
                List<Case> out = new ArrayList<>();
                for (Case decided : cases(condition, frame)) {
                    LawProposition<Value> holds = side(decided.is(), AnswerAspect.TRUTH);
                    out.addAll(under(Props.both(decided.when(), holds), cases(then, frame)));
                    out.addAll(under(Props.both(decided.when(), holds.denied()),
                            cases(otherwise, frame)));
                }
                yield out;
            }
            case LibraryTerm.OnAnOption(LibraryTerm option, BindingId value, LibraryTerm present,
                                        LibraryTerm absent, var _) -> {
                List<Case> out = new ArrayList<>();
                for (Case read : cases(option, frame)) {
                    LawProposition<Value> holds = side(read.is(), AnswerAspect.PRESENCE);
                    out.addAll(under(Props.both(read.when(), holds), cases(present,
                            frame.with(value, new Value.PayloadOf(read.is())))));
                    out.addAll(under(Props.both(read.when(), holds.denied()),
                            cases(absent, frame)));
                }
                yield out;
            }
            case LibraryTerm.Operator(BinOp op, LibraryTerm left, LibraryTerm right, var _) ->
                    operated(op, left, right, frame);
            case LibraryTerm.Unread(LibraryTerm.Unwritten what) ->
                    throw new Stopped(new Library.Settled.Open(new Unproved.ReadShort(what)));
        };
    }

    /** Nought less {@code value}, which is what a negation is. */
    private static Value negated(Value value) {
        return new Value.Arithmetic(BinOp.SUB, new Value.Whole(0), value);
    }

    /** Every combination of the cases of the two operands, each put to {@code op}. */
    private List<Case> operated(BinOp op, LibraryTerm left, LibraryTerm right, Frame frame) {
        List<Case> out = new ArrayList<>();
        List<Case> rights = cases(right, frame);
        for (Case one : cases(left, frame)) {
            for (Case other : rights) {
                out.add(new Case(Props.both(one.when(), other.when()),
                        operated(op, one.is(), other.is())));
            }
        }
        return out;
    }

    private static List<Case> one(Value value) {
        return List.of(new Case(Props.always(true), value));
    }

    private static List<Case> under(LawProposition<Value> when, List<Case> cases) {
        List<Case> out = new ArrayList<>();
        cases.forEach(each -> out.add(new Case(Props.both(when, each.when()), each.is())));
        return out;
    }

    private static List<Case> mapped(List<Case> cases, Function<Value, Value> into) {
        List<Case> out = new ArrayList<>();
        cases.forEach(each -> out.add(new Case(each.when(), into.apply(each.is()))));
        return out;
    }

    /** Every combination of the cases of {@code terms}, each made into one value. */
    private List<Case> each(List<LibraryTerm> terms, Frame frame,
                            Function<List<Value>, Value> into) {
        return flatEach(terms, frame, values -> one(into.apply(values)));
    }

    /** Every combination of the cases of {@code terms}, each read on into cases of its own. */
    private List<Case> flatEach(List<LibraryTerm> terms, Frame frame,
                                Function<List<Value>, List<Case>> into) {
        List<Case> combined = new ArrayList<>();
        combined.add(new Case(Props.always(true), new Value.Listed(List.of())));
        for (LibraryTerm term : terms) {
            List<Case> wider = new ArrayList<>();
            List<Case> read = cases(term, frame);
            for (Case before : combined) {
                for (Case next : read) {
                    List<Value> values = new ArrayList<>(((Value.Listed) before.is()).elements());
                    values.add(next.is());
                    wider.add(new Case(Props.both(before.when(), next.when()),
                            new Value.Listed(values)));
                }
            }
            combined = wider;
        }
        List<Case> out = new ArrayList<>();
        for (Case each : combined) {
            out.addAll(under(each.when(), into.apply(((Value.Listed) each.is()).elements())));
        }
        return out;
    }

    /** What calling {@code operation} on {@code args} comes to: its answer, or its body read where
     *  it is a walk over another walk. */
    private List<Case> called(ValueName.Stdlib.Operation operation, List<Value> args) {
        if (readThrough.contains(operation)) {
            return cases(bodyOf(operation), new Frame(args, Map.of()));
        }
        return one(new Value.Made(operation, args));
    }

    /** What applying {@code function} to {@code args} comes to. */
    List<Case> applied(Value function, List<Value> args) {
        if (function instanceof Value.Lambda(LibraryTerm.Closure closure, List<Value> params,
                Map<BindingId, Value> around)) {
            if (closure.params().size() != args.size()) {
                throw new Stopped(new Library.Settled.Open(new Unproved.ReadShort(
                        LibraryTerm.Unwritten.A_NAME_OF_NOTHING_HERE)));
            }
            Map<BindingId, Value> bound = new HashMap<>(around);
            for (int at = 0; at < args.size(); at++) {
                bound.put(closure.params().get(at), args.get(at));
            }
            return cases(closure.body(), new Frame(params, bound));
        }
        return one(new Value.AppliedTo(function, args));
    }

    /** The component at {@code index} of {@code value}, read off the tuple where it is written. */
    static Value componentOf(Value value, int index) {
        return value instanceof Value.Tupled(List<Value> elements) ? elements.get(index)
                : new Value.Component(value, index);
    }

    /** One of the language's operators applied. */
    private Value operated(BinOp op, Value left, Value right) {
        return switch (op) {
            case AND -> new Value.Statement(Props.both(side(left, AnswerAspect.TRUTH),
                    side(right, AnswerAspect.TRUTH)));
            case OR -> new Value.Statement(Props.either(side(left, AnswerAspect.TRUTH),
                    side(right, AnswerAspect.TRUTH)));
            case ADD, SUB, MUL, DIV -> new Value.Arithmetic(op, left, right);
            case CONCAT -> new Value.Joined(left, right);
            case LT, LE, GT, GE -> new Value.Statement(Props.compared(number(left),
                    relationOf(op), number(right)));
            case EQ, NE -> {
                LawProposition<Value> alike = isNumber(left) || isNumber(right)
                        ? Props.compared(number(left), Rel.EQ, number(right))
                        : same(left, right);
                yield new Value.Statement(op == BinOp.EQ ? alike : alike.denied());
            }
        };
    }

    private static Rel relationOf(BinOp op) {
        return switch (op) {
            case LT -> Rel.LT;
            case LE -> Rel.LE;
            case GT -> Rel.GT;
            case GE -> Rel.GE;
            default -> throw new IllegalArgumentException(op + " orders nothing");
        };
    }

    /** Whether {@code value} is a number by how it was made. */
    private boolean isNumber(Value value) {
        return switch (value) {
            case Value.Whole _, Value.Decimal _, Value.Arithmetic _ -> true;
            case Value.Made(ValueName.Stdlib.Operation operation, var _) ->
                    library.answersTheNumber(operation) != null;
            default -> false;
        };
    }

    /** That {@code one} and {@code other} are the same value. */
    static LawProposition<Value> same(Value one, Value other) {
        if (one.equals(other)) {
            return Props.always(true);
        }
        return new LawProposition.Same<>(new LawSubject.Argument<>(one),
                new LawSubject.Argument<>(other), true);
    }

    // --- what is known of a value ---------------------------------------------------------------

    /** That {@code value} comes out on {@code aspect}'s holding side. */
    LawProposition<Value> side(Value value, AnswerAspect aspect) {
        return switch (value) {
            case Value.Truth(boolean holds) when aspect == AnswerAspect.TRUTH ->
                    Props.always(holds);
            case Value.Statement(LawProposition<Value> holds) when aspect == AnswerAspect.TRUTH ->
                    holds;
            case Value.Listed(List<Value> elements) when aspect == AnswerAspect.EMPTINESS ->
                    Props.always(!elements.isEmpty());
            case Value.Joined(Value left, Value right) when aspect == AnswerAspect.EMPTINESS ->
                    Props.either(side(left, aspect), side(right, aspect));
            case Value.NothingYet _ when aspect == AnswerAspect.EMPTINESS -> Props.always(false);
            case Value.OneMore _ when aspect == AnswerAspect.EMPTINESS -> Props.always(true);
            case Value.AsEntries(Value entries) when aspect == AnswerAspect.EMPTINESS ->
                    side(entries, aspect);
            case Value.Made(ValueName.Stdlib.Operation operation, List<Value> args) ->
                    madeSide(operation, args, aspect);
            case Value.AppliedTo(Value function, List<Value> args)
                    when function instanceof Value.Lambda -> joined(applied(function, args),
                            each -> side(each, aspect));
            default -> new LawProposition.Observed<>(new LawSubject.Argument<>(value),
                    new SideAnswered(aspect, true));
        };
    }

    /** What the cases of something come to on one statement of each. */
    private static LawProposition<Value> joined(List<Case> cases,
                                                Function<Value, LawProposition<Value>> of) {
        List<LawProposition<Value>> ways = new ArrayList<>();
        cases.forEach(each -> ways.add(Props.both(each.when(), of.apply(each.is()))));
        return Props.any(ways);
    }

    private LawProposition<Value> madeSide(ValueName.Stdlib.Operation operation, List<Value> args,
                                           AnswerAspect aspect) {
        OperationLaw.Observed observed = OperationLaw.Observed.of(aspect);
        Library.Settled settled = library.settled(operation, observed);
        if (settled instanceof Library.Settled.ByALaw(OperationLaw<Integer> law)
                && law instanceof OperationLaw.Observation<Integer>(var _,
                        LawProposition<Integer> holds)) {
            used.add(Proof.Used.law(operation, observed));
            return proposition(holds, operation, args);
        }
        if (aspect == AnswerAspect.EMPTINESS && listed(operation, args) instanceof Value source) {
            return side(source, aspect);
        }
        Value made = new Value.Made(operation, args);
        unsettled.putIfAbsent(made, why(settled, operation, observed));
        return new LawProposition.Observed<>(new LawSubject.Argument<>(made),
                new SideAnswered(aspect, true));
    }

    /**
     * Why a side of what {@code operation} answers is known of nothing but itself: the domain has no
     * words for it, or what was stated of it is not proved, or nothing was stated.
     */
    private static Library.Settled why(Library.Settled settled,
                                       ValueName.Stdlib.Operation operation,
                                       OperationLaw.Observed observed) {
        return switch (settled) {
            case Library.Settled.Unsaid unsaid -> unsaid;
            case Library.Settled.Open _ ->
                    new Library.Settled.Open(new Unproved.OpenBelow(operation, observed));
            case null, default ->
                    new Library.Settled.Open(new Unproved.NothingSettles(operation, observed));
        };
    }

    /**
     * Why what {@code holds} says is about more than the operation's arguments, where it names a
     * value nothing settles a side of — the domain having no words for it first — or null where it
     * names none.
     */
    Library.Settled unsettledIn(LawProposition<Value> holds) {
        Library.Settled found = null;
        Set<Value> named = Collect.values(holds);
        for (Map.Entry<Value, Library.Settled> each : unsettled.entrySet()) {
            if (named.contains(each.getKey())) {
                if (each.getValue() instanceof Library.Settled.Unsaid) {
                    return each.getValue();
                }
                if (found == null) {
                    found = each.getValue();
                }
            }
        }
        return found;
    }

    /** The argument whose every element an answer of {@code operation} holds, each once, read
     *  as the answer is — or null where its answer lists no argument's elements. */
    private Value listed(ValueName.Stdlib.Operation operation, List<Value> args) {
        return switch (listing(operation)) {
            case AppliedClosures.Listing.EveryElementOf(int argument, var _) -> args.get(argument);
            case AppliedClosures.Listing.EveryEntryOf(int argument) -> args.get(argument);
            case null, default -> null;
        };
    }

    /** What {@code operation}'s answer lists, taken into what this reading rests on where it
     *  lists anything. */
    private AppliedClosures.Listing listing(ValueName.Stdlib.Operation operation) {
        AppliedClosures.Listing listing = library.listing(operation);
        if (listing != null) {
            used.add(new Proof.Used(operation, Proof.Taken.WHAT_IT_LISTS));
        }
        return listing;
    }

    /** How many {@code value} holds. */
    LinearForm<LawNumber<Value>> size(Value value) {
        return switch (value) {
            case Value.Listed(List<Value> elements) -> Props.constant(elements.size());
            case Value.Joined(Value left, Value right) -> Props.plus(size(left), size(right));
            case Value.NothingYet _ -> Props.constant(0);
            case Value.OneMore(Value walked, var _) -> Props.plus(size(walked), Props.constant(1));
            case Value.AsEntries(Value entries) -> size(entries);
            case Value.Made(ValueName.Stdlib.Operation operation, List<Value> args) -> {
                Library.Settled settled = library.settled(operation, OperationLaw.Observed.SIZE);
                if (settled instanceof Library.Settled.ByALaw(OperationLaw<Integer> law)
                        && law instanceof OperationLaw.Size<Integer>(var equalTo)) {
                    used.add(Proof.Used.law(operation, OperationLaw.Observed.SIZE));
                    yield form(equalTo, operation, args);
                }
                Value source = listed(operation, args);
                if (source != null) {
                    yield size(source);
                }
                unsettled.putIfAbsent(value, why(settled, operation, OperationLaw.Observed.SIZE));
                yield LinearForm.atom(new LawNumber.SizeOf<>(new LawSubject.Argument<>(value)));
            }
            default -> LinearForm.atom(new LawNumber.SizeOf<>(new LawSubject.Argument<>(value)));
        };
    }

    /** The number {@code value} is. */
    LinearForm<LawNumber<Value>> number(Value value) {
        return switch (value) {
            case Value.Whole(long whole) -> Props.constant(whole);
            case Value.Decimal(var decimal) -> LinearForm.constant(ExactRatio.of(decimal));
            case Value.Arithmetic(BinOp op, Value left, Value right) when op == BinOp.ADD ->
                    Props.plus(number(left), number(right));
            case Value.Arithmetic(BinOp op, Value left, Value right) when op == BinOp.SUB ->
                    Props.minus(number(left), number(right));
            case Value.Made(ValueName.Stdlib.Operation operation, List<Value> args)
                    when library.answersTheNumber(operation) != null -> {
                used.add(new Proof.Used(operation, Proof.Taken.THE_NUMBER_IT_ANSWERS));
                yield form(library.answersTheNumber(operation), operation, args);
            }
            default -> LinearForm.atom(new LawNumber.AnArgument<>(value));
        };
    }

    // --- a law read over what an operation was handed --------------------------------------------

    /**
     * The elements a statement inside quantifiers is about: one for each container a quantifier
     * around it is over, and the innermost of them, which is the one a closure named inside is
     * handed.
     */
    record Elements<A>(Map<A, Element> of, Element innermost) {

        static <A> Elements<A> none() {
            return new Elements<>(Map.of(), null);
        }

        Elements<A> with(A container, Element element) {
            Map<A, Element> more = new HashMap<>(of);
            more.put(container, element);
            return new Elements<>(more, element);
        }
    }

    /** {@code statement}, over the arguments of {@code operation} by place, read over
     *  {@code args}. */
    LawProposition<Value> proposition(LawProposition<Integer> statement,
                                      ValueName.Stdlib.Operation operation, List<Value> args) {
        return proposition(statement, operation, args::get, Elements.none());
    }

    /** {@code form}, over the arguments of {@code operation} by place, read over {@code args}. */
    LinearForm<LawNumber<Value>> form(LinearForm<LawNumber<Integer>> form,
                                      ValueName.Stdlib.Operation operation, List<Value> args) {
        return form(form, operation, args::get, Elements.none());
    }

    /**
     * {@code statement}, over whatever {@code argument} reads its words as, with {@code elements}
     * what a statement inside a quantifier is about. {@code operation} is the one whose closure a
     * statement about what a closure answers is about.
     */
    <A> LawProposition<Value> proposition(LawProposition<A> statement,
                                          ValueName.Stdlib.Operation operation,
                                          Function<A, Value> argument, Elements<A> elements) {
        return switch (statement) {
            case LawProposition.Always<A>(boolean always) -> Props.always(always);
            case LawProposition.All<A>(List<LawProposition<A>> parts) ->
                    Props.all(parts.stream().map(part -> proposition(part, operation, argument,
                            elements)).toList());
            case LawProposition.Any<A>(List<LawProposition<A>> parts) ->
                    Props.any(parts.stream().map(part -> proposition(part, operation, argument,
                            elements)).toList());
            case LawProposition.Observed<A>(LawSubject<A> of, SideAnswered side) -> {
                LawProposition<Value> holding = side(subject(of, operation, argument, elements),
                        side.aspect());
                yield side.holds() ? holding : holding.denied();
            }
            case LawProposition.Compared<A>(var form, Rel states) ->
                    Props.compared(form(form, operation, argument, elements), states);
            case LawProposition.SomeElement<A>(A container, LawProposition<A> ofTheElement,
                                               boolean holds) -> {
                LawProposition<Value> some = some(argument.apply(container), each ->
                        proposition(ofTheElement, operation, argument,
                                elements.with(container, each)));
                yield holds ? some : some.denied();
            }
            case LawProposition.Same<A>(LawSubject<A> one, LawSubject<A> other, boolean holds) -> {
                LawProposition<Value> alike = same(subject(one, operation, argument, elements),
                        subject(other, operation, argument, elements));
                yield holds ? alike : alike.denied();
            }
        };
    }

    /** {@code form}, over whatever {@code argument} reads its words as. */
    <A> LinearForm<LawNumber<Value>> form(LinearForm<LawNumber<A>> form,
                                          ValueName.Stdlib.Operation operation,
                                          Function<A, Value> argument, Elements<A> elements) {
        LinearForm<LawNumber<Value>> out = LinearForm.constant(form.constant());
        for (Map.Entry<LawNumber<A>, ExactRatio> term : form.coefs().entrySet()) {
            LinearForm<LawNumber<Value>> read = switch (term.getKey()) {
                case LawNumber.AnArgument<A>(A at) -> number(argument.apply(at));
                case LawNumber.SizeOf<A>(LawSubject<A> of) ->
                        size(subject(of, operation, argument, elements));
                case LawNumber.HowManyMeet<A>(A container, LawProposition<A> ofTheElement) ->
                        howMany(argument.apply(container), each ->
                                proposition(ofTheElement, operation, argument,
                                        elements.with(container, each)));
            };
            out = Props.plus(out, Props.held(read.times(term.getValue())));
        }
        return out;
    }

    /** The value {@code subject} names. */
    private <A> Value subject(LawSubject<A> subject, ValueName.Stdlib.Operation operation,
                              Function<A, Value> argument, Elements<A> elements) {
        return switch (subject) {
            case LawSubject.Argument<A>(A at) -> argument.apply(at);
            case LawSubject.ElementOf<A>(A container) ->
                    elementNamed(elements.of().get(container)).value();
            case LawSubject.KeyOf<A>(A container) ->
                    elementNamed(elements.of().get(container)).key();
            case LawSubject.AnswerOf<A>(ValueName.Stdlib.Operation answering,
                                        List<LawSubject<A>> args) -> new Value.Made(answering,
                    args.stream().map(arg -> subject(arg, operation, argument, elements)).toList());
            case LawSubject.WhatTheClosureAnswers<A>(A closure) -> {
                Element handed = elementNamed(elements.innermost());
                ClosurePositions at = library.positions(operation);
                Value function = argument.apply(closure);
                int arity = function instanceof Value.Lambda(LibraryTerm.Closure written, var _,
                        var _)
                        ? written.params().size() : at == null ? 0
                        : Math.max(at.elementParam(), at.keyParam()) + 1;
                List<Value> handedOn = new ArrayList<>();
                for (int p = 0; p < arity; p++) {
                    if (at != null && p == at.elementParam()) {
                        handedOn.add(handed.value());
                    } else if (at != null && p == at.keyParam()) {
                        handedOn.add(handed.key());
                    } else {
                        // A parameter the element and its key are not handed on is one a law
                        // about the closure's answer on an element says nothing of.
                        throw new Stopped(new Library.Settled.Open(
                                new Unproved.NotOverItsArguments()));
                    }
                }
                yield new Value.AppliedTo(function, handedOn);
            }
        };
    }

    private static Element elementNamed(Element element) {
        if (element == null) {
            throw new Stopped(new Library.Settled.Open(new Unproved.NotOverItsArguments()));
        }
        return element;
    }

    // --- statements about the elements of a container -------------------------------------------

    /** That some element of {@code container} meets what {@code of} makes of it. */
    LawProposition<Value> some(Value container, Function<Element, LawProposition<Value>> of) {
        return switch (container) {
            case Value.Listed(List<Value> elements) -> Props.any(elements.stream()
                    .map(each -> of.apply(itself(each))).toList());
            case Value.Joined(Value left, Value right) ->
                    Props.either(some(left, of), some(right, of));
            case Value.NothingYet _ -> Props.always(false);
            case Value.OneMore(Value walked, Value next) ->
                    Props.either(some(walked, of), of.apply(itself(next)));
            case Value.AsEntries(Value entries) -> some(entries, entry -> of.apply(unpacked(entry)));
            case Value.Made(ValueName.Stdlib.Operation operation, List<Value> args)
                    when library.listing(operation) != null ->
                    throughTheListing(operation, args, of, this::some);
            default -> {
                Element each = elementOf(container);
                yield new LawProposition.SomeElement<>(container, of.apply(each), true);
            }
        };
    }

    /** How many elements of {@code container} meet what {@code of} makes of them. */
    LinearForm<LawNumber<Value>> howMany(Value container,
                                         Function<Element, LawProposition<Value>> of) {
        return switch (container) {
            case Value.Listed(List<Value> elements) -> {
                LinearForm<LawNumber<Value>> out = Props.constant(0);
                for (Value each : elements) {
                    out = Props.plus(out, oneIf(each, of));
                }
                yield out;
            }
            case Value.Joined(Value left, Value right) ->
                    Props.plus(howMany(left, of), howMany(right, of));
            case Value.NothingYet _ -> Props.constant(0);
            case Value.OneMore(Value walked, Value next) ->
                    Props.plus(howMany(walked, of), oneIf(next, of));
            case Value.AsEntries(Value entries) ->
                    howMany(entries, entry -> of.apply(unpacked(entry)));
            case Value.Made(ValueName.Stdlib.Operation operation, List<Value> args)
                    when library.listing(operation) != null ->
                    throughTheListing(operation, args, of, this::howMany);
            default -> {
                Element each = elementOf(container);
                yield LinearForm.atom(new LawNumber.HowManyMeet<>(container, of.apply(each)));
            }
        };
    }

    /** One where {@code element} meets what {@code of} makes of it and nought where it does not,
     *  as the count of a list holding it alone. */
    private LinearForm<LawNumber<Value>> oneIf(Value element,
                                               Function<Element, LawProposition<Value>> of) {
        Value alone = new Value.Listed(List.of(element));
        return LinearForm.atom(new LawNumber.HowManyMeet<>(alone,
                of.apply(itself(element))));
    }

    /** The element a statement about the elements of {@code container} is about. */
    private static Element elementOf(Value container) {
        return itself(new Value.ElementOf(container));
    }

    /** {@code element} as an element of whatever holds it, under whatever key it is filed under. */
    private static Element itself(Value element) {
        return new Element(element, new Value.KeyOf(element));
    }

    /** An entry of a map, a pair of its key and its value, read as the value under the key. */
    private static Element unpacked(Element entry) {
        return new Element(componentOf(entry.value(), 1), componentOf(entry.value(), 0));
    }

    /**
     * A statement about the elements of what {@code operation} answers, read as one about the
     * argument whose elements it lists — the entries of a map read as its values, each under its
     * key.
     */
    private <T> T throughTheListing(ValueName.Stdlib.Operation operation, List<Value> args,
                                    Function<Element, LawProposition<Value>> of,
                                    BiFunction<Value, Function<Element, LawProposition<Value>>, T>
                                            over) {
        return switch (listing(operation)) {
            case AppliedClosures.Listing.EveryElementOf(int argument, var _) ->
                    over.apply(args.get(argument), of);
            case AppliedClosures.Listing.EveryEntryOf(int argument) ->
                    over.apply(args.get(argument), each -> of.apply(itself(
                            new Value.Tupled(List.of(each.key(), each.value())))));
            case AppliedClosures.Listing.AtMostOneElementOf _ ->
                    throw new Stopped(new Library.Settled.Open(
                            new Unproved.NothingSettles(operation, OperationLaw.Observed.SIZE)));
        };
    }
}
