package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.abort.AbortKind;
import souther.compiler.abort.AbortSet;
import souther.compiler.abort.AbortSites;
import souther.compiler.abort.GetsPast;
import souther.compiler.ast.Hir;
import souther.compiler.check.WhatARunMayEndFor.Endings;
import souther.compiler.core.KernelContracts;
import souther.compiler.semantics.Combinator;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.semantics.PieceOfAnElement;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.ReachName;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What each operation of a library may end a run without a value for, over every call of it and
 * everything the call runs: a kernel's own is {@link KernelContracts}', and one the library writes in
 * the language ends a run for what its body does. {@link Endings.Known} of none is said only where
 * nothing it runs ends one, whatever it is handed.
 *
 * <p>Read off the body from the same owners, and never classified a second time: what an operator in
 * it ends a run for is {@link AbortSites}', and what another operation it calls ends one for is this
 * table's own. A body's operands carry no type, so an operator is answered by the sites every typing
 * of it is written as ({@link AbortSites#ofAnOperatorOfAnyType}), which is no less than the sites of
 * one typing end a run for. {@link AbortSites} answers what each site ends a run for on its own; what
 * a site runs beyond itself is this reading's to follow, and an invariant a construction runs is not
 * in this tree.
 *
 * <p>A function runs where it is applied, and every place one is applied is not known here: a
 * function the body is handed or binds, applied by the body; a parameter the library applies in a
 * body of its own; and a kernel handed a function, whose contract answers for what the kernel itself
 * does and not for what the function it applies does. So a closure the body builds, and an operation
 * of the library it names without applying, run nothing of their own where they stand.
 *
 * <p>Also not known: a construction, whose invariant is its declaration's; an attempt at one, whose
 * refusal takes another arm; an operation coming back to itself, directly or through another, until
 * the cycle is read, and this reads none.
 *
 * <p>A pure function of a library, and the shipped one's is held once — the pattern
 * {@link LibraryReadThrough} follows.
 */
final class LibraryEndings {

    private static final Endings NONE = new Endings.Known(AbortSet.NONE);
    private static final Endings NOT_KNOWN = new Endings.NotKnown();

    private final Map<ValueName.Stdlib.Operation, Endings> ending;

    private final Map<ValueName.Stdlib.Operation, Endings> ofItsOwn;

    private final Map<ValueName.Stdlib.Operation, GetsPast> completions;

    private LibraryEndings(Map<ValueName.Stdlib.Operation, Endings> ending,
                           Map<ValueName.Stdlib.Operation, Endings> ofItsOwn,
                           Map<ValueName.Stdlib.Operation, GetsPast> completions) {
        this.ending = Map.copyOf(ending);
        this.ofItsOwn = Map.copyOf(ofItsOwn);
        this.completions = Map.copyOf(completions);
    }

    /** What every operation of {@code library}, and every sugar for one, ends a run for. */
    static LibraryEndings of(Stdlib library) {
        return of(library, OperationFactBinder.bindAll(library));
    }

    /**
     * The same, and what each ends a run for apart from the functions it is handed, read with
     * {@code facts}, what is proved of the library's operations.
     */
    static LibraryEndings of(Stdlib library, BoundOperationFacts facts) {
        Reading whole = new Reading(library, null);
        library.entries().keySet().forEach(whole::of);
        library.rewrites().keySet().forEach(whole::of);
        Reading apart = new Reading(library, facts);
        library.entries().keySet().forEach(apart::of);
        library.rewrites().keySet().forEach(apart::of);
        Map<ValueName.Stdlib.Operation, GetsPast> completions = new HashMap<>();
        Map<ValueName.Stdlib.Operation, Endings> own = new HashMap<>(apart.settled);
        own.forEach((operation, ends) -> completions.put(operation,
                apart.walksNoFurtherThanItsList(operation) ? new GetsPast.Always()
                        : completionOf(library, facts, operation, ends, apart)));
        return new LibraryEndings(whole.settled, apart.settled, completions);
    }

    /**
     * Where a call of {@code operation} answers apart from the functions it is handed, of what it
     * ends a run for apart from them ({@code own}).
     *
     * <p>Where that is nothing, always. Otherwise from the owner of how the answer is built: one
     * assembled of a piece for each element of a list of any number of elements answers where the
     * pieces together fit, since it puts them end to end along the walk and holds no more on the
     * way ({@link BoundOperationFacts#assembles}); a kernel answers where its contract says
     * ({@link KernelContracts#completionOf}); and an operation whose body answers, in each way it
     * may go, what an operator answering where its collection fits answers of the operation's
     * parameters, answers where the most any of those may hold fits
     * ({@link Reading#answerOfTheBody}). Nothing else is said here.
     */
    private static GetsPast completionOf(Stdlib library, BoundOperationFacts facts,
                                           ValueName.Stdlib.Operation operation, Endings own,
                                           Reading apart) {
        if (own.endsNone()) {
            return new GetsPast.Always();
        }
        BoundOperationFacts.Assembled assembled = facts.assembles(operation);
        if (assembled != null && assembled.piece() == PieceOfAnElement.WHAT_THE_CLOSURE_ANSWERS) {
            return new GetsPast.WhereTheAnswerFits(new GetsPast.AnswerSize.PiecesOf(
                    assembled.source().position(), assembled.closure().position()));
        }
        Stdlib.Intrinsic intrinsic = library.intrinsicOf(operation);
        if (intrinsic != null) {
            return KernelContracts.completionOf(intrinsic.kernel());
        }
        Hir.FnDef declaration = library.helpers().get(operation);
        Stdlib.Entry entry = library.entry(operation);
        if (declaration != null && entry != null) {
            GetsPast.AnswerSize.SumOf answer = apart.answerOfTheBody(declaration,
                    declaration.writtenBody(), entry.signature().result());
            if (answer != null) {
                return new GetsPast.WhereTheAnswerFits(answer);
            }
        }
        return new GetsPast.NotKnown();
    }

    /** Which of {@code declaration}'s parameters {@code e} reads, as it stands, or -1. */
    private static int parameterRead(Hir.FnDef declaration, Hir.Expr e) {
        if (!(e instanceof Hir.Var.Denoting name)
                || !(name.reachedAs() instanceof ReachName.InScope(ValueName.Local(var _, var id)))) {
            return -1;
        }
        for (int at = 0; at < declaration.params().size(); at++) {
            if (declaration.params().get(at).binder().binding().equals(id)) {
                return at;
            }
        }
        return -1;
    }

    /**
     * Where a call of {@code operation} answers apart from the functions it is handed, for a
     * caller that asks the body of each of those itself ({@link #completionOf}).
     *
     * @throws IllegalArgumentException where the library has no such operation
     */
    GetsPast completionApartFromWhatItIsHanded(ValueName.Stdlib.Operation operation) {
        GetsPast found = completions.get(operation);
        if (found == null) {
            throw new IllegalArgumentException(
                    "`" + operation.qualified() + "` is no operation of the library read");
        }
        return found;
    }

    /** The shipped library's, which is the same for every compilation. */
    static LibraryEndings shipped() {
        return Shipped.ENDINGS;
    }

    private static final class Shipped {
        private static final LibraryEndings ENDINGS =
                of(DefaultStdlib.get(), DefaultBoundOperationFacts.get());
    }

    /**
     * What {@code operation} ends a run for.
     *
     * @throws IllegalArgumentException where the library has no such operation — never answered as
     *     not known, which says the operation was read and its body did not say
     */
    Endings of(ValueName.Stdlib.Operation operation) {
        Endings found = ending.get(operation);
        if (found == null) {
            throw new IllegalArgumentException(
                    "`" + operation.qualified() + "` is no operation of the library read");
        }
        return found;
    }

    /**
     * What {@code operation} ends a run for apart from what the functions it is handed do, for a
     * caller that asks the body of each of those itself: the kernel's own contract, or what its
     * body does where none of them is applied. A closure its body builds is read as run, wherever
     * the body applies it. Asked without reading the functions handed, it says less than the run
     * does — what {@link #of(ValueName.Stdlib.Operation)} answers is that.
     *
     * @throws IllegalArgumentException where the library has no such operation
     */
    Endings apartFromWhatItIsHanded(ValueName.Stdlib.Operation operation) {
        Endings found = ofItsOwn.get(operation);
        if (found == null) {
            throw new IllegalArgumentException(
                    "`" + operation.qualified() + "` is no operation of the library read");
        }
        return found;
    }

    /**
     * One reading of a library, each operation settled once.
     *
     * <p>With {@code facts}, apart from the functions each operation is handed: a function the
     * body applies that is no operation of the library ends nothing here, since one handed is its
     * caller's to read and one the body built is read where it is built. And two operations end
     * nothing of their own by what is proved of them rather than by a reading of their bodies,
     * which a body cannot say: the walk, and one that assembles its answer of at most one element
     * for each element of a list ({@link #endsNothingOfItsOwn}).
     */
    private static final class Reading {
        private final Stdlib library;
        private final BoundOperationFacts facts;
        private final Map<ValueName.Stdlib.Operation, Endings> settled = new HashMap<>();
        private final Set<ValueName.Stdlib.Operation> reading = new HashSet<>();

        private Reading(Stdlib library, BoundOperationFacts facts) {
            this.library = library;
            this.facts = facts;
        }

        /**
         * Whether {@code operation}, apart from the functions it is handed, ends no run by what is
         * proved of it.
         *
         * <p>The walk: it reads the element at its index and goes on from the next only where
         * there is one, and there the index is below the list's length, which an {@code Int}
         * holds, so the next index has a place; and it ends ({@code TheWalkEnds}, from the same
         * law of reading an element). What is left is the step, which it is handed.
         *
         * <p>An operation whose answer is a piece of at most one element for each element of a
         * list, put end to end along the walk ({@link BoundOperationFacts#assembles}): what it has
         * put together after an element is no longer than the part of the list walked to there,
         * which is no longer than a list that has a place, so each joining has a place too. What
         * is left is the closure that makes a piece, which it is handed. A piece of any number of
         * elements is not this — what the closure answers on one element can be as long as a list
         * holds — and is read off the body.
         */
        private boolean endsNothingOfItsOwn(ValueName.Stdlib.Operation operation) {
            if (operation.equals(library.walk().operation())) {
                return true;
            }
            BoundOperationFacts.Assembled assembled = facts.assembles(operation);
            return assembled != null
                    && assembled.piece() != PieceOfAnElement.WHAT_THE_CLOSURE_ANSWERS;
        }

        /**
         * What {@code operation} ends a run for. One met again while its own body is being read is
         * on a cycle, and so is everything read between the two meetings, which comes back to it.
         */
        Endings of(ValueName.Stdlib.Operation operation) {
            Endings done = settled.get(operation);
            if (done != null) {
                return done;
            }
            if (!reading.add(operation)) {
                return NOT_KNOWN;
            }
            Endings out = worked(operation);
            reading.remove(operation);
            settled.put(operation, out);
            return out;
        }

        private Endings worked(ValueName.Stdlib.Operation operation) {
            if (facts != null && endsNothingOfItsOwn(operation)) {
                return NONE;
            }
            Stdlib.Intrinsic intrinsic = library.intrinsicOf(operation);
            if (intrinsic != null) {
                return handedAFunction(operation) && facts == null ? NOT_KNOWN
                        : new Endings.Known(KernelContracts.abortsOf(intrinsic.kernel()));
            }
            Hir.FnDef declaration = library.helpers().get(operation);
            if (declaration != null) {
                return of(declaration.writtenBody());
            }
            Stdlib.Rewrite rewrite = library.rewriteOf(operation);
            if (rewrite != null) {
                return of(rewrite.target());
            }
            throw new IllegalArgumentException(
                    "`" + operation.qualified() + "` is no operation of this library");
        }

        /**
         * Whether {@code operation}, apart from the functions it is handed, ends no run because
         * its body walks a list once and builds no more than it walks.
         *
         * <p>The body is one walk of the library, and nothing else in it ends a run. The walk
         * starts from a collection holding nothing, or from a tuple of such collections and of
         * whole numbers written out; and its step answers what it carries with each collection
         * as it was or with at most one element put into it, by an operation that answers where
         * the collection fits ({@link GetsPast.WhereTheAnswerFits}), and each number as it was
         * or with a number written out added to it. Nothing else in the step ends a run.
         *
         * <p>Then by induction on the elements walked, after {@code k} of them each collection
         * holds at most {@code k} and each number is at most {@code k} times what is added to it:
         * no more than the list holds, which has a place, and no more than an {@code Int} holds,
         * since a list holds fewer than the square root of what an {@code Int} does and what is
         * added is written out no larger. So every collection put together on the way fits, and
         * every sum worked out on the way is an {@code Int}.
         */
        boolean walksNoFurtherThanItsList(ValueName.Stdlib.Operation operation) {
            Hir.FnDef declaration = library.helpers().get(operation);
            if (declaration == null || facts == null) {
                return false;
            }
            List<Hir.Apply> walks = new ArrayList<>();
            boolean[] endsElsewhere = {false};
            visitOutsideTheWalk(declaration.writtenBody(), walks, endsElsewhere);
            if (walks.size() != 1 || endsElsewhere[0]) {
                return false;
            }
            Hir.Apply walk = walks.getFirst();
            ValueName.Stdlib.Operation walked = ((ReachName.OfLibrary) ((Hir.Var.Denoting)
                    walk.function()).reachedAs()).denotes();
            Reductions.Reduction reduction = Reductions.of(walked);
            Combinator handing = Combinators.of(walked);
            List<Hir.Expr> args = walk.args();
            if (reduction.seedArg() >= args.size() || handing.containerArg() >= args.size()
                    || handing.closureArg() >= args.size()
                    || !(args.get(handing.closureArg()) instanceof Hir.Block step)
                    || reduction.accumulatorParam() >= step.params().size()) {
                return false;
            }
            for (int at = 0; at < args.size(); at++) {
                if (at != handing.closureArg() && !of(args.get(at)).endsNone()) {
                    return false;
                }
            }
            List<Boolean> counts = seedOf(args.get(reduction.seedArg()));
            if (counts == null) {
                return false;
            }
            Set<BindingId> carried = new HashSet<>();
            carried.add(step.params().get(reduction.accumulatorParam()).binding());
            return answersWhatItCarriedGrown(step.body(), carried, counts, new HashMap<>(),
                    new HashMap<>());
        }

        /**
         * Every walk of the library under {@code e}, not looking into one, and whether anything
         * else under it ends a run.
         */
        private void visitOutsideTheWalk(Hir.Expr e, List<Hir.Apply> walks,
                                         boolean[] endsElsewhere) {
            if (e instanceof Hir.Apply apply && apply.function() instanceof Hir.Var.Denoting callee
                    && callee.reachedAs() instanceof ReachName.OfLibrary library
                    && Reductions.of(library.denotes()) != null
                    && Combinators.of(library.denotes()) != null) {
                walks.add(apply);
                return;
            }
            if (!itself(e).endsNone()) {
                endsElsewhere[0] = true;
            }
            Hir.forEachChild(e, child -> visitOutsideTheWalk(child, walks, endsElsewhere));
        }

        /**
         * What the walk starts from, as a list of its parts each saying whether it is a number:
         * one part where it is a collection holding nothing, and one for each element where it is
         * a tuple of those and of whole numbers written out — or null where it is anything else.
         */
        private List<Boolean> seedOf(Hir.Expr seed) {
            if (holdsNothing(seed)) {
                return List.of(false);
            }
            if (!(seed instanceof Hir.Tuple tuple)) {
                return null;
            }
            List<Boolean> out = new ArrayList<>();
            for (Hir.Expr each : tuple.elements()) {
                if (each instanceof Hir.IntLit) {
                    out.add(true);
                } else if (holdsNothing(each)) {
                    out.add(false);
                } else {
                    return null;
                }
            }
            return out;
        }

        /** Whether {@code e} is a collection holding nothing: written out empty, or an operation
         *  of the library taking nothing whose answer the library says holds none. */
        private boolean holdsNothing(Hir.Expr e) {
            if (e instanceof Hir.ListLit written) {
                return written.elements().isEmpty();
            }
            if (!(e instanceof Hir.Var.Denoting name)
                    || !(name.reachedAs() instanceof ReachName.OfLibrary library)) {
                return false;
            }
            return facts.settled(library.denotes(), OperationLaw.Observed.SIZE)
                    instanceof BoundOperationFacts.Settled.ByALaw(
                            OperationLaw.Size<DeclaredArgument> law, var _)
                    && law.unconditional() != null && law.unconditional().coefs().isEmpty()
                    && law.unconditional().constant().signum() == 0;
        }

        /**
         * Whether {@code body} answers what is carried under any of {@code carried}, of
         * {@code counts.size()} parts, with each part grown as {@link #walksNoFurtherThanItsList}
         * says, and ends a run nowhere else. {@code parts} holds the names bound to a part of it,
         * and {@code added} the names bound to a number part with a number written out added.
         */
        private boolean answersWhatItCarriedGrown(Hir.Expr body, Set<BindingId> carried,
                                                  List<Boolean> counts,
                                                  Map<BindingId, Integer> parts,
                                                  Map<BindingId, Integer> added) {
            switch (body) {
                case Hir.LetIn let -> {
                    BindingId name = let.binder().binding();
                    Integer part = partRead(let.value(), carried, counts, parts);
                    if (let.value() instanceof Hir.Var.Denoting read && isCarried(read, carried)) {
                        carried.add(name);
                    } else if (part != null) {
                        parts.put(name, part);
                    } else if (counted(let.value(), counts, parts) != null) {
                        added.put(name, counted(let.value(), counts, parts));
                    } else if (!of(let.value()).endsNone()) {
                        return false;
                    }
                    return answersWhatItCarriedGrown(let.body(), carried, counts, parts, added);
                }
                case Hir.If fork -> {
                    return of(fork.cond()).endsNone()
                            && answersWhatItCarriedGrown(fork.then(), carried, counts, parts,
                                    added)
                            && answersWhatItCarriedGrown(fork.els(), carried, counts, parts,
                                    added);
                }
                case Hir.Tuple tuple -> {
                    if (tuple.elements().size() != counts.size()) {
                        return false;
                    }
                    for (int at = 0; at < counts.size(); at++) {
                        Hir.Expr each = tuple.elements().get(at);
                        boolean grown = counts.get(at)
                                ? isPart(each, at, parts) || addedTo(each, at, added, counts, parts)
                                : isPart(each, at, parts) || putInOne(each, at, parts);
                        if (!grown) {
                            return false;
                        }
                    }
                    return true;
                }
                default -> {
                    if (counts.size() != 1 || counts.getFirst()) {
                        return false;
                    }
                    Map<BindingId, Integer> whole = new HashMap<>(parts);
                    carried.forEach(name -> whole.put(name, 0));
                    return isPart(body, 0, whole) || putInOne(body, 0, whole);
                }
            }
        }

        /** Whether {@code read} reads what is carried, under one of {@code carried}. */
        private static boolean isCarried(Hir.Var.Denoting read, Set<BindingId> carried) {
            return read.reachedAs() instanceof ReachName.InScope(ValueName.Local(var _, var id))
                    && carried.contains(id);
        }

        /** Which part of what is carried {@code e} reads as it is, or null. */
        private static Integer partRead(Hir.Expr e, Set<BindingId> carried, List<Boolean> counts,
                                        Map<BindingId, Integer> parts) {
            if (e instanceof Hir.TupleGet get && get.tuple() instanceof Hir.Var.Denoting read
                    && isCarried(read, carried) && get.index() < counts.size()) {
                return get.index();
            }
            return e instanceof Hir.Var.Denoting read
                    && read.reachedAs() instanceof ReachName.InScope(ValueName.Local(var _, var id))
                    ? parts.get(id) : null;
        }

        /** Whether {@code e} reads part {@code at} of what is carried, as it is. */
        private static boolean isPart(Hir.Expr e, int at, Map<BindingId, Integer> parts) {
            return e instanceof Hir.Var.Denoting read
                    && read.reachedAs() instanceof ReachName.InScope(ValueName.Local(var _, var id))
                    && Integer.valueOf(at).equals(parts.get(id));
        }

        /** Which number part {@code e} adds a number written out, no larger than a list holds,
         *  to — or null. */
        private static Integer counted(Hir.Expr e, List<Boolean> counts,
                                       Map<BindingId, Integer> parts) {
            if (!(e instanceof Hir.Binary sum) || sum.op() != BinOp.ADD
                    || !(sum.right() instanceof Hir.IntLit step) || step.value() < 0
                    || step.value() > Integer.MAX_VALUE) {
                return null;
            }
            for (int at = 0; at < counts.size(); at++) {
                if (counts.get(at) && isPart(sum.left(), at, parts)) {
                    return at;
                }
            }
            return null;
        }

        /** Whether {@code e} is number part {@code at} with a number written out added. */
        private static boolean addedTo(Hir.Expr e, int at, Map<BindingId, Integer> added,
                                       List<Boolean> counts, Map<BindingId, Integer> parts) {
            if (e instanceof Hir.Var.Denoting read
                    && read.reachedAs() instanceof ReachName.InScope(ValueName.Local(var _, var id))
                    && Integer.valueOf(at).equals(added.get(id))) {
                return true;
            }
            return Integer.valueOf(at).equals(counted(e, counts, parts));
        }

        /**
         * Whether {@code e} is collection part {@code at} with at most one element put in, by an
         * operation answering where the collection fits whose answer holds the part and one more
         * at most, and whatever else it is handed ends no run.
         */
        private boolean putInOne(Hir.Expr e, int at, Map<BindingId, Integer> parts) {
            if (e instanceof Hir.Binary join && join.op() == BinOp.CONCAT) {
                return isPart(join.left(), at, parts) && join.right() instanceof Hir.ListLit one
                        && one.elements().size() <= 1
                        && one.elements().stream().allMatch(each -> of(each).endsNone());
            }
            if (!(e instanceof Hir.Apply apply)
                    || !(apply.function() instanceof Hir.Var.Denoting callee)
                    || !(callee.reachedAs() instanceof ReachName.OfLibrary library)) {
                return false;
            }
            Stdlib.Intrinsic intrinsic = this.library.intrinsicOf(library.denotes());
            if (intrinsic == null || !(KernelContracts.completionOf(intrinsic.kernel())
                    instanceof GetsPast.WhereTheAnswerFits(
                            GetsPast.AnswerSize.SumOf(List<Integer> operands, int more)))
                    || operands.size() != 1 || more > 1
                    || operands.getFirst() >= apply.args().size()
                    || !isPart(apply.args().get(operands.getFirst()), at, parts)) {
                return false;
            }
            for (int each = 0; each < apply.args().size(); each++) {
                if (each != operands.getFirst() && !of(apply.args().get(each)).endsNone()) {
                    return false;
                }
            }
            return true;
        }

        /**
         * How many elements {@code e}, standing in {@code declaration}'s body and answering a
         * value of {@code answer}, holds at most, where it ends a run only where that collection
         * fits: in each way it may go — an arm of a choice, the body of a {@code let} — an
         * operator answering where its collection fits applied to the operation's parameters
         * ({@link KernelContracts#completionOf}, {@link AbortSites#completionOfAnOperator}), and
         * nothing else on the way ending a run. The most of all the ways is what any of them
         * holds at most. Null where it is not that.
         */
        GetsPast.AnswerSize.SumOf answerOfTheBody(Hir.FnDef declaration, Hir.Expr e,
                                                    Type answer) {
            switch (e) {
                case Hir.LetIn let -> {
                    return of(let.value()).endsNone()
                            ? answerOfTheBody(declaration, let.body(), answer) : null;
                }
                case Hir.If fork -> {
                    return of(fork.cond()).endsNone()
                            ? either(answerOfTheBody(declaration, fork.then(), answer),
                                    answerOfTheBody(declaration, fork.els(), answer))
                            : null;
                }
                case Hir.Match match -> {
                    if (!of(match.scrutinee()).endsNone() || match.cases().isEmpty()) {
                        return null;
                    }
                    GetsPast.AnswerSize.SumOf out = null;
                    for (Hir.Case arm : match.cases()) {
                        GetsPast.AnswerSize.SumOf one =
                                answerOfTheBody(declaration, arm.body(), answer);
                        if (one == null) {
                            return null;
                        }
                        out = out == null ? one : either(out, one);
                    }
                    return out;
                }
                case Hir.Binary binary -> {
                    return ofTheParameters(declaration,
                            AbortSites.completionOfAnOperator(binary.op(), answer),
                            List.of(binary.left(), binary.right()));
                }
                case Hir.Apply apply when apply.function() instanceof Hir.Var.Denoting callee
                        && callee.reachedAs() instanceof ReachName.OfLibrary called
                        && library.intrinsicOf(called.denotes()) != null -> {
                    return ofTheParameters(declaration, KernelContracts.completionOf(
                            library.intrinsicOf(called.denotes()).kernel()), apply.args());
                }
                default -> {
                    return null;
                }
            }
        }

        /**
         * {@code completion} of a site handed {@code operands}, as a count of the operation's
         * parameters: each operand it counts is a parameter as it stands, and every other operand
         * ends no run. Null where it is not that.
         */
        private GetsPast.AnswerSize.SumOf ofTheParameters(Hir.FnDef declaration,
                                                            GetsPast completion,
                                                            List<Hir.Expr> operands) {
            if (!(completion instanceof GetsPast.WhereTheAnswerFits(
                    GetsPast.AnswerSize.SumOf(List<Integer> counted, int more)))) {
                return null;
            }
            List<Integer> parameters = new ArrayList<>();
            for (int at = 0; at < operands.size(); at++) {
                if (counted.contains(at)) {
                    int parameter = parameterRead(declaration, operands.get(at));
                    if (parameter < 0) {
                        return null;
                    }
                    parameters.add(parameter);
                } else if (!of(operands.get(at)).endsNone()) {
                    return null;
                }
            }
            return new GetsPast.AnswerSize.SumOf(parameters, more);
        }

        /** What holds as many as either of {@code one} and {@code other} at most. */
        private static GetsPast.AnswerSize.SumOf either(GetsPast.AnswerSize.SumOf one,
                                                          GetsPast.AnswerSize.SumOf other) {
            if (one == null || other == null) {
                return null;
            }
            Set<Integer> operands = new LinkedHashSet<>(one.operands());
            operands.addAll(other.operands());
            return new GetsPast.AnswerSize.SumOf(List.copyOf(operands),
                    Math.max(one.more(), other.more()));
        }

        /** Whether the kernel {@code operation} is takes a function, which it may apply. */
        private boolean handedAFunction(ValueName.Stdlib.Operation operation) {
            Stdlib.Entry entry = library.entry(operation);
            if (entry == null) {
                throw new IllegalStateException(
                        "`" + operation.qualified() + "` is a kernel the library declares no entry for");
            }
            return entry.signature().params().stream().anyMatch(Type.FnOf.class::isInstance);
        }

        /** What working {@code e} out, and everything under it it works out, ends a run for — and,
         *  apart from the functions handed, a closure built under it as well, as run. */
        private Endings of(Hir.Expr e) {
            Endings[] out = {itself(e)};
            if (e instanceof Hir.Block && facts == null) {
                return out[0];
            }
            Hir.forEachChild(e, child -> {
                if (out[0] instanceof Endings.Known) {
                    out[0] = out[0].and(of(child));
                }
            });
            return out[0];
        }

        /**
         * What {@code e} itself, and none of what it is made of, ends a run for.
         *
         * <p>Exhaustive over {@link Hir.Expr}, so a node kind added later stops the build here.
         */
        private Endings itself(Hir.Expr e) {
            return switch (e) {
                case Hir.Binary binary -> operator(binary);
                case Hir.Neg _ -> new Endings.Known(AbortSites.ofANegationOfAnyType());
                case Hir.Unreachable _ -> new Endings.Known(AbortSites.ofAnUnreachableWherever());
                case Hir.Apply apply -> applied(apply);
                case Hir.Var name -> read(name);
                case Hir.NewData _, Hir.IfConstructed _, Hir.Expansion _, Hir.Materialised _,
                     Hir.ValueBuild _, Hir.ValueInvocation _ -> NOT_KNOWN;
                case Hir.IntLit _, Hir.DecimalLit _, Hir.StringLit _, Hir.BoolLit _,
                     Hir.FieldAccess _, Hir.Match _, Hir.If _, Hir.ListLit _, Hir.RowCollection _,
                     Hir.ListComp _, Hir.LetIn _, Hir.Block _, Hir.Tuple _, Hir.TupleGet _ -> NONE;
            };
        }

        /**
         * What the sites an operator is written as end a run for ({@link AbortSites}), where that
         * is all they run. Where an unheld invariant is among the reasons, a construction may stand
         * there, and so may the invariant clauses it runs: those are its declaration's, not in this
         * tree, and what they end a run for is not known here.
         */
        private static Endings operator(Hir.Binary binary) {
            AbortSet sites = AbortSites.ofAnOperatorOfAnyType(binary.op());
            return sites.contains(AbortKind.INVARIANT_NOT_HELD)
                    ? NOT_KNOWN : new Endings.Known(sites);
        }

        /** An application of an operation of the library is what that operation ends a run for;
         *  of anything else, a function this body is handed or binds, it is not known — and apart
         *  from the functions handed, nothing: one handed is the caller's, and one built is read
         *  where it is built. */
        private Endings applied(Hir.Apply apply) {
            return apply.function() instanceof Hir.Var.Denoting callee
                    && callee.reachedAs() instanceof ReachName.OfLibrary library
                    ? of(library.denotes()) : facts == null ? NOT_KNOWN : NONE;
        }

        /**
         * A name read: an operation of the library that takes nothing is worked out where it is
         * read, and anything else names a value already worked out or a function, which runs where
         * it is applied. A name that names nothing says nothing of what it reads.
         */
        private Endings read(Hir.Var name) {
            return switch (name) {
                case Hir.Var.Denoting denoting
                        when denoting.reachedAs() instanceof ReachName.OfLibrary library -> {
                    Stdlib.Entry entry = this.library.entry(library.denotes());
                    yield entry != null && entry.signature().params().isEmpty()
                            ? of(library.denotes()) : NONE;
                }
                case Hir.Var.Denoting _ -> NONE;
                case Hir.Var.Unanswered _ -> NOT_KNOWN;
            };
        }
    }
}
