package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.abort.AbortKind;
import souther.compiler.abort.AbortSet;
import souther.compiler.abort.AbortSites;
import souther.compiler.abort.GetsPast;
import souther.compiler.check.WhatARunMayEndFor.Endings;
import souther.compiler.core.KernelContracts;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.proof.AskedOnTheWay;
import souther.compiler.proof.ByPlace;
import souther.compiler.proof.HeldOnTheWay;
import souther.compiler.proof.LibraryProver;
import souther.compiler.proof.LibraryTerm;
import souther.compiler.proof.LibraryTerms;
import souther.compiler.proof.OnTheWay;
import souther.compiler.proof.WhereReached;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawSubject;
import souther.compiler.semantics.PieceOfAnElement;
import souther.compiler.semantics.WhereAnOperatorAnswers;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.BinOp;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Supplier;

/**
 * What each operation of a library may end a run without a value for, and where it answers, apart
 * from the functions it is handed: a kernel's own is {@link KernelContracts}', and one the library
 * writes in the language ends a run for what its body does.
 *
 * <p>A body is read as the library's proofs read it ({@link LibraryTerm}), and never through a
 * reading of the tree of its own: what it applies, binds and chooses between is that term's to say.
 * What an operator in it ends a run for is {@link AbortSites}', at the type the proofs read it to
 * answer ({@link LibraryProver#typesOf}), or over every typing where they read none; what another
 * operation it calls ends one for is this table's own. A site that may hold too much — what it
 * builds holding more than a collection does, or the whole number it works out passing an
 * {@code Int} — ends no run for that where the proofs show it holds no more than something the
 * operation is handed, or lies inside the type, wherever it is reached; and the operation answers
 * where what those sites hold fits where that is all they are shown to hold. A site is asked
 * where the body reaches it, as the proofs read the way there — a fork's condition, an option
 * present or not, the left of {@code &&} and {@code ||}: one reached on no way ends none, and a
 * division whose divisor is never nought where it is reached ends none for that. Each is said
 * only of a site whose every run the proofs read, and all of it off one reading of the ways
 * ({@link LibraryProver#onTheWay}).
 *
 * <p>Apart from the functions handed: a function the body applies that is no operation of the
 * library is the caller's to read where it is handed, and one the body builds is read where it is
 * built, as run, wherever the body hands it. So what an operation ends a run for whole, with what
 * it is handed run as well, is this where it is handed no function, and not known where it is.
 *
 * <p>Also not known: a construction, whose invariant is its declaration's; anything the proofs'
 * reading has no word for; an operation handed over by its name; and an operation coming back to
 * itself, directly or through another, until the cycle is read, and this reads none.
 *
 * <p>A pure function of a library, and the shipped one's is held once — the pattern
 * {@link LibraryReadThrough} follows.
 */
final class LibraryEndings {

    private static final Endings NONE = new Endings.Known(AbortSet.NONE);
    private static final Endings NOT_KNOWN = new Endings.NotKnown();

    private final Stdlib library;

    private final Supplier<BoundOperationFacts> facts;

    /**
     * The reading of the library, made on the first asking, with what is proved of the library —
     * proving that is most of the cost of reading one. Each operation is read where it is first
     * asked, with what it calls. Which is asked first changes no answer: one met again while it is
     * being read is not known, and so is everything calling it.
     */
    private Reading reading;

    private LibraryEndings(Stdlib library, Supplier<BoundOperationFacts> facts) {
        this.library = library;
        this.facts = facts;
    }

    /** What every operation of {@code library}, and every sugar for one, ends a run for. */
    static LibraryEndings of(Stdlib library) {
        return of(library, () -> OperationFactBinder.bindAll(library));
    }

    /** The same, read with {@code facts}, what is proved of the library's operations. */
    static LibraryEndings of(Stdlib library, Supplier<BoundOperationFacts> facts) {
        return new LibraryEndings(library, facts);
    }

    /** What an operation ends a run for apart from what it is handed, and where it answers. */
    private record Read(Endings own, GetsPast completion) {}

    private synchronized Read readOf(ValueName.Stdlib.Operation operation) {
        if (!library.entries().containsKey(operation)
                && !library.rewrites().containsKey(operation)) {
            throw new IllegalArgumentException(
                    "`" + operation.qualified() + "` is no operation of the library read");
        }
        if (reading == null) {
            BoundOperationFacts proved = facts.get();
            reading = new Reading(library, proved.proofs(), proved);
        }
        return reading.of(operation);
    }

    /**
     * What {@code operation} ends a run for, with what it is handed run as well: what it ends one
     * for apart from that where it is handed no function, and not known where it is.
     *
     * @throws IllegalArgumentException where the library has no such operation — never answered as
     *     not known, which says the operation was read and its body did not say
     */
    Endings of(ValueName.Stdlib.Operation operation) {
        Read found = readOf(operation);
        return handedAFunction(operation) ? NOT_KNOWN : found.own();
    }

    /**
     * What a call of {@code operation} answering a value of {@code answer} ends a run for, with
     * what it is handed run as well: {@link #of}, but of a kernel at the number it answers
     * ({@link KernelContracts#abortsAnswering}), which is narrower where the kernel is one
     * operation over several numbers.
     *
     * @throws IllegalArgumentException where the library has no such operation
     */
    Endings ofACallAnswering(ValueName.Stdlib.Operation operation, Type answer) {
        Stdlib.Intrinsic intrinsic = library.intrinsicOf(operation);
        return intrinsic == null || handedAFunction(operation) ? of(operation)
                : new Endings.Known(KernelContracts.abortsAnswering(intrinsic.kernel(), answer));
    }

    /**
     * What {@code operation} ends a run for apart from what the functions it is handed do, for a
     * caller that asks the body of each of those itself: the kernel's own contract, or what its
     * body does where none of them is applied. A closure its body builds is read as run, wherever
     * the body hands it.
     *
     * @throws IllegalArgumentException where the library has no such operation
     */
    Endings apartFromWhatItIsHanded(ValueName.Stdlib.Operation operation) {
        return readOf(operation).own();
    }

    /**
     * Where a call of {@code operation} answers apart from the functions it is handed, for a
     * caller that asks the body of each of those itself.
     *
     * <p>Where it ends nothing, always. A kernel answers where its contract says. One the library
     * writes answers where what the sites of its body that may hold too much are shown to hold
     * fits, where that is all that ends a run in it; and one assembling its answer of a piece for
     * each element of a list, which holds as many as the pieces do, where those fit
     * ({@link BoundOperationFacts#assembles}). Nothing else is said here.
     *
     * @throws IllegalArgumentException where the library has no such operation
     */
    GetsPast completionApartFromWhatItIsHanded(ValueName.Stdlib.Operation operation) {
        return readOf(operation).completion();
    }

    /**
     * Which operand of a call of {@code operation}, counted from nought, is the one it ends a run
     * on alone, or -1 where there is none: the operation's kernel says
     * ({@link KernelContracts#theOperandItAloneStopsOn}).
     */
    int theOperandItAloneStopsOn(ValueName.Stdlib.Operation operation) {
        Stdlib.Intrinsic intrinsic = library.intrinsicOf(operation);
        return intrinsic == null ? -1 : KernelContracts.theOperandItAloneStopsOn(intrinsic.kernel());
    }

    /** Whether {@code operation} takes a function, which it may apply. */
    private boolean handedAFunction(ValueName.Stdlib.Operation operation) {
        Stdlib.Entry entry = library.entry(operation);
        if (entry != null) {
            return entry.signature().params().stream().anyMatch(Type.FnOf.class::isInstance);
        }
        Stdlib.Rewrite rewrite = library.rewriteOf(operation);
        return rewrite != null && handedAFunction(rewrite.target());
    }

    /** The shipped library's, which is the same for every compilation. */
    static LibraryEndings shipped() {
        return Shipped.ENDINGS;
    }

    private static final class Shipped {
        private static final LibraryEndings ENDINGS =
                of(DefaultStdlib.get(), DefaultBoundOperationFacts::get);
    }

    /** One reading of a library, each operation settled once. */
    private static final class Reading {
        private final Stdlib library;
        private final LibraryProofs prover;
        private final BoundOperationFacts facts;
        private final Map<ValueName.Stdlib.Operation, Read> settled = new HashMap<>();
        private final Set<ValueName.Stdlib.Operation> reading = new HashSet<>();

        private Reading(Stdlib library, LibraryProofs prover, BoundOperationFacts facts) {
            this.library = library;
            this.prover = prover;
            this.facts = facts;
        }

        /**
         * What {@code operation} ends a run for and where it answers. One met again while its own
         * body is being read is on a cycle, and so is everything read between the two meetings,
         * which comes back to it.
         */
        Read of(ValueName.Stdlib.Operation operation) {
            Read done = settled.get(operation);
            if (done != null) {
                return done;
            }
            if (!reading.add(operation)) {
                return new Read(NOT_KNOWN, new GetsPast.NotKnown());
            }
            Read out;
            try {
                out = worked(operation);
            } finally {
                reading.remove(operation);
            }
            settled.put(operation, out);
            return out;
        }

        /**
         * The walk ends nothing of its own: it reads the element at its index and goes on from the
         * next only where there is one, and there the index is below the list's length, which an
         * {@code Int} holds, so the next index has a place; and it ends ({@code TheWalkEnds}).
         * What is left is the step, which it is handed.
         */
        private Read worked(ValueName.Stdlib.Operation operation) {
            if (operation.equals(library.walk().operation())) {
                return new Read(NONE, new GetsPast.Always());
            }
            Stdlib.Intrinsic intrinsic = library.intrinsicOf(operation);
            if (intrinsic != null) {
                return new Read(new Endings.Known(KernelContracts.abortsOf(intrinsic.kernel())),
                        KernelContracts.completionOf(intrinsic.kernel()));
            }
            if (library.helpers().get(operation) != null) {
                return ofTheBody(operation);
            }
            Stdlib.Rewrite rewrite = library.rewriteOf(operation);
            if (rewrite != null) {
                return of(rewrite.target());
            }
            throw new IllegalArgumentException(
                    "`" + operation.qualified() + "` is no operation of this library");
        }

        /** What {@code operation}, which the library writes, ends a run for, read off its body. */
        private Read ofTheBody(ValueName.Stdlib.Operation operation) {
            LibraryTerm body = LibraryTerms.of(library, library.helpers().get(operation));
            OfTheBody read = new OfTheBody(prover.typesOf(operation, body));
            read.visit(body);
            if (read.ending.isEmpty()) {
                return new Read(NONE, new GetsPast.Always());
            }
            if (!(WhereAnOperatorAnswers.ofAnOperator(BinOp.ADD, Type.INT)
                    instanceof WhereAnOperatorAnswers.WhereItsExactValueIsHeld(
                            BigInteger least, BigInteger greatest))) {
                throw new IllegalStateException("a sum of two whole numbers is read where its"
                        + " exact value is held, between the least and the greatest an Int holds");
            }
            OnTheWay proved = prover.onTheWay(new AskedOnTheWay(operation, body,
                    read.ending.keySet(), read.divisions, read.collections, read.numbers,
                    read.bounds, least, greatest, GetsPast.MOST_ELEMENTS));
            read.reached(proved.reached());
            if (read.all.endsNone()) {
                return new Read(NONE, new GetsPast.Always());
            }
            if (read.collections.isEmpty() && read.numbers.isEmpty()) {
                return new Read(read.all, otherwise(operation, read.apart));
            }
            return switch (proved.held()) {
                case HeldOnTheWay.WithinWhatItIsHanded _ -> new Read(read.apart,
                        read.apart.endsNone() ? new GetsPast.Always()
                                : otherwise(operation, read.apart));
                case HeldOnTheWay.NoMoreThan(LinearForm<LawNumber<Integer>> most) ->
                        new Read(read.all, read.apart.endsNone()
                                ? new GetsPast.WhereTheAnswerFits(most)
                                : otherwise(operation, read.apart));
                case HeldOnTheWay.NotShown _ -> new Read(read.all, otherwise(operation, read.apart));
            };
        }

        /** {@code ends} but for {@code kind}, where what they are is known. */
        private static Endings without(Endings ends, AbortKind kind) {
            if (!(ends instanceof Endings.Known(AbortSet kinds))) {
                return ends;
            }
            Set<AbortKind> rest = EnumSet.noneOf(AbortKind.class);
            rest.addAll(kinds.kinds());
            rest.remove(kind);
            return new Endings.Known(AbortSet.copyOf(rest));
        }

        /**
         * Where {@code operation} answers where what its sites hold is not shown to be all that
         * ends a run in it, which ends nothing but {@code apart} beside those: an answer
         * assembled of a piece for each element of a list, each what the closure answers on one,
         * holds what the pieces together hold and no more on the way; nothing else is said.
         */
        private GetsPast otherwise(ValueName.Stdlib.Operation operation, Endings apart) {
            BoundOperationFacts.Assembled assembled = facts.assembles(operation);
            if (apart.endsNone() && assembled != null
                    && assembled.piece() == PieceOfAnElement.WHAT_THE_CLOSURE_ANSWERS) {
                int source = assembled.source().position();
                return new GetsPast.WhereTheAnswerFits(LinearForm.atom(new LawNumber.SumOver<>(
                        source, new LawNumber.SizeOf<>(new LawSubject.WhatTheClosureAnswers<>(
                                assembled.closure().position())))));
            }
            return new GetsPast.NotKnown();
        }

        /**
         * One reading of a body: what its sites end a run for, all of them and apart from what
         * those that may hold too much end one for by holding too much, and which those are.
         *
         * <p>Apart from that kind alone, and not from the whole of what such a site ends a run
         * for: a site is one of them by what it builds or works out, and a call among them ends a
         * run for whatever its operation does.
         */
        private final class OfTheBody {
            private final Map<LibraryTerm, Type> typed;
            private final Set<LibraryTerm> collections = LibraryTerm.places();
            private final Set<LibraryTerm> numbers = LibraryTerm.places();
            /** What a site holds at most by its own owner's word, over the operation's
             *  parameters, where that is a number of them. */
            private final List<LinearForm<LawNumber<Integer>>> bounds = new ArrayList<>();
            /** Every site that may end a run, with what it ends one for of itself. */
            private final Map<LibraryTerm, Endings> ending = new IdentityHashMap<>();
            /** The sites that divide, which end a run for a divisor of nought. */
            private final Set<LibraryTerm> divisions = LibraryTerm.places();
            private Endings all = NONE;
            private Endings apart = NONE;

            OfTheBody(Map<LibraryTerm, Type> typed) {
                this.typed = typed;
            }

            void visit(LibraryTerm term) {
                Endings itself = itself(term);
                if (!itself.endsNone()) {
                    ending.put(term, itself);
                }
                LibraryTerm.forEachPart(term, this::visit);
            }

            /**
             * What the sites end a run for where the body reaches them
             * ({@link LibraryProver#onTheWay}): one it reaches on no way ends none, and a division
             * whose divisor is never nought where it is reached ends none for that.
             */
            void reached(WhereReached reached) {
                collections.removeAll(reached.onNoWay());
                numbers.removeAll(reached.onNoWay());
                ending.forEach((site, ends) -> {
                    if (reached.onNoWay().contains(site)) {
                        return;
                    }
                    Endings left = reached.neverByNought().contains(site)
                            ? without(ends, AbortKind.DIVISION_BY_ZERO) : ends;
                    all = all.and(left);
                    apart = apart.and(collections.contains(site) || numbers.contains(site)
                            ? without(left, AbortKind.REQUIRED_FORM_HAS_NO_PLACE) : left);
                });
            }

            /**
             * What {@code term} itself, and none of what it is made of, ends a run for — telling
             * the sites that end one only where they hold too much on the way.
             */
            private Endings itself(LibraryTerm term) {
                return switch (term) {
                    case LibraryTerm.Operator(BinOp op, var _, var _, var _) -> operator(term, op);
                    case LibraryTerm.Negated _ -> {
                        Type answer = typed.get(term);
                        if (Type.INT.equals(answer)) {
                            numbers.add(term);
                        }
                        yield new Endings.Known(answer == null ? AbortSites.ofANegationOfAnyType()
                                : AbortSites.ofANegationAnswering(answer));
                    }
                    case LibraryTerm.Call(ValueName.Stdlib.Operation called,
                                          List<LibraryTerm> args) -> {
                        Read callee = Reading.this.of(called);
                        if (callee.completion() instanceof GetsPast.WhereTheAnswerFits(
                                LinearForm<LawNumber<Integer>> answer)) {
                            collections.add(term);
                            overTheParameters(answer, args);
                        }
                        Stdlib.Intrinsic intrinsic = library.intrinsicOf(called);
                        Type answering = typed.get(term);
                        yield intrinsic == null || answering == null ? callee.own()
                                : new Endings.Known(KernelContracts.abortsAnswering(
                                        intrinsic.kernel(), answering));
                    }
                    case LibraryTerm.Unread(LibraryTerm.Unwritten what) -> switch (what) {
                        case A_STRING -> NONE;
                        case AN_UNREACHABLE_PLACE ->
                                new Endings.Known(AbortSites.ofAnUnreachableWherever());
                        case A_DECLARED_VALUE, A_MATCH_ON_DECLARED_CASES, AN_EXPANSION,
                             A_COMPREHENSION, A_NAME_OF_NOTHING_HERE, AN_OPERATION_AS_A_VALUE ->
                                NOT_KNOWN;
                    };
                    case LibraryTerm.Parameter _, LibraryTerm.Bound _, LibraryTerm.WholeNumber _,
                         LibraryTerm.DecimalNumber _, LibraryTerm.Truth _, LibraryTerm.UnitValue _,
                         LibraryTerm.ListOf _,
                         LibraryTerm.TupleOf _, LibraryTerm.Component _, LibraryTerm.Applied _,
                         LibraryTerm.Closure _, LibraryTerm.Let _, LibraryTerm.Fork _,
                         LibraryTerm.OnAnOption _ -> NONE;
                };
            }

            /**
             * What the operator {@code term} ends a run for: at the type it is read to answer, and
             * over every typing where it is read to answer none. One answering where what it
             * builds fits, and {@code + - *} over whole numbers, are sites.
             */
            private Endings operator(LibraryTerm term, BinOp op) {
                Type answer = typed.get(term);
                if (answer == null) {
                    AbortSet sites = AbortSites.ofAnOperatorOfAnyType(op);
                    return sites.contains(AbortKind.INVARIANT_NOT_HELD)
                            ? NOT_KNOWN : new Endings.Known(sites);
                }
                if (AbortSites.completionOfAnOperator(op, answer)
                        instanceof GetsPast.WhereTheAnswerFits(LinearForm<LawNumber<Integer>> fits)
                        && term instanceof LibraryTerm.Operator(var _, LibraryTerm left,
                                LibraryTerm right, var _)) {
                    collections.add(term);
                    overTheParameters(fits, List.of(left, right));
                }
                if (Type.INT.equals(answer)
                        && (op == BinOp.ADD || op == BinOp.SUB || op == BinOp.MUL)) {
                    numbers.add(term);
                }
                AbortSet sites = AbortSites.ofAnOperatorAnswering(op, answer);
                if (sites.contains(AbortKind.DIVISION_BY_ZERO)) {
                    divisions.add(term);
                }
                return sites.contains(AbortKind.INVARIANT_NOT_HELD)
                        ? NOT_KNOWN : new Endings.Known(sites);
            }

            /**
             * Tells {@link #bounds} what a site answering where {@code fits} says, a number of what
             * it is handed at {@code operands}, holds at most as a number of the operation's own
             * parameters, where each operand it counts is one of them as it stands.
             */
            private void overTheParameters(LinearForm<LawNumber<Integer>> fits,
                                           List<LibraryTerm> operands) {
                boolean[] apart = {false};
                Function<Integer, Integer> parameter = at -> {
                    if (at < operands.size()
                            && operands.get(at) instanceof LibraryTerm.Parameter(int position)) {
                        return position;
                    }
                    apart[0] = true;
                    return at;
                };
                // Number by number, since two operands may be one parameter, counted twice.
                Map<LawNumber<Integer>, ExactRatio> over = new LinkedHashMap<>();
                for (Map.Entry<LawNumber<Integer>, ExactRatio> each : fits.coefs().entrySet()) {
                    LawNumber<Integer> number = ByPlace.form(LinearForm.atom(each.getKey()),
                            parameter).coefs().keySet().iterator().next();
                    ExactRatio before = over.get(number);
                    if (before == null) {
                        over.put(number, each.getValue());
                    } else if (before.plus(each.getValue())
                            instanceof ExactAnswer.Held<ExactRatio>(ExactRatio both)) {
                        over.put(number, both);
                    } else {
                        return;
                    }
                }
                LinearForm<LawNumber<Integer>> most = new LinearForm<>(fits.constant(), over);
                if (!apart[0] && !bounds.contains(most)) {
                    bounds.add(most);
                }
            }
        }
    }
}
