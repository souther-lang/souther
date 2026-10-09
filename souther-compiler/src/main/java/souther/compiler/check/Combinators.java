package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.proof.AppliedClosures;
import souther.compiler.semantics.BuiltFrom;
import souther.compiler.semantics.ClosurePositions;
import souther.compiler.semantics.Combinator;
import souther.compiler.semantics.ElementLineage;
import souther.compiler.semantics.HowAClosureIsApplied;
import souther.compiler.semantics.SizeAgainstItsSource;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

/**
 * Which library operations hand a closure the contents of a container, and where: the closure is
 * argument {@code closureArg}, the value it receives is closure parameter {@code elementParam}, the
 * container it comes from is argument {@code containerArg}, and where the container is a map, the
 * key the value is filed under arrives on closure parameter {@code keyParam}.
 *
 * <p>Two checks read this and neither states it. The totality check credits a value a closure is
 * handed as a sub-term of the container, so recursing on it is structural; the invariant-discharge
 * check binds that value to the container's element type, so a construction inside the closure is
 * analyzed rather than left opaque. What each does with the answer is its own; what it asks is one
 * question about the operation.
 *
 * <p>Two halves, from two places. Where the closure and the container are is read off the library's
 * signature ({@link #positionsOf}): the argument that takes a function, and the parameter of it
 * whose type is the type of what a container holds. That the operation hands the closure anything
 * at all, which container, and how far it goes, a signature does not say — an operation of that type
 * could apply its closure once, or never. So that half is read off the operation's body where it
 * has one ({@link AppliedClosures}), and declared of a kernel where it has none ({@link #KERNELS}),
 * held there to what the kernel computes by a test that runs it. An operation answered by neither
 * hands its closure nothing this says, whatever its signature.
 *
 * <p>Each reader asks under the name it holds. The totality check reads the tree an author wrote,
 * where {@code List.fold} still spells itself; the discharge check reads one where the rewrite to
 * {@code List.foldFrom} has happened. So a {@linkplain Stdlib#rewrites() sugared} name is answered
 * with what it rewrites to, over the arguments the rewrite keeps in place.
 */
final class Combinators {

    /** What {@code operation} hands its closure, or null where it hands one nothing a container
     * holds — including where it applies no closure at all, where nothing establishes that it
     * applies the one it takes, and where the name applied is not a library operation. */
    static Combinator of(ValueName operation) {
        return operation instanceof ValueName.Stdlib.Operation library
                ? Derived.RULES.get(library) : null;
    }

    /**
     * Where {@code operation}'s signature puts a closure and a container whose contents it could be
     * handed, or null where the signature puts none.
     *
     * <p>Places and nothing else, for a reader that has a fact to hold to the arguments it names:
     * which argument "the container" of a fact is depends on the signature and not on what the
     * operation does with it.
     */
    static ClosurePositions positionsOf(ValueName operation) {
        return operation instanceof ValueName.Stdlib.Operation library
                ? Positions.RULES.get(library) : null;
    }

    /** What a call hands its closure: the argument that takes the function, the block that argument
     * is, the parameter the element arrives on, the container it comes from, and the parameter the
     * key it is filed under arrives on — null where the closure is handed no key — and how far the
     * operation goes applying it. */
    record Handed(Core closure, Core.Block step, Core.Binder element, Core container,
                  Core.Binder key, HowAClosureIsApplied applied) {}

    /** The same, off the tree an author wrote, where a closure is the block as written. */
    record Written(Hir.Block step, Hir.Binder element, Hir.Expr container) {}

    /**
     * What {@code call} hands its closure, or null where it hands one nothing a container holds — or
     * where what stands in the closure argument is not a block this can read.
     *
     * <p>{@code at} is what the names around the call denote, since a closure may be written as a
     * name bound to a block. It is the denotations where the call stands: what a name means depends
     * on which bindings it is under, so it is asked per call and not once per body.
     */
    static Handed handedTo(Core.PreservedCall call, Denotations at) {
        return handedTo(call, closure -> Terms.blockOf(closure, at));
    }

    /**
     * The same, told how to reach the block a closure is.
     *
     * <p>What a closure is written as is the one thing a reader of this needs that differs between
     * readers: a walk inside a check has the denotations it built, and a reading of the input has
     * its own answer about what a name stands for. What the operation hands over does not differ, so
     * it is read once here and the difference is a parameter.
     */
    static Handed handedTo(Core.PreservedCall call, Function<Core, Core.Block> blockOf) {
        return handedTo(call.operation(), call.args(), blockOf);
    }

    /**
     * The same, of an application named by the operation it applies and the arguments it passes.
     *
     * <p>Which of the two shapes a representation gives an application is not a difference this
     * table has anything to say about: the rule is about the operation, and the arguments are the
     * arguments. So the question is asked once, of the two things it is about, and a reader holding
     * either shape hands over the operation it resolved to and the arguments it carries.
     *
     * <p>An operation that hands its closure the elements from an index it is handed hands them all
     * only where that index is nought, and is answered for nowhere else.
     */
    static Handed handedTo(ValueName operation, List<Core> args, Function<Core, Core.Block> blockOf) {
        Combinator rule = of(operation);
        if (rule == null || rule.closureArg() >= args.size()
                || rule.containerArg() >= args.size() || !fromTheFirst(rule, args)) {
            return null;
        }
        Core closure = args.get(rule.closureArg());
        Core.Block step = blockOf.apply(closure);
        if (step == null || rule.elementParam() >= step.params().size()
                || rule.keyParam() >= step.params().size()) {
            return null;
        }
        return new Handed(closure, step, step.params().get(rule.elementParam()),
                args.get(rule.containerArg()),
                rule.handsAKey() ? step.params().get(rule.keyParam()) : null, rule.applied());
    }

    /** Whether a call hands its closure the container's elements from the first. */
    private static boolean fromTheFirst(Combinator rule, List<Core> args) {
        return rule.startsFrom() == Combinator.FROM_THE_FIRST
                || (rule.startsFrom() < args.size()
                && Core.withoutStanding(args.get(rule.startsFrom())) instanceof Core.Int from
                && from.value() == 0);
    }

    /**
     * The same, off the tree an author wrote — where a closure written as anything but a block is one
     * this says nothing about, the tree not yet having been read for what names denote.
     *
     * <p>Nor is a call the operation would not have accepted — written with fewer arguments than it
     * takes, or handed a block with fewer parameters than it applies one to. That is not this table
     * disagreeing with a signature: it is what the surface tree still holds, the walk that reads it
     * running beside the checks that report an arity rather than after them, so a call already known
     * to be wrong reaches here. A sugar is how both arrive — it has no declaration of its own, so
     * what is said about the arity of {@code List.fold} is said against the call it becomes, and by
     * then this has already read it. Nothing about arguments or parameters a call does not have is
     * true, so nothing is said, and the arity is reported by the check whose question it is.
     */
    static Written handedTo(Hir.Apply call) {
        // A call applying a name nothing declares hands its closure to no operation this table
        // has: there is no declaration to find a rule under, and what is wrong with it is reported
        // where the name is written.
        Combinator rule = call.answered() == null ? null : of(call.answered().denotes());
        if (rule == null || rule.closureArg() >= call.args().size()
                || rule.containerArg() >= call.args().size()
                || !(call.args().get(rule.closureArg()) instanceof Hir.Block step)) {
            return null;
        }
        if (rule.startsFrom() != Combinator.FROM_THE_FIRST
                && (rule.startsFrom() >= call.args().size()
                || !(call.args().get(rule.startsFrom()) instanceof Hir.IntLit(long from, var _, var _))
                || from != 0)) {
            return null;
        }
        if (rule.elementParam() >= step.params().size()) {
            return null;
        }
        return new Written(step, step.params().get(rule.elementParam()),
                call.args().get(rule.containerArg()));
    }

    /** What every operation it is established hands its closure what a container holds hands it. */
    static Map<ValueName.Stdlib.Operation, Combinator> all() {
        return Derived.RULES;
    }

    /** The operations it is established hand their closure what a container holds. */
    static Set<ValueName> answered() {
        return Collections.unmodifiableSet(Derived.RULES.keySet());
    }

    /** The operations there is a rule for, for the tests that hold them to firing. Handed over as
     *  the operations, so a reader holding one asks the library with it rather than with a spelling
     *  this rendered on the way out. */
    static Set<ValueName.Stdlib.Operation> named() {
        return Collections.unmodifiableSet(new LinkedHashSet<>(Derived.RULES.keySet()));
    }

    /**
     * How far each kernel that takes a closure goes applying it.
     *
     * <p>An axiom about each, since a kernel has no body to read it off. Where the closure and the
     * container are is still its signature's to say; this says only that it is applied, and how
     * far. Every entry is held to what the kernel computes by a test that runs it.
     */
    private static final Map<ValueName.Stdlib.Operation, HowAClosureIsApplied> KERNELS = Map.of(
            ValueName.Stdlib.operation("List", "find"), HowAClosureIsApplied.UNTIL_ONE_HOLDS,
            ValueName.Stdlib.operation("List", "sortBy"), HowAClosureIsApplied.TO_EVERY_ELEMENT,
            ValueName.Stdlib.operation("Option", "map"), HowAClosureIsApplied.TO_EVERY_ELEMENT);

    /**
     * What kernels answer of their arguments that no fact about what they build says: a list of
     * every element of a set, each once; an option holding, where it holds anything, one value of a
     * map.
     *
     * <p>An axiom about each, as {@link #KERNELS} is, and held to what the kernel computes the same
     * way. Read where a body hands its closure what such an answer holds.
     */
    private static final Map<ValueName.Stdlib.Operation, AppliedClosures.Listing> LISTED = Map.of(
            ValueName.Stdlib.operation("Set", "toList"),
            new AppliedClosures.Listing.EveryElementOf(0),
            ValueName.Stdlib.operation("Map", "get"),
            new AppliedClosures.Listing.AtMostOneElementOf(1));

    /** The places, read off the library's signatures on the first ask. */
    private static final class Positions {
        private static final Map<ValueName.Stdlib.Operation, ClosurePositions> RULES =
                positions(DefaultStdlib.get());
    }

    /** What each operation does with them, read off the library on the first ask. The library is
     *  the same library for every module compiled, and reading it is answering the question for all
     *  of them at once. */
    private static final class Derived {
        private static final Map<ValueName.Stdlib.Operation, Combinator> RULES =
                read(DefaultStdlib.get(), DefaultBoundOperationFacts.get());
    }

    /** A pure function of the library and what its kernels are declared to answer, so the holders
     *  above are the only things here that reach for the process's own. */
    private static Map<ValueName.Stdlib.Operation, Combinator> read(Stdlib stdlib,
                                                                    BoundOperationFacts facts) {
        Map<ValueName.Stdlib.Operation, Combinator> kernels = new LinkedHashMap<>();
        KERNELS.forEach((operation, how) -> {
            if (stdlib.intrinsicOf(operation) == null) {
                throw new IllegalStateException(operation + " is declared to apply its closure as"
                        + " a kernel, and the library writes it in the language — what it does is"
                        + " its body's to say");
            }
            ClosurePositions at = positionsOf(operation);
            if (at == null) {
                throw new IllegalStateException(operation + " is declared to apply its closure, and"
                        + " its signature puts no closure beside a container");
            }
            kernels.put(operation, new Combinator(at.closureArg(), at.elementParam(),
                    at.containerArg(), at.keyParam(), how, Combinator.FROM_THE_FIRST));
        });
        return AppliedClosures.of(stdlib, kernels, operation -> listing(stdlib, facts, operation),
                Combinators::positionsOf);
    }

    /**
     * What a kernel's answer lists of its arguments, as it is declared: every element of one, where
     * it holds each of them once and nothing else; every entry or every value of a map it lists;
     * at most one element of one, where it holds an element of it in an option.
     */
    private static AppliedClosures.Listing listing(Stdlib stdlib, BoundOperationFacts facts,
                                                   ValueName.Stdlib.Operation operation) {
        AppliedClosures.Listing declared = LISTED.get(operation);
        if (declared != null) {
            if (stdlib.intrinsicOf(operation) == null) {
                throw new IllegalStateException(operation + " is declared to list what it answers"
                        + " as a kernel, and the library writes it in the language");
            }
            return declared;
        }
        BoundOperationFacts.Listed listed = facts.listsAPartOf(operation);
        if (listed != null) {
            return switch (listed.part()) {
                case ENTRIES -> new AppliedClosures.Listing.EveryEntryOf(listed.map().position());
                case VALUES -> new AppliedClosures.Listing.EveryElementOf(listed.map().position());
                case KEYS -> null;
            };
        }
        BuiltFrom<DeclaredArgument> built = facts.buildsItsResultFrom(operation);
        if (built == null || built.outputs().size() != 1
                || !(built.lineage() instanceof ElementLineage.SameAs<DeclaredArgument> same)
                || same.source().elements() != 1) {
            return null;
        }
        return built.outputs().get(0).at().equals(ElementLineage.ResultPath.elements())
                && built.size() == SizeAgainstItsSource.SAME
                ? new AppliedClosures.Listing.EveryElementOf(same.source().argument().position())
                : null;
    }

    /** A pure function of the library. */
    private static Map<ValueName.Stdlib.Operation, ClosurePositions> positions(Stdlib stdlib) {
        Map<ValueName.Stdlib.Operation, ClosurePositions> rules = new LinkedHashMap<>();
        stdlib.entries().forEach((operation, entry) -> {
            ClosurePositions rule = positionsIn(operation, entry.signature().params());
            if (rule != null) {
                rules.put(operation, rule);
            }
        });
        stdlib.rewrites().forEach((sugar, rewrite) -> {
            ClosurePositions target = rules.get(rewrite.target());
            if (target == null) {
                return;   // what it becomes hands its closure nothing, so neither does it
            }
            if (target.closureArg() >= rewrite.keptArgs()
                    || target.containerArg() >= rewrite.keptArgs()) {
                throw new IllegalStateException(sugar + " is sugar for " + rewrite.target()
                        + ", whose closure or container is not among the arguments the rewrite keeps"
                        + " in place — what it hands its closure cannot be said of the sugar");
            }
            rules.put(sugar, target);
        });
        return Collections.unmodifiableMap(rules);
    }

    /**
     * Where the signature of {@code qualified} puts a closure and a container, or null where it
     * puts none.
     *
     * <p>The closure is the argument that takes a function. The container is an argument holding
     * something whose element type is the type of one of that closure's parameters. An operation
     * whose signature admits more than one reading of either is one this cannot answer for.
     */
    private static ClosurePositions positionsIn(ValueName.Stdlib.Operation qualified,
                                                List<Type> params) {
        int closureArg = -1;
        for (int i = 0; i < params.size(); i++) {
            if (params.get(i) instanceof Type.FnOf) {
                if (closureArg >= 0) {
                    throw new IllegalStateException(qualified + " takes two functions, so which one is"
                            + " handed the container's elements is not read off its signature");
                }
                closureArg = i;
            }
        }
        if (closureArg < 0) {
            return null;
        }
        List<Type> closureParams = ((Type.FnOf) params.get(closureArg)).params();
        ClosurePositions found = null;
        for (int c = 0; c < params.size(); c++) {
            if (c == closureArg) {
                continue;   // the closure is what receives; it is not what is received from
            }
            Type element = Terms.elementType(params.get(c));
            if (element == null) {
                continue;
            }
            for (int p = 0; p < closureParams.size(); p++) {
                if (!element.equals(closureParams.get(p))) {
                    continue;
                }
                if (found != null) {
                    throw new IllegalStateException(qualified + " could be handing its closure the"
                            + " contents of more than one of its arguments, or on more than one"
                            + " parameter, so which is not read off its signature");
                }
                found = new ClosurePositions(closureArg, p, c,
                        keyParam(qualified, Type.keyOf(params.get(c)), closureParams, p));
            }
        }
        return found;
    }

    /**
     * The parameter of the closure the container's key arrives on, or {@link Combinator#NO_KEY}
     * where the container files what it holds under none or the closure takes no parameter of that
     * type.
     *
     * <p>Read the way the element is: the parameter whose type is the type of the key. One that
     * could be either the key or the value — a map whose two types are one type variable — is not
     * read off the signature, and is refused rather than answered with whichever came first.
     */
    private static int keyParam(ValueName.Stdlib.Operation qualified, Type key,
                                List<Type> closureParams, int elementParam) {
        if (key == null) {
            return Combinator.NO_KEY;
        }
        int found = Combinator.NO_KEY;
        for (int q = 0; q < closureParams.size(); q++) {
            if (!key.equals(closureParams.get(q))) {
                continue;
            }
            if (q == elementParam || found != Combinator.NO_KEY) {
                throw new IllegalStateException(qualified + " hands its closure a key on a"
                        + " parameter that could as well be another, so which is not read off its"
                        + " signature");
            }
            found = q;
        }
        return found;
    }

    private Combinators() {}
}
