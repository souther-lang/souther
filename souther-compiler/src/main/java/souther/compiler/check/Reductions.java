package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.core.Core;
import souther.compiler.proof.TheWalkEnds;
import souther.compiler.proof.WalksFromASeed;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.types.ValueName;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

/**
 * Which library operations walk a container from a seed and answer the accumulator they end with,
 * and where the seed and the accumulator are.
 *
 * <p>Read off the operations' bodies ({@link WalksFromASeed}), since that an operation is a walk
 * from a seed is not something a type says: {@code ((A, B) -> A, A, List<B>) -> A} is equally the
 * declaration of an operation that applies its closure once, or that ignores the seed and answers
 * something it built itself. The walk the library publishes is one by its own body, and an
 * operation answering a call of it from its own seed with its own closure as the step is another.
 *
 * <p>Which argument is the closure, which the container, and which parameter the element arrives on
 * are not here at all. {@link Combinators} reads those, and an operation this has an answer for is
 * one that answered there.
 *
 * <p>What the rule licenses is stated once, here, and is the whole of what anything downstream may
 * assume: the answer is the seed, or is {@code step} applied to an earlier accumulator and something
 * the container holds. Nothing about how many elements there are, nothing about the order they
 * arrive in, and nothing about the walk terminating. {@link InductiveBounds} is written against
 * exactly that and knows no operation's name.
 */
final class Reductions {

    /** A reduction's seed and the closure parameter it arrives on, as positions of the call —
     * meaningful only beside the call they are positions in, which is why they are read through
     * {@link #reducing} rather than handed about on their own. */
    record Reduction(int seedArg, int accumulatorParam) {}

    /**
     * What a call reduces: the value it starts from, the step it repeats, and the parameters the step
     * is handed.
     *
     * <p>The element and the container come from {@link Combinators}, so a caller reading this reads
     * one answer about the call rather than two it has to line up itself.
     */
    record Reducing(Core seed, Core.Block step, Core.Binder accumulator, Core.Binder element,
                    Core container) {}

    /** The reduction {@code operation} is, or null where it reduces nothing — including where it
     * applies no closure at all, and where the name applied is not a library operation. */
    static Reduction of(ValueName operation) {
        // A name that is no library operation reduces nothing, and is answered by the type rather
        // than by a lookup that finds nothing.
        return operation instanceof ValueName.Stdlib.Operation library
                ? Derived.RULES.get(library) : null;
    }

    /**
     * What {@code call} reduces, or null where it is not a reduction, or where what stands in its
     * closure argument is not a block this can read.
     *
     * <p>{@code at} is what the names around the call denote, for the reason {@link
     * Combinators#handedTo} takes one: a closure may be written as a name bound to a block.
     */
    static Reducing reducing(Core.PreservedCall call, Denotations at) {
        return reducing(call, closure -> Terms.blockOf(closure, at));
    }

    /**
     * The same, told how to reach the block a closure is, for a reader whose names are denoted by
     * something other than the denotations a check builds.
     */
    static Reducing reducing(Core.PreservedCall call, Function<Core, Core.Block> blockOf) {
        Reduction rule = of(call.operation());
        Combinators.Handed handed = Combinators.handedTo(call, blockOf);
        if (rule == null || handed == null
                || rule.accumulatorParam() >= handed.step().params().size()) {
            return null;
        }
        return new Reducing(call.args().get(rule.seedArg()), handed.step(),
                handed.step().params().get(rule.accumulatorParam()), handed.element(),
                handed.container());
    }

    /** The operations there is a rule about. */
    static Set<ValueName.Stdlib.Operation> answered() {
        return Derived.RULES.keySet();
    }

    /**
     * Whether {@code operation} is a recursion of the library's own proved to end, from any index it
     * starts at ({@link TheWalkEnds}) — which the library's walk is and nothing else the library
     * writes is.
     */
    static boolean endsWhereverItStarts(ValueName.Stdlib.Operation operation) {
        return Derived.WALK_ENDS && DefaultStdlib.get().walk().operation().equals(operation);
    }

    /** Read once. The library is the same library for every module compiled. */
    private static final class Derived {
        private static final Map<ValueName.Stdlib.Operation, Reduction> RULES = read();
        private static final boolean WALK_ENDS = walkEnds();
    }

    /** Whether the walk ends, read off the law of what it reads an element at its index with,
     *  which it hands its index first and its list second. */
    private static boolean walkEnds() {
        return DefaultBoundOperationFacts.get().settled(DefaultStdlib.get().walk().reads(),
                        OperationLaw.Observed.PRESENCE)
                instanceof BoundOperationFacts.Settled.ByALaw(var law, var _)
                && TheWalkEnds.proved(law, 0, 1, DeclaredArgument::position);
    }

    /** Each walk the bodies are, in the positions this hands about. The holder above is the only
     *  thing here that reaches for the process's own library — {@link DefaultStdlib} says who may
     *  and why the loader may not. */
    private static Map<ValueName.Stdlib.Operation, Reduction> read() {
        Map<ValueName.Stdlib.Operation, Reduction> rules = new LinkedHashMap<>();
        WalksFromASeed.of(DefaultStdlib.get(), Combinators.all()).forEach((operation, walk) ->
                rules.put(operation, new Reduction(walk.seedArg(), walk.accumulatorParam())));
        return Map.copyOf(rules);
    }

    private Reductions() {}
}
