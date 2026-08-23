package souther.compiler.check;

import souther.compiler.semantics.Combinator;

import souther.compiler.core.Core;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Which library operations walk a container from a seed and answer the accumulator they end with,
 * and where the seed and the accumulator are.
 *
 * <p>Two halves, in the order ADR-0097 puts them. That an operation is a walk from a seed is not
 * something a type says: {@code ((A, B) -> A, A, List<B>) -> A} is equally the declaration of an
 * operation that applies its closure once, or that ignores the seed and answers something it built
 * itself. So {@link Question#REDUCTION} states the range and {@link #REDUCES} answers it. Where the
 * seed and the accumulator are, once an operation is known to be one, the declaration does say — the
 * seed is the argument of the type the operation answers, and the accumulator is the closure
 * parameter of that type — so those are read off the signature and are not written down.
 *
 * <p>Which argument is the closure, which the container, and which parameter the element arrives on
 * are not here at all. {@link Combinators} reads those off the same signature, and an operation this
 * has an answer for is one that answered there.
 *
 * <p>What the rule licenses is stated once, here, and is the whole of what anything downstream may
 * assume: the answer is the seed, or is {@code step} applied to an earlier accumulator and something
 * the container holds. Nothing about how many elements there are, nothing about the order they
 * arrive in, and nothing about the walk terminating. {@link InductiveBounds} is written against
 * exactly that and knows no operation's name.
 */
final class Reductions {

    /**
     * The operations that walk a container from a seed through their closure and answer the
     * accumulator they end with.
     *
     * <p>The semantic half, and the only part written down. {@code List.foldFrom} is the walk itself;
     * {@code List.foldRight} is it over the container reversed; {@code Set.fold} and {@code Map.fold}
     * are it over containers with no order, which changes nothing this states — what is licensed says
     * nothing about the order elements arrive in.
     */
    private static final Set<ValueName> REDUCES = Set.of(
            op("List", "foldFrom"),
            op("List", "foldRight"),
            op("Set", "fold"),
            op("Map", "fold"));

    /**
     * The operations that take a container, a seed of the type they answer, and a closure answering
     * that type, and are not a walk from the seed through the closure. The library has none.
     *
     * <p>Empty is a decision and not an oversight: every operation the range holds today is a fold
     * under some name. An operation that took this shape and applied its closure once, or answered
     * without consulting the seed, would be named here with what it does instead — and until one is
     * written the emptiness is what says the range was looked at.
     */
    static final Set<ValueName> REDUCES_NOTHING = Set.of();

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
        return operation == null ? null : Derived.RULES.get(operation);
    }

    /**
     * What {@code call} reduces, or null where it is not a reduction, or where what stands in its
     * closure argument is not a block this can read.
     *
     * <p>{@code at} is what the names around the call denote, for the reason {@link
     * Combinators#handedTo} takes one: a closure may be written as a name bound to a block.
     */
    static Reducing reducing(Core.PreservedCall call, Denotations at) {
        Reduction rule = of(call.operation());
        Combinators.Handed handed = Combinators.handedTo(call, at);
        if (rule == null || handed == null
                || rule.accumulatorParam() >= handed.step().params().size()) {
            return null;
        }
        return new Reducing(call.args().get(rule.seedArg()), handed.step(),
                handed.step().params().get(rule.accumulatorParam()), handed.element(),
                handed.container());
    }

    /** The operations there is a rule about, for the check that a rule answers a question its
     * operation is asked. */
    static Set<ValueName> answered() {
        return Derived.RULES.keySet();
    }

    /** Read once. The library is the same library for every module compiled. */
    private static final class Derived {
        private static final Map<ValueName, Reduction> RULES = read();
    }

    /**
     * The shape of each operation named a reduction, and of the sugars for one.
     *
     * <p>A sugar has no declaration, so what is true of the call it becomes is what is true of it,
     * over the arguments the rewrite keeps in place — the same reading {@link Combinators} makes.
     */
    private static Map<ValueName, Reduction> read() {
        Map<ValueName, Reduction> rules = new LinkedHashMap<>();
        for (ValueName operation : REDUCES) {
            Prelude.PreludeEntry entry = Prelude.entry(operation.toString());
            if (entry == null) {
                throw new IllegalStateException(operation + " is named a reduction and the library"
                        + " declares no such operation");
            }
            rules.put(operation, shapeOf(operation, entry.signature()));
        }
        Prelude.rewrites().forEach((sugar, rewrite) -> {
            Reduction target = rules.get(rewrite.target());
            if (target == null) {
                return;   // what it becomes reduces nothing, so neither does it
            }
            if (target.seedArg() >= rewrite.keptArgs()) {
                throw new IllegalStateException(sugar + " is sugar for " + rewrite.target()
                        + ", whose seed is not among the arguments the rewrite keeps in place —"
                        + " what it reduces from cannot be said of the sugar");
            }
            rules.put(Prelude.operation(sugar), target);
        });
        return Map.copyOf(rules);
    }

    /**
     * Where the seed and the accumulator are, read off the declaration of an operation already known
     * to be a walk from a seed.
     *
     * <p>The accumulator is what the step carries and hands back, so it is the closure parameter of
     * the type the closure answers, which is the type the operation answers. The seed is what that
     * accumulator starts as, so it is an argument of that same type — and not the closure or the
     * container, which the signature has already been read for.
     *
     * <p>A signature that admits more than one reading of either raises rather than answering half,
     * as {@link Combinators} does. Nothing in the library takes that shape: an operation whose
     * element and accumulator are one type — {@code ((A, A) -> A, A, List<A>) -> A} — would, and the
     * day one is declared it is written down here rather than guessed at.
     */
    private static Reduction shapeOf(ValueName operation, Prelude.Signature signature) {
        Combinator handed = Combinators.of(operation);
        if (handed == null) {
            throw new IllegalStateException(operation + " is named a reduction and its signature does"
                    + " not say what it hands its closure, so where its accumulator arrives cannot"
                    + " be read");
        }
        Type result = signature.result();
        int seedArg = -1;
        for (int i = 0; i < signature.params().size(); i++) {
            if (i == handed.closureArg() || i == handed.containerArg()
                    || !result.equals(signature.params().get(i))) {
                continue;
            }
            if (seedArg >= 0) {
                throw new IllegalStateException(operation + " takes two arguments of the type it"
                        + " answers, so which one it reduces from is not read off its signature");
            }
            seedArg = i;
        }
        List<Type> closureParams = ((Type.FnOf) signature.params().get(handed.closureArg())).params();
        int accumulatorParam = -1;
        for (int p = 0; p < closureParams.size(); p++) {
            if (!result.equals(closureParams.get(p))) {
                continue;
            }
            if (accumulatorParam >= 0) {
                throw new IllegalStateException(operation + " hands its closure two values of the"
                        + " type it answers, so which one is the accumulator is not read off its"
                        + " signature");
            }
            accumulatorParam = p;
        }
        if (seedArg < 0 || accumulatorParam < 0) {
            throw new IllegalStateException(operation + " is named a reduction and its signature has"
                    + (seedArg < 0 ? " no argument" : " no closure parameter")
                    + " of the type it answers");
        }
        return new Reduction(seedArg, accumulatorParam);
    }

    /** The operation {@code name} of the library module published as {@code alias}, written as the
     * two values a library name is made of — the spelling {@link DischargeRules} states its own rows
     * in. */
    private static ValueName op(String alias, String name) {
        return new ValueName.Stdlib(alias, name);
    }

    private Reductions() {}
}
