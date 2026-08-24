package souther.compiler.semantics;

import java.math.BigDecimal;
import java.util.Optional;

/**
 * What a reader can say about the arguments a fact names, which is the constant each of them reads
 * as.
 *
 * <p>Only that. Whether the argument is there at all, and whether what stands at it is the kind of
 * thing the fact is about, are settled before any call is read
 * ({@code check.OperationFactBinder}) — so what is left for a reader at the call is the one
 * question this asks, and an answer of {@link Optional#empty()} says this reader does not know the
 * value rather than that there is no such argument.
 *
 * <p>Asked rather than handed over as a map, because what a value reads as is the reading's answer
 * and not a property of the syntax at the call: a name given a constant is that constant, wherever
 * it was written.
 */
@FunctionalInterface
public interface ConstantArguments {

    /** The constant {@code argument} reads as, or empty where this reader cannot say. */
    Optional<BigDecimal> at(ArgumentRef argument);

    /** A reader that knows no argument's value — what an operation's own facts are read under where
     *  there is no call in hand, and what an operation given no number is read under always. */
    ConstantArguments NONE = _ -> Optional.empty();

    /**
     * Whether these meet the condition a bound was stated under.
     *
     * <p>One reading of a {@link ResultBound.Provided} and not one per reader. The condition is
     * about the arguments, so it is answered wherever the arguments are answered — and a reader that
     * knows none of them meets only the condition that asks nothing, which is the bound the
     * operation states whatever it is given.
     */
    default boolean satisfy(ResultBound.Provided provided) {
        return switch (provided) {
            case ResultBound.Provided.Always _ -> true;
            case ResultBound.Provided.ConstantAboveZero above ->
                    at(above.argument()).filter(read -> read.signum() > 0).isPresent();
        };
    }
}
