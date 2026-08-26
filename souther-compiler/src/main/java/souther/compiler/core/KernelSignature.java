package souther.compiler.core;

import souther.compiler.types.Type;

import java.util.List;
import java.util.Objects;

/**
 * What a kernel was declared to take and to answer.
 *
 * <p>The declaration is Souther, written in a core module, and this is that declaration's types as
 * the checker resolved them. It belongs to the callee: an output emitting a call builds its own
 * boundary form out of this, and the types at the call supply values rather than the shape of the
 * thing being called. The two agree only where a declared parameter is a type no value can arrive
 * narrower than, and a sum-typed parameter ends that — the argument's type is the case it happens
 * to be, while the declaration names the sum.
 *
 * <p>{@code result} is the return type as it was declared, whole. A kernel that can depart declares
 * the departure beside what it answers with ({@code Decimal | DivisionByZero}), and the union is
 * what a value of it is; splitting the success half off here would leave every reader to work out
 * what carries the rest.
 *
 * <p>Not a boundary form. Which JVM descriptor, Wasm type or class name these become is whichever
 * output is emitting, and two outputs may settle them differently without the kernel taking
 * anything different.
 *
 * <p>Distinct from {@code program.CheckedSignature}, which the shape does not say. That one is what
 * the check settled for a behavior of a program; this is what the language declares of an operation
 * of its own, and the two are asked in different places for different reasons.
 */
public record KernelSignature(List<Type> parameters, Type result) {

    /**
     * @throws NullPointerException where the declaration writes no return type. A kernel has no body
     *     to infer one from, so what it answers is only ever what it declared — there is no state of
     *     this value standing for a kernel whose answer is not yet known, and nothing downstream has
     *     to ask whether there is one.
     */
    public KernelSignature {
        parameters = List.copyOf(parameters);
        Objects.requireNonNull(result, "a kernel answers what it declared, and this declares nothing");
    }
}
