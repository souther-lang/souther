package souther.compiler.core;

import souther.compiler.abort.AbortSet;

import java.util.Objects;

/**
 * What a kernel was declared to take and to answer, and every way a call to it can end without a
 * value instead.
 *
 * <p>One value and not two parallel ones. A kernel's {@link #aborts} is read off the same
 * declaration {@link #signature} is — the standard library's, as this compiler resolved it — so an
 * output holding a kernel's contract never asks a second table that could hold fewer kernels than
 * the first, or answer a newer or older reading of one. {@link KernelContracts} is what keeps that
 * true across the whole language: total over {@link Kernel}, the way {@link KernelSignatures} was
 * before this and {@link KernelContracts} is now.
 *
 * <p>{@code aborts} answers every {@link souther.compiler.abort.AbortKind} a call to this kernel
 * can end without a value for — never {@code null}, and {@link AbortSet#NONE} where it cannot.
 * "Cannot" is itself an answer here and not an absence: a kernel added later that aborts on nothing
 * says so by name, the same way one that does names what it does.
 */
public record KernelContract(KernelSignature signature, AbortSet aborts) {

    public KernelContract {
        Objects.requireNonNull(signature, "a kernel's contract is a signature and its aborts, and"
                + " this declares no signature");
        Objects.requireNonNull(aborts, "a kernel that aborts on nothing still answers "
                + "AbortSet.NONE, and this declares no answer at all");
    }
}
