package souther.compiler.check;

import souther.compiler.Prelude;
import souther.compiler.types.ValueName;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * The calls the representation being typed keeps standing, and the signature each was declared with.
 *
 * <p>Which calls a representation keeps is the representation's to decide
 * ({@link InliningPolicy}), so it is decided once, where that representation is built, and handed to
 * the checker as this. The checker asks only whether this call is one of them: what the operation
 * means to whoever reads the representation — that a {@code List.map} carries a property of every
 * element, that a {@code List.filter} can only lose elements — is that reader's, and typing a call
 * does not depend on anyone having a rule for it.
 *
 * <p>That separation is the point. An operation kept by a representation with no rule about it types
 * like any other and simply states nothing, so being able to type a call and being able to reason
 * about it stay independent. Were the two joined, adding a rule would mean teaching the checker, and
 * a rule missing would mean a program that does not type.
 *
 * <p>What is not here is not kept. A call standing in a representation that keeps none of them, or
 * one this representation never said it would keep, is this compiler having failed to expand it, and
 * is reported as that rather than typed.
 */
public record Preserved(Map<ValueName, CompleteSignature> operations) {

    /** Every representation that keeps nothing standing — the tree the backend emits from, and every
     *  expression checked outside one. */
    public static final Preserved NONE = new Preserved(Map.of());

    /**
     * What {@link InliningPolicy#DISCHARGE} keeps: the language's own operations, each under the
     * signature the library declared it with.
     *
     * <p>The line is the one that policy draws. The language defines what these do to the properties
     * an analysis tracks and every module already has them, so leaving one standing says something; a
     * module's own helper has no such definition and is expanded. Asked of the library rather than
     * listed here, so an operation the library gains is kept without this being edited — and one it
     * rewrites away before any of this ({@code List.fold} becomes {@code List.foldFrom}) has no
     * declaration to keep and is absent, as it must be.
     *
     * <p>Built once. The library is the same library for every tree that keeps it standing, and this
     * is asked once per definition typed in such a representation.
     */
    public static Preserved byTheLanguagesOwnOperations() {
        return TheLanguagesOwn.OPERATIONS;
    }

    /**
     * Built on the first ask and not before. What is required of these signatures is required of a
     * representation that keeps them standing, so a checker that keeps none must not be held to it —
     * and a class is initialized whole, so building this beside {@link #NONE} would raise the
     * discharge representation's demand the moment anything asked for no representation at all.
     */
    private static final class TheLanguagesOwn {
        private static final Preserved OPERATIONS = readTheLibrary();
    }

    private static Preserved readTheLibrary() {
        Map<ValueName, CompleteSignature> operations = new LinkedHashMap<>();
        Prelude.entries().forEach((qualified, entry) -> {
            ValueName.Stdlib operation = Prelude.operation(qualified);
            operations.put(operation, CompleteSignature.of(
                    operation, entry.signature().params(), entry.signature().result()));
        });
        return new Preserved(operations);
    }

    public Preserved {
        operations = Map.copyOf(operations);
    }

    /**
     * The signature {@code operation} was declared with, or null where this representation does not
     * keep it standing.
     *
     * <p>Asked of what the name was resolved to rather than of how it was written: a module that
     * imported an operation writes it bare, and one that did not writes it qualified, and they are
     * the same operation. Two operations that share a type are not.
     */
    public CompleteSignature signatureOf(ValueName operation) {
        return operation == null ? null : operations.get(operation);
    }
}
