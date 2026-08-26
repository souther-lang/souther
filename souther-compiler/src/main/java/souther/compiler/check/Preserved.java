package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * The names the representation being typed keeps standing, and what each of them is known to be: a
 * signature for a call, a settled type for a reference to a value.
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
public record Preserved(Map<ValueName, CompleteSignature> operations, SettledValues values) {

    /**
     * What a value's own check settled it as, asked by the name it was resolved to.
     *
     * <p>A lookup rather than a map, because the answers arrive while the representation is being
     * read: a module's values are checked one after another, each against what the ones it names
     * were settled as, and a snapshot taken per definition would copy the whole set once per
     * definition — the cost this was for.
     */
    @FunctionalInterface
    public interface SettledValues {

        /** Nothing settled: every value is substituted, which is what every representation but the
         * standalone check of a value does. */
        SettledValues NONE = _ -> null;

        /** The type {@code name} was settled as, or null where nothing settled it. */
        Type typeOf(ValueName name);
    }

    /** Every representation that keeps nothing standing — the tree the backend emits from, and every
     *  expression checked outside one. */
    public static final Preserved NONE = new Preserved(Map.of(), SettledValues.NONE);

    public Preserved(Map<ValueName, CompleteSignature> operations) {
        this(operations, SettledValues.NONE);
    }

    /**
     * A representation that keeps a reference to each of {@code settled} standing, under the type
     * that value's own check settled for it.
     *
     * <p>What a value means is settled where it is declared and is the same wherever it is named
     * (ADR-0072), so a check that has that answer already needs nothing from the value's body. The
     * one it does not have is what the value is a constant of: that is folded into the reference
     * where the reference is written, so everything downstream reads a literal exactly as it did
     * when the whole body was copied there.
     */
    public static Preserved valuesAlreadySettled(SettledValues settled) {
        return new Preserved(Map.of(), settled);
    }

    /**
     * The type {@code name} was settled as, or null where this representation does not keep a
     * reference to it standing.
     *
     * <p>Asked of what the name was resolved to, as an operation is: a binding spelled like a value
     * is a binding, and two modules' same-named values are two values.
     */
    public Type valueKept(ValueName name) {
        return name == null ? null : values.typeOf(name);
    }

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
        private static final Preserved OPERATIONS = readTheLibrary(DefaultStdlib.get());
    }

    /* A pure function of the library, so the holder above is the only thing here that reaches for
     * the process's own — {@link souther.compiler.DefaultStdlib} says who may and why the loader
     * may not. */
    private static Preserved readTheLibrary(Stdlib stdlib) {
        Map<ValueName, CompleteSignature> operations = new LinkedHashMap<>();
        stdlib.entries().forEach((operation, entry) -> {
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
