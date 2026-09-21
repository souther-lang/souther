package souther.compiler.core;

import souther.compiler.types.LanguageCaseId;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;

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
     * @throws NullPointerException where {@code result} is null. There is no state of this value
     *     standing for a kernel whose answer is not yet known, so nothing downstream asks whether
     *     there is one. What refuses a declaration that states no return type — and says which — is
     *     the library, where the declaration is read.
     */
    public KernelSignature {
        parameters = List.copyOf(parameters);
        Objects.requireNonNull(result, "a kernel answers what it declared, and this declares nothing");
    }

    /**
     * The language's own cases the declared result names directly.
     *
     * <p>A projection of {@link #result()} and not a second declaration. A kernel that can depart
     * declares the departure as a member of the union it answers, so a member of the language's own
     * is where that answer already is. An output holding a kernel against a spelling and searching
     * the union for the member carrying it works out what the declaration settled, and reads a name
     * that moves when the case is renamed.
     *
     * <p>Members, which is what this says and the whole of it. Which of them a call reaches is the
     * runtime's, and which of them the kernel itself constructs rather than passes on is a question
     * the language does not ask here: the day a kernel answers with a case it was handed, that is a
     * fact about the kernel and belongs beside one, not read off the members the result happens to
     * have.
     *
     * <p>A set, so the width of a union is the union's. An output whose boundary form carries one
     * case descriptor refuses a second where it emits, as a limit of what it can lower; told here
     * that there is at most one, it would emit against a shape the language never promised.
     *
     * <p>The iteration order is not part of what this answers. {@link Type.Union} holds its members
     * in the order they are shown, which is this compiler's own way of writing a union down and no
     * calling convention.
     *
     * <p>{@code Option}'s two cases are not among these: an arm naming one dispatches on the
     * option's own cases and names nothing the language declares
     * ({@link LanguageCaseId#isNamedAsALanguageCase}).
     */
    public Set<TypeSymbol.LanguageCase> languageCaseMembers() {
        if (result instanceof Type.Ref(TypeSymbol.LanguageCase only)) {
            return only.id().isNamedAsALanguageCase() ? Set.of(only) : Set.of();
        }
        if (!(result instanceof Type.Union union)) {
            return Set.of();
        }
        Set<TypeSymbol.LanguageCase> named = new LinkedHashSet<>();
        for (TypeSymbol member : union.members()) {
            if (member instanceof TypeSymbol.LanguageCase given
                    && given.id().isNamedAsALanguageCase()) {
                named.add(given);
            }
        }
        return Collections.unmodifiableSet(named);
    }
}
