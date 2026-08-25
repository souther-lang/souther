package souther.compiler.types;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * A whole type as one module writes it, or the name in it that module cannot write.
 *
 * <p>{@link TypeReachName} answers this for a single name. A type is made of several, and a caller
 * that has to write the type down needs every one of them answered before it has anything to write —
 * so the two states are held here rather than left to a caller to assemble out of a walk of its own.
 * There is no rendering on {@link Unnameable}: a caller that would write the type has to say what it
 * does where one of its names has no spelling, rather than being handed text that resolves to
 * something else, or to nothing, wherever it is put.
 *
 * <p>Whether an unnameable name is an error is not decided here. It is a fact about the type and the
 * module, and what follows from it depends on what the text was for — a message may say the type
 * cannot be named and go on, and a published signature may not. {@code meta.ModuleMetadata} is the
 * one that may not.
 */
public sealed interface TypeSpelling {

    /** The type, written the way this module writes it. */
    record Spelled(String rendered) implements TypeSpelling {}

    /**
     * The first name in the type that this module has no spelling for.
     *
     * <p>The first and not all of them. What a caller does about one is what it does about any, and a
     * report that listed every name would be listing consequences of the same fact — the same reason
     * {@code codegen.JvmLimits} names the first declaration that will not fit.
     */
    record Unnameable(TypeSymbol denotes) implements TypeSpelling {}

    /**
     * How {@code naming}'s module writes {@code type}.
     *
     * <p>Every name is asked for before any of it is written. A renderer that asked as it went would
     * have built most of a spelling before finding out that it may not have one, and the shape that
     * invites is a caller keeping the part that was ready.
     */
    static TypeSpelling of(Type type, TypeReachName.Naming naming) {
        Map<TypeSymbol, String> spelled = new LinkedHashMap<>();
        List<TypeSymbol> unnameable = new ArrayList<>();
        Type.forEachName(type, name -> {
            if (spelled.containsKey(name)) {
                return;
            }
            if (naming.of(name) instanceof TypeReachName.Written written) {
                spelled.put(name, written.rendered());
            } else {
                unnameable.add(name);
            }
        });
        if (!unnameable.isEmpty()) {
            return new Unnameable(unnameable.getFirst());
        }
        return new Spelled(Type.showAs(type, name -> spelled.get(name), false));
    }
}
