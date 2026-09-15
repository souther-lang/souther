package souther.compiler.meta;

import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * The types a part is declared to hold, for a sweep over what a declaration can reach.
 *
 * <p>Refuses a part it cannot name rather than answering none. A sweep says something about every
 * type a declaration reaches, and a part whose declared type names nothing a reader here knows is
 * one the sweep would walk past — reaching less and staying green, which is the failure these
 * sweeps exist to catch and the one they would then be having. So the day a form is written to hold
 * whatever it was made with, the sweep stops and says so, and whoever adds it decides what a sweep
 * over what a declaration reaches means for it.
 *
 * <p>A reader that has to be right about what arrives asks the value instead, which is what the
 * reading of equality does. Nothing here is that reader: these are static sweeps, and what they are
 * held to is the declarations.
 */
final class TypesAPartIsDeclaredToHold {

    private TypesAPartIsDeclaredToHold() {}

    /** What a part declared as {@code part} holds: itself, or what its container is of. */
    static List<Class<?>> named(Type part) {
        if (part instanceof Class<?> plain) {
            return plain.isArray() ? List.of(plain.getComponentType()) : List.of(plain);
        }
        if (part instanceof ParameterizedType parameterized
                && parameterized.getRawType() instanceof Class<?> raw) {
            if (!Collection.class.isAssignableFrom(raw) && !Map.class.isAssignableFrom(raw)
                    && raw != Optional.class) {
                throw new IllegalStateException(raw.getName() + " is written with what it holds, and"
                        + " a sweep over what a declaration reaches has no way through one. Read it"
                        + " the way the containers above are read, or say what a sweep should make"
                        + " of it.");
            }
            List<Class<?>> of = new ArrayList<>();
            for (Type argument : parameterized.getActualTypeArguments()) {
                of.addAll(named(argument));
            }
            return of;
        }
        throw new IllegalStateException(part.getTypeName() + " names no type a sweep can go on"
                + " from, so a sweep that passed it over would reach less and say nothing about"
                + " what it did not reach.");
    }
}
