package souther.compiler.query;

import java.lang.reflect.Field;
import java.lang.reflect.GenericArrayType;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.lang.reflect.TypeVariable;
import java.lang.reflect.WildcardType;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * What a question declares it answers with, walked as the declarations wrote it.
 *
 * <p>The other half of the closure, and not a cheaper way of asking what a store already holds. A
 * walk of a store quantifies over what a corpus reached; this quantifies over what the compiler
 * declares, which is settled before anything is compiled. Neither contains the other: a question no
 * corpus puts is invisible to the first, and what a declaration allows is wider than what any run
 * happened to build.
 *
 * <p><b>It stops where an equality stops.</b> A type that says nothing by {@code equals} is named
 * and the walk goes no further under it, exactly as the walk of objects does — what is under such a
 * type is unreachable through an equality that never holds, and reporting it would be reporting the
 * consequences of the thing already reported.
 *
 * <p><b>What a declaration does not settle is a finding and not a silence.</b> An interface nothing
 * closes could be anything at all when a compile puts something there, and an array says which
 * object it is however its elements compare — so both are named here rather than walked into and
 * found clean. A sum that is closed is walked into every arm, which is what makes the difference
 * between the two worth having.
 *
 * <p>A type that reaches itself is walked once. A declaration that holds another of its own kind is
 * a shape and not a defect, so meeting one again is the end of that path rather than a gap: what is
 * under it has been asked about already, at the place it was first met.
 */
final class DeclaredAnswerWalk {

    /** One type in one place, and why the walk stopped there. */
    record Found(TypePath.Place place, Why why) {}

    /** What a declaration failed to settle, or what it settled on that cannot compare. */
    enum Why {
        /** An array, which says which object it is however its elements compare. */
        AN_ARRAY,
        /** A class that says nothing by {@code equals}. */
        NO_EQUALITY,
        /** An interface nothing closes, so what stands here is not settled by the declaration. */
        AN_OPEN_INTERFACE,
        /** A type variable or a wildcard nothing here binds, so what stands here is not settled
         *  either. */
        NOT_BOUND
    }

    /** Everything the questions in {@code keys} declare that cannot be compared as a value. */
    static List<Found> of(List<Class<?>> keys) {
        List<Found> out = new ArrayList<>();
        for (Class<?> key : keys) {
            Type answered = answeredBy(key);
            Walk walk = new Walk(key.getName(), out);
            if (answered == null) {
                out.add(new Found(TypePath.ROOT.of(key.getName(), Key.class.getTypeName()),
                        Why.NOT_BOUND));
                continue;
            }
            walk.at(answered, TypePath.ROOT);
        }
        return List.copyOf(out);
    }

    /**
     * The type {@code key} answers with, with what a longer way round bound substituted through.
     *
     * <p>A question may reach {@link Key} through an interface of its own — what a compilation is
     * given goes through {@link Input} — and the argument it wrote is on that interface rather than
     * on this one. Read without following the binding, every such question would answer with the
     * letter its interface calls the type, which is a question this walk cannot ask anything about.
     */
    private static Type answeredBy(Class<?> key) {
        return answeredBy(key, Map.of());
    }

    private static Type answeredBy(Class<?> at, Map<String, Type> bound) {
        for (Type each : at.getGenericInterfaces()) {
            if (each instanceof ParameterizedType wrote
                    && wrote.getRawType() instanceof Class<?> raw) {
                if (raw == Key.class) {
                    return substituted(wrote.getActualTypeArguments()[0], bound);
                }
                if (Key.class.isAssignableFrom(raw)) {
                    Map<String, Type> under = new LinkedHashMap<>();
                    TypeVariable<?>[] letters = raw.getTypeParameters();
                    Type[] wrotten = wrote.getActualTypeArguments();
                    for (int i = 0; i < letters.length && i < wrotten.length; i++) {
                        under.put(letters[i].getName(), substituted(wrotten[i], bound));
                    }
                    Type found = answeredBy(raw, under);
                    if (found != null) {
                        return found;
                    }
                }
                continue;
            }
            if (each instanceof Class<?> raw && raw != Key.class
                    && Key.class.isAssignableFrom(raw)) {
                Type found = answeredBy(raw, Map.of());
                if (found != null) {
                    return found;
                }
            }
        }
        return at.getSuperclass() == null ? null : answeredBy(at.getSuperclass(), bound);
    }

    /** {@code type} with whatever {@code bound} says about the letters in it put in its place. */
    private static Type substituted(Type type, Map<String, Type> bound) {
        return type instanceof TypeVariable<?> letter
                ? bound.getOrDefault(letter.getName(), type) : type;
    }

    private static final class Walk {

        private final String question;
        private final List<Found> out;
        /** Types already walked under this question, so a declaration that reaches itself is
         *  followed once. */
        private final Set<String> walked = new LinkedHashSet<>();

        Walk(String question, List<Found> out) {
            this.question = question;
            this.out = out;
        }

        private void say(TypePath where, String offender, Why why) {
            out.add(new Found(where.of(question, offender), why));
        }

        void at(Type type, TypePath where) {
            at(type, where, Map.of());
        }

        private void at(Type type, TypePath where, Map<String, Type> bound) {
            switch (type) {
                case Class<?> raw -> ofClass(raw, where, bound);
                case ParameterizedType wrote -> ofParameterized(wrote, where, bound);
                case GenericArrayType array -> say(where, array.getTypeName(), Why.AN_ARRAY);
                case TypeVariable<?> letter -> {
                    Type found = bound.get(letter.getName());
                    if (found == null) {
                        say(where, letter.getTypeName(), Why.NOT_BOUND);
                        return;
                    }
                    at(found, where, bound);
                }
                // What stands under a bound is anything the bound admits, which is the same question
                // as a member declared as the bound — so it is asked that way and not refused for
                // being written with a `?`.
                case WildcardType wildcard -> {
                    Type[] upper = wildcard.getUpperBounds();
                    if (upper.length != 1) {
                        say(where, wildcard.getTypeName(), Why.NOT_BOUND);
                        return;
                    }
                    at(upper[0], where, bound);
                }
                default -> say(where, type.getTypeName(), Why.NOT_BOUND);
            }
        }

        private void ofParameterized(ParameterizedType wrote, TypePath where,
                                     Map<String, Type> bound) {
            if (!(wrote.getRawType() instanceof Class<?> raw)) {
                say(where, wrote.getTypeName(), Why.NOT_BOUND);
                return;
            }
            if (held(raw, wrote.getActualTypeArguments(), where, bound)) {
                return;
            }
            // Something of its own that takes arguments. What it holds is its members, read with
            // the arguments this declaration wrote put in the letters' place.
            Map<String, Type> under = new LinkedHashMap<>();
            TypeVariable<?>[] letters = raw.getTypeParameters();
            Type[] arguments = wrote.getActualTypeArguments();
            for (int i = 0; i < letters.length && i < arguments.length; i++) {
                under.put(letters[i].getName(), substituted(arguments[i], bound));
            }
            ofClass(raw, where, under);
        }

        /**
         * A container the JDK declares, walked by what the declaration says it holds.
         *
         * @return whether this was one
         */
        private boolean held(Class<?> raw, Type[] arguments, TypePath where,
                             Map<String, Type> bound) {
            if ((Collection.class.isAssignableFrom(raw) || raw == Optional.class)
                    && arguments.length == 1) {
                at(arguments[0], where.then(new TypePath.Step.Argument("held")), bound);
                return true;
            }
            if (Map.class.isAssignableFrom(raw) && arguments.length == 2) {
                at(arguments[0], where.then(new TypePath.Step.Argument("key")), bound);
                at(arguments[1], where.then(new TypePath.Step.Argument("value")), bound);
                return true;
            }
            return false;
        }

        private void ofClass(Class<?> raw, TypePath where, Map<String, Type> bound) {
            if (AnswerShape.isLeaf(raw)) {
                return;
            }
            if (raw.isArray()) {
                say(where, raw.getTypeName(), Why.AN_ARRAY);
                return;
            }
            // A container written without its arguments holds whatever anybody put in it.
            if (Collection.class.isAssignableFrom(raw) || Map.class.isAssignableFrom(raw)
                    || raw == Optional.class) {
                say(where, raw.getTypeName(), Why.NOT_BOUND);
                return;
            }
            if (raw.isInterface()) {
                if (!raw.isSealed()) {
                    say(where, raw.getTypeName(), Why.AN_OPEN_INTERFACE);
                    return;
                }
                for (Class<?> arm : raw.getPermittedSubclasses()) {
                    at(arm, where.then(new TypePath.Step.Arm(arm.getTypeName())), bound);
                }
                return;
            }
            if (!AnswerShape.declaresEquals(raw)) {
                say(where, raw.getTypeName(), Why.NO_EQUALITY);
                return;
            }
            // An abstract class that says what it is still leaves what stands here to whatever
            // extends it, and nothing closes that.
            if (!walked.add(raw.getTypeName() + " " + bound)) {
                return;
            }
            for (Field field : AnswerShape.fieldsOf(raw)) {
                at(field.getGenericType(),
                        where.thenMember(field.getDeclaringClass(), field.getName()), bound);
            }
        }
    }

    private DeclaredAnswerWalk() {
    }
}
