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
        /**
         * A class nothing closes, which is the same absence as the one above.
         *
         * <p>Something that says what it is and can still be extended says what it is about the
         * part it declares. What stands here may be of anything that extends it, holding whatever
         * that holds and meaning it however it likes — so a walk that opened the members it can see
         * would be reporting on a type nothing said would be the one there.
         */
        AN_OPEN_CLASS,
        /** A type variable or a wildcard nothing here binds, so what stands here is not settled
         *  either. */
        NOT_BOUND
    }

    /**
     * What a walk of the declarations found, and how much of them it opened.
     *
     * @param opened how many types it went into the members of, which is what says a walk that
     *               found nothing looked at something
     */
    record Walked(List<Found> found, int opened) {}

    /** Everything the questions in {@code keys} declare that cannot be compared as a value. */
    static Walked of(List<Class<?>> keys) {
        List<Found> out = new ArrayList<>();
        int opened = 0;
        for (Class<?> key : keys) {
            Type answered = answeredBy(key);
            Walk walk = new Walk(key.getName(), out);
            if (answered == null) {
                out.add(new Found(TypePath.ROOT.of(key.getName(), Key.class.getTypeName()),
                        Why.NOT_BOUND));
                continue;
            }
            walk.at(answered, TypePath.ROOT);
            opened += walk.opened();
        }
        return new Walked(List.copyOf(out), opened);
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

    /**
     * A type walked with the letters in it bound as they were where it was met.
     *
     * <p>The pair and not the type. One declaration reached twice under different arguments is two
     * shapes, and what is under it is two answers — remembered by the type alone, the second would
     * come back as walked already and whatever it holds would go unasked.
     */
    private record Reached(Class<?> type, Map<String, Type> bound) {}

    private static final class Walk {

        private final String question;
        private final List<Found> out;
        /** What was found under each type this has been into, as the way down from that type, so
         *  that every path reaching it says the same things about it. */
        private final Map<Reached, List<Found>> settled = new LinkedHashMap<>();
        /** What this is inside at the moment, so a declaration that reaches itself stops. */
        private final Set<Reached> walking = new LinkedHashSet<>();
        private int opened;

        Walk(String question, List<Found> out) {
            this.question = question;
            this.out = out;
        }

        /** How many types this went into the members of. */
        int opened() {
            return opened;
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
            // A sum, whichever way it is written. What stands here is one of its arms, and the walk
            // takes all of them: an arm carries what the type above it declares, so nothing is left
            // behind by going down rather than opening the sum itself.
            if (raw.isSealed()) {
                for (Class<?> arm : raw.getPermittedSubclasses()) {
                    at(arm, where.then(new TypePath.Step.Arm(arm.getTypeName())), bound);
                }
                return;
            }
            if (raw.isInterface()) {
                say(where, raw.getTypeName(), Why.AN_OPEN_INTERFACE);
                return;
            }
            // Something that can still be extended says what it says about the part it declares,
            // and a walk that read that would be reporting on a type nothing said would be the one
            // standing here. Asked before the equality, because whatever stands here brings its
            // own: writing one on what is declared would not settle what is compared.
            if (!java.lang.reflect.Modifier.isFinal(raw.getModifiers())) {
                say(where, raw.getTypeName(), Why.AN_OPEN_CLASS);
                return;
            }
            if (!AnswerShape.declaresEquals(raw)) {
                say(where, raw.getTypeName(), Why.NO_EQUALITY);
                return;
            }
            Reached reached = new Reached(raw, bound);
            List<Found> already = settled.get(reached);
            if (already != null) {
                already.forEach(each -> out.add(new Found(
                        where.followedBy(each.place().at()).of(question, each.place().offender()),
                        each.why())));
                return;
            }
            // Nothing under a type this is already inside, which is a declaration that reaches
            // itself. What is under it is being asked about where it was first met, and following
            // it again is the same question one step further down forever.
            if (!walking.add(reached)) {
                return;
            }
            opened++;
            int before = out.size();
            for (Field field : AnswerShape.fieldsOf(raw)) {
                at(field.getGenericType(),
                        where.thenMember(field.getDeclaringClass(), field.getName()), bound);
            }
            walking.remove(reached);
            // What was found under this type, as the way down from it rather than from the answer,
            // so that the next path to reach it says the same things about it. Written out at every
            // path that gets here, for the reason a place is a place: one type held two ways is two
            // places the answer exposes it, and a register keyed by the first path taken would move
            // with the order the members happen to be declared in.
            List<Found> mine = new ArrayList<>();
            for (Found each : out.subList(before, out.size())) {
                mine.add(new Found(
                        where.from(each.place().at()).of(question, each.place().offender()),
                        each.why()));
            }
            settled.put(reached, List.copyOf(mine));
        }
    }

    private DeclaredAnswerWalk() {
    }
}
