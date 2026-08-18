package souther.compiler.query;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Where two answers to one question stop being the same thing, and why.
 *
 * <p>A pair walk and not a scan of one of them. What makes an answer fail to compare is not always
 * something with no {@code equals}: a record whose component is a way of reading a store has an
 * {@code equals} of its own and still says no, because the two stores are two objects. Only holding
 * the two side by side says which is which.
 *
 * @param path where in the answer the two came apart, as field names from the answer down
 * @param cause the class the two are of at that point, or the array type
 * @param kind whether the two say the same thing there, or different things
 */
record Divergence(String path, String cause, Divergence.Kind kind) {

    /** What a divergence means. */
    enum Kind {
        /**
         * The two are the same thing said twice and compare unequal anyway — an array, a class with
         * no {@code equals} of its own, or one whose {@code equals} rests on something that is one
         * object per store. Nothing downstream of it can ever be kept.
         */
        THE_SAME_THING_TWICE,
        /**
         * The two say different things. One compile of one input answered differently from another,
         * which is not about equality at all.
         */
        DIFFERENT_THINGS
    }

    /** Where {@code a} and {@code b} come apart, empty where nothing downstream can tell them
     *  apart. */
    static List<Divergence> between(Object a, Object b) {
        List<Divergence> out = new ArrayList<>();
        new Walk(out).at(a, b, "");
        return out;
    }

    private static final class Walk {

        /**
         * Pairs already walked, so a graph that loops is walked once.
         *
         * <p>A set that compares its members and not their addresses, because a pair is made where
         * it is asked about and is never the same object twice. What is compared is what
         * {@link Pair} says: the two sides by address, which is the question — whether these two
         * objects have been walked together — and not whether two objects are equal, which is what
         * the walk is here to find out.
         */
        private final Set<Pair> seen = new HashSet<>();
        private final List<Divergence> out;
        /** A walk of two whole answers is bounded, so a graph nobody meant to walk stops. */
        private int budget = 400_000;

        Walk(List<Divergence> out) {
            this.out = out;
        }

        private static boolean opaque(Class<?> c) {
            return c == String.class || Number.class.isAssignableFrom(c) || c == Boolean.class
                    || c == Character.class || c.isEnum();
        }

        private void say(String path, Class<?> c, Kind kind) {
            out.add(new Divergence(path, c.isArray() ? c.getSimpleName() : c.getName(), kind));
        }

        void at(Object a, Object b, String path) {
            if (a == b || budget-- <= 0) {
                return;
            }
            if (a == null || b == null || a.getClass() != b.getClass()) {
                say(path, (a == null ? b : a).getClass(), Kind.DIFFERENT_THINGS);
                return;
            }
            Class<?> c = a.getClass();
            if (opaque(c)) {
                if (!a.equals(b)) {
                    say(path, c, Kind.DIFFERENT_THINGS);
                }
                return;
            }
            // The store itself is where a walk stops. Every answer in it is being compared already,
            // and an answer that holds it holds one object per store however deep the walk goes.
            if (a instanceof Db) {
                say(path, c, Kind.THE_SAME_THING_TWICE);
                return;
            }
            if (!seen.add(new Pair(a, b))) {
                return;
            }
            int before = out.size();
            descend(a, b, c, path);
            if (out.size() == before && !a.equals(b)) {
                say(path, c, Kind.THE_SAME_THING_TWICE);
            }
        }

        private void descend(Object a, Object b, Class<?> c, String path) {
            if (c.isArray()) {
                int length = java.lang.reflect.Array.getLength(a);
                if (length != java.lang.reflect.Array.getLength(b)) {
                    say(path, c, Kind.DIFFERENT_THINGS);
                    return;
                }
                for (int i = 0; i < length; i++) {
                    at(java.lang.reflect.Array.get(a, i), java.lang.reflect.Array.get(b, i),
                            path + "[]");
                }
                // An array compares by identity, so where the elements agree the caller's own
                // check is what names it.
                return;
            }
            if (a instanceof Map<?, ?> left && b instanceof Map<?, ?> right) {
                if (!left.keySet().equals(right.keySet())) {
                    say(path, c, Kind.DIFFERENT_THINGS);
                    return;
                }
                left.forEach((key, value) -> at(value, right.get(key), path + ".value"));
                return;
            }
            if (a instanceof Collection<?> left && b instanceof Collection<?> right) {
                if (left.size() != right.size()) {
                    say(path, c, Kind.DIFFERENT_THINGS);
                    return;
                }
                Iterator<?> theirs = right.iterator();
                for (Object each : left) {
                    at(each, theirs.next(), path + "[]");
                }
                return;
            }
            if (a.equals(b)) {
                return;
            }
            for (Class<?> k = c; k != null && k != Object.class; k = k.getSuperclass()) {
                for (Field f : k.getDeclaredFields()) {
                    if (Modifier.isStatic(f.getModifiers())) {
                        continue;
                    }
                    try {
                        f.setAccessible(true);
                        at(f.get(a), f.get(b), path + "." + f.getName());
                    } catch (ReflectiveOperationException | RuntimeException | Error _) {
                        // Nothing this can say about a field it cannot read. The class itself is
                        // still reported where the descent finds nothing.
                    }
                }
            }
        }
    }

    /** Two objects walked together, by identity. */
    private record Pair(Object left, Object right) {
        @Override
        public boolean equals(Object other) {
            return other instanceof Pair pair && pair.left == left && pair.right == right;
        }

        @Override
        public int hashCode() {
            return System.identityHashCode(left) * 31 + System.identityHashCode(right);
        }
    }
}
