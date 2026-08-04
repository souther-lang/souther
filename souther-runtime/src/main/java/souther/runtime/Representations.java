package souther.runtime;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * The order a boundary writes a collection's members in, and it is the order of their <em>external
 * representations</em> — not of the Souther values behind them. A {@code Set}'s element is only
 * required to answer equality, so most of them have no ordering at all ({@code TypeOps.isOrdered}
 * gives one to five primitives and nothing else); ordering by what is written instead is defined for
 * every member a boundary can carry, because having an external representation is what being a
 * boundary type means.
 *
 * <p>The law the rest of it rests on: <strong>comparing two forms answers zero exactly when they are
 * the same JSON value.</strong> Same, there, treats an object's member order as insignificant and
 * everything else as significant — an array's order is part of what it is, and so is the form a
 * number is written in, since {@code 1}, {@code 1.0} and {@code 1.00} are one amount and three
 * numbers on the wire. Without that last part two members that no comparison separates would keep
 * whatever order the trie handed them, which is the construction history this class exists to
 * remove.
 *
 * <p>An object's member order is ignored so that the comparison does not depend on the thing it is
 * used to decide. Reading members in key order is what makes the answer independent of who produced
 * the value. Two forms this class calls the same are nonetheless written byte for byte the same,
 * because the members being compared are of one type — an array's members are a {@code Set<T>}'s and
 * so are all {@code T}, and a sum's cases are told apart by the discriminator they carry — and one
 * type's members are written in one order: a data's in declaration order, a map's in key order.
 *
 * <p>Who moves what, because it is easy to read one of these as another:
 *
 * <ul>
 *   <li>{@link #sortedObject} reorders its own members and does not touch what they hold.
 *   <li>{@link #compareExternalForms} descends into members and reorders nothing.
 *   <li>A nested {@code Set} or {@code Map} is already sorted by its own encoder before it arrives.
 *   <li>A product data's fields stay in declaration order. That is a different contract and this
 *       class does not have an opinion about it.
 * </ul>
 *
 * <p>The forms are the closed set the encoders emit: {@code null}, a {@code Boolean}, a {@code Long}
 * or {@code BigDecimal}, a {@code String} (a temporal is written as one), a {@code List} and a
 * {@code Map}. Anything else is refused rather than given some order, because a carrier that reached
 * here unrecognised means the codec contract broke, and a silently wrong order is the one failure
 * that would not be noticed.
 */
public final class Representations {

    private static final int NULL = 0;
    private static final int FALSE = 1;
    private static final int TRUE = 2;
    private static final int NUMBER = 3;
    private static final int STRING = 4;
    private static final int ARRAY = 5;
    private static final int OBJECT = 6;

    private Representations() {}

    /** The members of an encoded array, in ascending order of their own external representation. */
    public static Object sortedArray(Object encoded) {
        return sortedMembers((List<?>) encoded);
    }

    /** The members of an encoded object, in ascending order of their keys. */
    public static Object sortedObject(Object encoded) {
        return byKey((Map<?, ?>) encoded);
    }

    /**
     * Where {@code a} is written relative to {@code b}: {@code null} first, then {@code false},
     * {@code true}, numbers, strings, arrays and objects. Numbers compare as amounts and then by the
     * form they are written in; strings by UTF-16 code unit; arrays element by element with the
     * shorter one first; objects as their members read in key order.
     */
    public static int compareExternalForms(Object a, Object b) {
        return compare(a, b, null);
    }

    private static int compare(Object a, Object b, KeyOrders orders) {
        int form = rank(a);
        int other = rank(b);
        if (form != other) {
            return Integer.compare(form, other);
        }
        return switch (form) {
            case NULL, FALSE, TRUE -> 0;
            case NUMBER -> compareNumbers(a, b);
            case STRING -> ((String) a).compareTo((String) b);
            case ARRAY -> compareArrays((List<?>) a, (List<?>) b, orders);
            default -> compareObjects((Map<?, ?>) a, (Map<?, ?>) b, orders);
        };
    }

    /**
     * Whether the two are written the same, answered on its own terms rather than by asking
     * {@link #compareExternalForms} for a zero, so that the two are a check on each other. That is
     * the whole of what it is for, so it is not public: what a boundary needs is the order.
     *
     * <p>It takes no shortcut for two references that are the same object. One would be right about
     * the answer and wrong about the domain — a container may be a form this class writes while what
     * it holds is not — and stopping at the outside would accept, at one entry point, what the other
     * refuses.
     */
    static boolean representationEquals(Object a, Object b) {
        int form = rank(a);
        if (form != rank(b)) {
            return false;
        }
        return switch (form) {
            case NULL, FALSE, TRUE -> true;
            case NUMBER -> asWritten(a).equals(asWritten(b));
            case STRING -> a.equals(b);
            case ARRAY -> sameArray((List<?>) a, (List<?>) b);
            default -> sameObject((Map<?, ?>) a, (Map<?, ?>) b);
        };
    }

    private static int rank(Object v) {
        return switch (v) {
            case null -> NULL;
            case Boolean b -> b ? TRUE : FALSE;
            case Long _ -> NUMBER;
            case BigDecimal _ -> NUMBER;
            case String _ -> STRING;
            case List<?> _ -> ARRAY;
            case Map<?, ?> _ -> OBJECT;
            default -> throw new IllegalStateException(
                    "not a Souther external representation: " + v.getClass());
        };
    }

    /**
     * The amount decides, and where it cannot, the form does. Two {@code Decimal}s that differ only
     * in scale are one amount (the language drops scale from identity) and two numbers on the wire,
     * so leaving them tied would let whichever arrived first stay first.
     */
    private static int compareNumbers(Object a, Object b) {
        if (a instanceof Long x && b instanceof Long y) {
            return Long.compare(x, y);
        }
        int byAmount = asAmount(a).compareTo(asAmount(b));
        return byAmount != 0 ? byAmount : asWritten(a).compareTo(asWritten(b));
    }

    private static BigDecimal asAmount(Object number) {
        return number instanceof BigDecimal d ? d : BigDecimal.valueOf((Long) number);
    }

    /** What the encoder writes for this number — which is what each carrier's own toString is. */
    private static String asWritten(Object number) {
        return number.toString();
    }

    private static int compareArrays(List<?> a, List<?> b, KeyOrders orders) {
        Iterator<?> xs = a.iterator();
        Iterator<?> ys = b.iterator();
        while (xs.hasNext() && ys.hasNext()) {
            int c = compare(xs.next(), ys.next(), orders);
            if (c != 0) {
                return c;
            }
        }
        return Integer.compare(a.size(), b.size());
    }

    private static int compareObjects(Map<?, ?> a, Map<?, ?> b, KeyOrders orders) {
        List<String> xs = keysOf(a, orders);
        List<String> ys = keysOf(b, orders);
        for (int i = 0; i < Math.min(xs.size(), ys.size()); i++) {
            int byKey = xs.get(i).compareTo(ys.get(i));
            if (byKey != 0) {
                return byKey;
            }
            int byValue = compare(a.get(xs.get(i)), b.get(ys.get(i)), orders);
            if (byValue != 0) {
                return byValue;
            }
        }
        return Integer.compare(xs.size(), ys.size());
    }

    private static boolean sameArray(List<?> a, List<?> b) {
        if (a.size() != b.size()) {
            return false;
        }
        Iterator<?> xs = a.iterator();
        Iterator<?> ys = b.iterator();
        while (xs.hasNext()) {
            if (!representationEquals(xs.next(), ys.next())) {
                return false;
            }
        }
        return true;
    }

    private static boolean sameObject(Map<?, ?> a, Map<?, ?> b) {
        if (a.size() != b.size()) {
            return false;
        }
        for (Map.Entry<?, ?> e : a.entrySet()) {
            requireKey(e.getKey());
            // containsKey rather than a null from get: a member that is written null and a member
            // that is not there are two different objects, and get cannot tell them apart
            if (!b.containsKey(e.getKey()) || !representationEquals(e.getValue(), b.get(e.getKey()))) {
                return false;
            }
        }
        return true;
    }

    private static List<Object> sortedMembers(List<?> members) {
        List<Object> out = new ArrayList<>(members);
        KeyOrders orders = new KeyOrders();
        out.sort((a, b) -> compare(a, b, orders));
        return out;
    }

    /**
     * The key order each object is read in, remembered for the length of one sort. A sort asks about
     * the same member O(log n) times and reads it the same way every time, so working the order out
     * per comparison is the sort's cost over again — and it is the whole of it for a member that is
     * an object, which every member of a {@code Set} of data is.
     *
     * <p>Kept by identity, not by equality: two members that are written the same are still two
     * objects, and asking whether they are equal is the question being answered. The map is made on
     * first use, so a {@code Set} of strings or numbers never allocates one.
     */
    private static final class KeyOrders {

        private Map<Object, List<String>> known;

        List<String> of(Map<?, ?> members) {
            if (known == null) {
                known = new IdentityHashMap<>();
            }
            return known.computeIfAbsent(members, m -> sortedKeys((Map<?, ?>) m));
        }
    }

    private static List<String> keysOf(Map<?, ?> members, KeyOrders orders) {
        return orders == null ? sortedKeys(members) : orders.of(members);
    }

    private static Map<String, Object> byKey(Map<?, ?> members) {
        List<String> keys = sortedKeys(members);
        Map<String, Object> out = LinkedHashMap.newLinkedHashMap(keys.size());
        for (String key : keys) {
            out.put(key, members.get(key));
        }
        return out;
    }

    private static List<String> sortedKeys(Map<?, ?> members) {
        List<String> keys = new ArrayList<>(members.size());
        for (Object key : members.keySet()) {
            keys.add(requireKey(key));
        }
        keys.sort(null);
        return keys;
    }

    /** A boundary object is keyed by strings, so a key that is not one means the codec broke. */
    private static String requireKey(Object key) {
        if (key instanceof String s) {
            return s;
        }
        throw new IllegalStateException("not a Souther external representation: "
                + (key == null ? "a null key" : key.getClass()));
    }
}
