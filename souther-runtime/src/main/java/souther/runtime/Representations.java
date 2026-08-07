package souther.runtime;

import org.jspecify.annotations.Nullable;

import java.math.BigDecimal;
import java.math.BigInteger;
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
 * number is written in. Without that last part two members that no comparison separates would keep
 * whatever order the trie handed them, which is the construction history this class exists to
 * remove. {@link #canonicalNumber} means the encoders never hand it two forms of one amount, so the
 * tie-break there is what leaves the order total for any pair rather than only for the expected
 * ones.
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

    /**
     * How many digits an exponent may be spelt out into. It bounds the <em>expansion</em> and not the
     * output: a value that already carries a thousand significant digits is written with all of them,
     * here as anywhere, and that is not this rule's business. What this stops is a compact input
     * asking for an enormous output — {@code 1E+1000000} is eleven characters and a million and one
     * digits.
     *
     * <p>A thousand is where a reader gives up as well ({@code jackson-core}'s
     * {@code StreamReadConstraints.DEFAULT_MAX_NUM_LEN}), which is where the figure comes from. It is
     * a reference point and not the definition: that limit is per-factory and configurable, and the
     * form this class writes is part of the language.
     */
    private static final int MAX_SPELT_OUT_DIGITS = 1000;

    private Representations() {}

    /**
     * The amount, written the one way an amount is written. Scale records how a number was written
     * and not how much it is — the language drops it from identity (spec {@code [#primitives]}) —
     * so a boundary that kept it would write two equal values two ways.
     *
     * <p>{@code stripTrailingZeros} alone is not the form: it answers {@code 1E+2} for a hundred,
     * and a hundred is written {@code 100}. A negative scale is what an exponent is, so setting the
     * scale back to zero is what asks for the digits.
     *
     * <p>Which is bounded, because asking for the digits is what an exponent lets a caller not pay
     * for: {@code 1E+1000000} is eleven characters and a million and one digits, so spelling every
     * amount out would let a small input ask for an arbitrarily large one. The cut is
     * {@link #MAX_SPELT_OUT_DIGITS}, and it falls on the amount rather than on the value that carried it
     * — the two forms of one amount reach the same side of it, which is what keeps this a function
     * of the amount.
     */
    public static BigDecimal canonicalNumber(BigDecimal amount) {
        BigDecimal stripped = strippedAsFarAsTheScaleGoes(amount);
        if (stripped.scale() >= 0) {
            return stripped;
        }
        // in long, because a scale at the floor asks for more digits than an int can count
        long spelledOut = (long) stripped.precision() - stripped.scale();
        return spelledOut <= MAX_SPELT_OUT_DIGITS ? stripped.setScale(0) : stripped;
    }

    /**
     * The amount carried by as few digits as a {@code BigDecimal} can carry it.
     *
     * <p>{@code stripTrailingZeros} is that, until the scale it would need is one the type cannot
     * say: a scale is an {@code int}, and taking the zero off {@code (10, MIN_VALUE)} asks for
     * {@code MIN_VALUE - 1}, which it answers by throwing. Stopping at the floor instead still leaves
     * one form per amount — {@code (10, MIN_VALUE)} and {@code (100, MIN_VALUE + 1)} are one amount
     * and both stop at {@code (10, MIN_VALUE)} — because fixing the scale fixes the digits.
     */
    private static BigDecimal strippedAsFarAsTheScaleGoes(BigDecimal amount) {
        if (amount.signum() == 0) {
            return BigDecimal.ZERO;                  // every way of writing nothing is one amount
        }
        long room = (long) amount.scale() - Integer.MIN_VALUE;
        if (room >= amount.precision()) {
            return amount.stripTrailingZeros();      // fewer zeros than digits: it cannot fall out
        }
        BigInteger digits = amount.unscaledValue();
        int scale = amount.scale();
        for (long left = room; left > 0; left--) {
            BigInteger[] divided = digits.divideAndRemainder(BigInteger.TEN);
            if (divided[1].signum() != 0) {
                break;
            }
            digits = divided[0];
            scale--;
        }
        return new BigDecimal(digits, scale);
    }

    /** The members of an encoded array, in ascending order of their own external representation. */
    public static Object sortedArray(@Nullable Object encoded) {
        if (!(encoded instanceof List<?> members)) {
            throw notAnExternalForm(encoded);
        }
        return sortedMembers(members);
    }

    /** The members of an encoded object, in ascending order of their keys. */
    public static Object sortedObject(@Nullable Object encoded) {
        if (!(encoded instanceof Map<?, ?> members)) {
            throw notAnExternalForm(encoded);
        }
        return byKey(members);
    }

    /**
     * Where {@code a} is written relative to {@code b}: {@code null} first, then {@code false},
     * {@code true}, numbers, strings, arrays and objects. Numbers compare as amounts and then by the
     * form they are written in; strings by UTF-16 code unit; arrays element by element with the
     * shorter one first; objects as their members read in key order.
     */
    public static int compareExternalForms(@Nullable Object a, @Nullable Object b) {
        return compare(a, b, null);
    }

    private static int compare(@Nullable Object a, @Nullable Object b, @Nullable KeyOrders orders) {
        int form = rank(a);
        int other = rank(b);
        if (form != other) {
            return Integer.compare(form, other);
        }
        if (a == null || b == null) {
            // the ranks agree, so both are null: the rank is the whole of what a null is
            return 0;
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
    static boolean representationEquals(@Nullable Object a, @Nullable Object b) {
        int form = rank(a);
        if (form != rank(b)) {
            return false;
        }
        if (a == null || b == null) {
            // the ranks agree, so both are null: the rank is the whole of what a null is
            return true;
        }
        return switch (form) {
            case NULL, FALSE, TRUE -> true;
            case NUMBER -> asWritten(a).equals(asWritten(b));
            case STRING -> a.equals(b);
            case ARRAY -> sameArray((List<?>) a, (List<?>) b);
            default -> sameObject((Map<?, ?>) a, (Map<?, ?>) b);
        };
    }

    private static int rank(@Nullable Object v) {
        return switch (v) {
            case null -> NULL;
            case Boolean b -> b ? TRUE : FALSE;
            case Long _ -> NUMBER;
            case BigDecimal _ -> NUMBER;
            case String _ -> STRING;
            case List<?> _ -> ARRAY;
            case Map<?, ?> _ -> OBJECT;
            default -> throw notAnExternalForm(v);
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

    private static int compareArrays(List<?> a, List<?> b, @Nullable KeyOrders orders) {
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

    private static int compareObjects(Map<?, ?> a, Map<?, ?> b, @Nullable KeyOrders orders) {
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

        private @Nullable Map<Object, List<String>> known;

        List<String> of(Map<?, ?> members) {
            Map<Object, List<String>> cache = known;
            if (cache == null) {
                cache = new IdentityHashMap<>();
                known = cache;
            }
            return cache.computeIfAbsent(members, m -> sortedKeys((Map<?, ?>) m));
        }
    }

    private static List<String> keysOf(Map<?, ?> members, @Nullable KeyOrders orders) {
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
        throw notAnExternalForm(key == null ? "a null key" : key);
    }

    /** One refusal, so a carrier the encoders do not emit is reported the same wherever it lands. */
    private static IllegalStateException notAnExternalForm(@Nullable Object v) {
        return new IllegalStateException("not a Souther external representation: " + switch (v) {
            case null -> "nothing at all";     // null is a form, but it is not an array or an object
            case String said -> said;          // a phrase from the caller, not a value's own class
            default -> v.getClass();
        });
    }
}
