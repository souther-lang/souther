package souther.compiler.query;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

/**
 * What it takes to compare something as a value, asked of one thing at a time.
 *
 * <p>The frontier both walks stop at. One of them holds an object and asks what it is; the other
 * holds a declared type and asks what anything of that type would be — and they would answer
 * differently the day one of them learned that a case of an enumeration means what it says and the
 * other did not. So what a leaf is, what saying what it is looks like, and what a thing holds are
 * settled here and read by both.
 *
 * <p>What is not here is how to get from a thing to what it holds. A walk of objects steps into a
 * collection by asking the object what it is; a walk of types steps into it by reading the argument
 * the declaration wrote, and there is nothing to share between reading a list and reading
 * {@code List<T>}. Put here anyway, one of the two would be answering with the other's question.
 */
final class AnswerShape {

    /**
     * What the language says the meaning of, so that asking further would be asking about the JDK.
     *
     * <p><b>Named one at a time and not by what they are under.</b> A rule that admits whatever
     * extends one of these admits whatever anybody writes: something that extends {@link Number} is
     * a number the way its author says it is, and one that holds a value it can be told to change,
     * or that says only which object it is, would come back here as a thing the language settles.
     * The list is short and closing it is the whole of what makes it a rule.
     */
    private static final Set<Class<?>> WHAT_THE_LANGUAGE_SETTLES = Set.of(
            String.class, Boolean.class, Character.class,
            Byte.class, Short.class, Integer.class, Long.class, Float.class, Double.class,
            // Numbers of no fixed width, which the language ships and which say what they are:
            // what one of these compares as is the number it wrote down. Here one at a time and not
            // because of what they extend — that is the rule, not an exception to it.
            java.math.BigInteger.class, java.math.BigDecimal.class,
            // What a class is is which class it is, and nothing here goes into one.
            Class.class);

    /**
     * Whether the language says what a thing of this type is.
     *
     * <p>A case of an enumeration is one of these too, and is asked of the type rather than listed:
     * what an enumeration's cases are is written where the enumeration is, and each of them is that
     * case and no other.
     */
    static boolean isLeaf(Class<?> type) {
        return type.isPrimitive() || type.isEnum() || WHAT_THE_LANGUAGE_SETTLES.contains(type);
    }

    /**
     * The contracts under which comparing a thing compares what it holds, named one at a time.
     *
     * <p>What a declaration promises when it writes one of these is the contract: two of them are
     * equal when they hold equal things. Anything else a declaration may write — a class of this
     * compiler's own that implements a map, or one of the language's own that says it keeps none of
     * the contract — promises whatever that class promises, which is not this.
     *
     * <p><b>Each is here for what its own specification says about comparing two, and never for
     * what it is under.</b> Holding things is not the contract: what the language says about
     * comparing two collections is that it says nothing beyond comparing two objects, and something
     * that implements no more than that may answer by which object it is and be within its rights.
     * A list and a set are here because each says what comparing two of them compares; a map is;
     * an absence is; and the ordered and sorted ones are the same contracts said again over an
     * order. Adding one is reading what the language says about {@code equals} on it and writing
     * that down here, which is what {@code AWalkOfWhatIsDeclaredStopsWhereNothingSettlesItTest}
     * holds each of these to at the place a declaration writes it.
     */
    private static final Set<Class<?>> THE_CONTRACTS = Set.of(
            java.util.List.class, java.util.Set.class,
            java.util.SequencedSet.class, java.util.SortedSet.class,
            java.util.Map.class, java.util.SortedMap.class, java.util.SequencedMap.class,
            java.util.Optional.class);

    /**
     * The things the language ships that say they keep none of it.
     *
     * <p>Named, and each of them held to failing the contract by
     * {@code AWalkOfOneAnswerNamesWhatMeansNothingTest} — a name here that turned out to keep the
     * contract would be something excluded for nothing, and one that is missing is what the same
     * test's other half is for.
     */
    private static final Set<Class<?>> WHICH_KEEP_NONE_OF_IT =
            Set.of(java.util.IdentityHashMap.class);

    /**
     * Whether a declaration writing this type promises that comparing one compares what it holds.
     *
     * <p>The contract itself and not whatever implements it. A declaration naming an
     * implementation names what that implementation does, which may be to compare by which objects
     * were put in it — and read as one of these it would be read for what it holds and never asked.
     */
    static boolean standsForWhatItHolds(Class<?> type) {
        return THE_CONTRACTS.contains(type);
    }

    /**
     * Whether a thing that turned out to be of this class keeps one of those contracts.
     *
     * <p>Asked where an object is in hand and nothing was declared: the language ships one of these
     * for a walk to hold, and what it is is what it turned out to be. Of the language's own, since
     * something of this compiler's own that implements a map holds whatever else it was written to
     * hold; and not one that says it keeps none of the contract, which is written down above.
     */
    static boolean keepsThatContract(Class<?> type) {
        return !WHICH_KEEP_NONE_OF_IT.contains(type)
                && type.getModule() == Object.class.getModule()
                && (java.util.List.class.isAssignableFrom(type)
                        || java.util.Set.class.isAssignableFrom(type)
                        || java.util.Map.class.isAssignableFrom(type)
                        || type == java.util.Optional.class);
    }

    /** What is named as keeping none of it, for a test that holds each of them to it. */
    static Set<Class<?>> whichKeepNoneOfIt() {
        return WHICH_KEEP_NONE_OF_IT;
    }

    /** Whether {@code type} says what it is, rather than which object it is. */
    static boolean declaresEquals(Class<?> type) {
        try {
            return type.getMethod("equals", Object.class).getDeclaringClass() != Object.class;
        } catch (NoSuchMethodException none) {
            return false;
        }
    }

    /**
     * What a thing of this type holds, by the fields it and everything it extends declare.
     *
     * <p>A record's component and a class's field alike: both are reached the same way and neither
     * is what the walk is about — what is under a thing is what it holds, however the declaration
     * spelled the holding.
     *
     * <p>Without what is static, which belongs to the class rather than to a thing of it, and
     * without what is primitive, which the language already says the meaning of.
     */
    static List<Field> fieldsOf(Class<?> type) {
        List<Field> out = new ArrayList<>();
        for (Class<?> at = type; at != null && at != Object.class; at = at.getSuperclass()) {
            for (Field field : at.getDeclaredFields()) {
                if (!Modifier.isStatic(field.getModifiers()) && !field.getType().isPrimitive()) {
                    out.add(field);
                }
            }
        }
        return List.copyOf(out);
    }

    private AnswerShape() {
    }
}
