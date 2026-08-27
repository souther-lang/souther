package souther.compiler.query;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.List;

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
     * Whether the language says what a thing of this type is, so that asking further would be
     * asking about the JDK.
     *
     * <p>A number, a string, a case of an enumeration, a class: each of these means what it says,
     * and no walk has anything to add about one.
     */
    static boolean isLeaf(Class<?> type) {
        return type.isPrimitive() || type == String.class || Number.class.isAssignableFrom(type)
                || type == Boolean.class || type == Character.class || type.isEnum()
                || type == Class.class;
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
