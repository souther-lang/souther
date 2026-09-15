package souther.compiler.meta;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.RecordComponent;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

/**
 * What a form is made of, read one way wherever this comparison asks.
 *
 * <p>Three readers ask: the comparison that holds two builds' declarations to each other, the walk
 * that follows what one of them reaches, and the check that every type a declaration can reach has
 * been classified. Each of them used to ask a record for its components, which made "a form of the
 * grammar" and "a Java record" one thing — and they are not. A form whose representation its own
 * subsystem settled for its own reasons is still a form, and a reader that cannot see inside one
 * does not say so: the comparison falls to comparing written values, the walk stops, and the check
 * reaches less and stays green. Asked here, the three see the same parts or none of them do.
 *
 * <p>A record hands over its components. Anything else hands over what it declares and lets be read
 * — an instance field with a no-argument method of the same name, which is the shape a record has
 * and the one a form written by hand keeps. A field with no such method is refused rather than
 * passed over: a part nothing can read is a part a comparison would decide without, which is the
 * failure this exists to stop. Nothing reaches into what a form does not hand out.
 */
final class StructuralParts {

    private StructuralParts() {}

    /**
     * One part: what it is called, what it is declared to hold, and how to read it off a form.
     *
     * <p>The declared type and not the value's, because the check that asks is static: what a part
     * may hold is a question about the form, and a walk over what some tree happened to build
     * answers about that tree instead.
     */
    record Part(String name, java.lang.reflect.Type held, Method read) {

        /** This part of {@code form}. */
        Object of(Object form) {
            try {
                return read.invoke(form);
            } catch (ReflectiveOperationException e) {
                throw new IllegalStateException("a part that cannot be read: " + name, e);
            }
        }
    }

    /** Whether a form of this shape hands its parts over. */
    static boolean areHandedOver(Class<?> type) {
        return type.isRecord() || DeclarationAgreement.isAFormOfTheGrammar(type);
    }

    /**
     * The parts, in an order that does not change between runs.
     *
     * <p>A record's own order, which is the one it was written in. A form read off its fields is put
     * in name order instead: what {@code getDeclaredFields} answers is not specified to be anything,
     * and an order that varies would make a comparison stop at a different part each run.
     */
    static List<Part> of(Class<?> type) {
        if (type.isRecord()) {
            List<Part> parts = new ArrayList<>(type.getRecordComponents().length);
            for (RecordComponent component : type.getRecordComponents()) {
                parts.add(new Part(component.getName(), component.getGenericType(),
                        component.getAccessor()));
            }
            return parts;
        }
        List<Part> parts = new ArrayList<>();
        for (java.lang.reflect.Field field : type.getDeclaredFields()) {
            if (Modifier.isStatic(field.getModifiers()) || field.isSynthetic()) {
                continue;
            }
            parts.add(new Part(field.getName(), field.getGenericType(),
                    handsOver(type, field.getName())));
        }
        parts.sort(Comparator.comparing(Part::name));
        return parts;
    }

    /** The method a form hands one of its parts over by. */
    private static Method handsOver(Class<?> type, String part) {
        try {
            return type.getMethod(part);
        } catch (NoSuchMethodException e) {
            throw new IllegalStateException(type.getName() + " holds `" + part + "` and hands it to"
                    + " nobody, so a comparison over what it is made of would pass it over without"
                    + " saying so. Hand it over, or hold it somewhere this does not read.", e);
        }
    }
}
