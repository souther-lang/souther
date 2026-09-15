package souther.compiler.meta;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.RecordComponent;
import java.lang.reflect.Type;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

/**
 * What a form is made of, read one way wherever this comparison asks.
 *
 * <p>A reader that goes inside a form asks here rather than working out for itself what one is made
 * of. Readers used to ask a record for its components, which made "a form of the grammar" and "a
 * Java record" one thing — and they are not. A form whose representation its own subsystem settled
 * for its own reasons is still a form, and a reader that cannot see inside one does not say so: a
 * comparison falls to comparing written values, a walk stops, a check reaches less and stays green.
 * Asked here, readers see the same parts or none of them do.
 *
 * <p>A record hands over its components. Anything else hands over what it declares and lets be read
 * — a final instance field with a no-argument method of the same name answering the type the field
 * holds, which is the shape a record has and the one a form written by hand keeps. Each of those is
 * refused rather than passed over, since a part nothing can read is a part a comparison would decide
 * without and a part handed over as something else is the two readers here looking at two things.
 * Nothing reaches into what a form does not hand out.
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
    record Part(String name, Type held, Method read) {

        /** This part of {@code form}. */
        Object of(Object form) {
            try {
                return read.invoke(form);
            } catch (ReflectiveOperationException e) {
                throw new IllegalStateException("a part that cannot be read: " + name, e);
            }
        }
    }

    /**
     * Whether a form of this shape hands its parts over.
     *
     * <p>How it is written and not what a crossing makes of it. A form the comparison passes over
     * is read through all the same — the walk that goes looking for the declarations a crossing
     * reaches has to go inside one to find what it holds — so what is asked here is whether there
     * are parts to read.
     */
    static boolean areHandedOver(Class<?> type) {
        return type.isRecord() || DeclarationAgreement.isANodeWrittenByHand(type);
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
        for (Field field : type.getDeclaredFields()) {
            if (Modifier.isStatic(field.getModifiers()) || field.isSynthetic()) {
                continue;
            }
            parts.add(new Part(field.getName(), field.getGenericType(), handsOver(type, field)));
        }
        parts.sort(Comparator.comparing(Part::name));
        return parts;
    }

    /**
     * The method a form hands one of its parts over by.
     *
     * <p>Held to what a record's accessor is, because the two readers here would otherwise come
     * apart again: what a part may hold is read off the field and what it does hold is read off the
     * method, so a method answering something else is a static reader and a walking reader looking
     * at two things — which is what reading parts in one place was for. A part written where it can
     * be set again is refused for the same reason, a form being compared for what it says now and
     * asked about for what it can ever say.
     */
    private static Method handsOver(Class<?> type, Field field) {
        String part = field.getName();
        if (!Modifier.isFinal(field.getModifiers())) {
            throw new IllegalStateException(type.getName() + " can write `" + part + "` again, so"
                    + " what it is made of is not what it was made of. Hold it as written once, or"
                    + " hold it somewhere this does not read.");
        }
        Method handedOver;
        try {
            handedOver = type.getMethod(part);
        } catch (NoSuchMethodException e) {
            throw new IllegalStateException(type.getName() + " holds `" + part + "` and hands it to"
                    + " nobody, so a comparison over what it is made of would pass it over without"
                    + " saying so. Hand it over, or hold it somewhere this does not read.", e);
        }
        if (!handedOver.getGenericReturnType().equals(field.getGenericType())) {
            throw new IllegalStateException(type.getName() + " hands `" + part + "` over as "
                    + handedOver.getGenericReturnType() + " and holds it as " + field.getGenericType()
                    + ", so what this walks and what it reads off the class are two things.");
        }
        return handedOver;
    }

}
