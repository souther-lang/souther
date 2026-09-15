package souther.compiler.meta;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.RecordComponent;
import java.lang.reflect.Type;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

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

    /** Whether a form of this shape hands its parts over. */
    static boolean areHandedOver(Class<?> type) {
        return type.isRecord() || DeclarationAgreement.isAFormOfTheGrammar(type);
    }

    /**
     * Whether everything a value of this type keeps can be read off it.
     *
     * <p>A different question from {@link #areHandedOver}, which says whether this comparison takes
     * a value apart. This one says whether a reader could — what a value keeps and hands to nobody
     * is read by that value's own equality and by nothing here, so a reader asking what a value
     * depends on has to know when its answer is short rather than answer anyway.
     *
     * <p>Answered rather than thrown, because a caller asking this is asking to find out. The same
     * shape refused where the parts are read is the shape answered no here.
     */
    static boolean handsOverEverythingItKeeps(Class<?> type) {
        if (type.isRecord()) {
            return true;
        }
        for (Field field : kept(type)) {
            if (handedOver(type, field).whyNot() != null) {
                return false;
            }
        }
        return true;
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
        for (Field field : kept(type)) {
            parts.add(new Part(field.getName(), field.getGenericType(), handsOver(type, field)));
        }
        parts.sort(Comparator.comparing(Part::name));
        return parts;
    }

    /** What a form written by hand holds per value of it. */
    private static List<Field> kept(Class<?> type) {
        List<Field> kept = new ArrayList<>();
        for (Field field : type.getDeclaredFields()) {
            if (!Modifier.isStatic(field.getModifiers()) && !field.isSynthetic()) {
                kept.add(field);
            }
        }
        return kept;
    }

    /** The method a part is read off by, or why there is none. One of the two is null. */
    private record HandedOver(Method by, String whyNot) {}

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
        HandedOver read = handedOver(type, field);
        if (read.whyNot() != null) {
            throw new IllegalStateException(read.whyNot());
        }
        return read.by();
    }

    /**
     * Whether a part can be read off a form, and what is wrong where it cannot.
     *
     * <p>One reading, asked by the two callers that want different things of it: one reads the
     * parts and refuses a form that does not hand them all over, and one asks whether it would. Two
     * readings would let a form be refused by one and vouched for by the other.
     */
    private static HandedOver handedOver(Class<?> type, Field field) {
        String part = field.getName();
        if (!Modifier.isFinal(field.getModifiers())) {
            return new HandedOver(null, type.getName() + " can write `" + part + "` again, so what"
                    + " it is made of is not what it was made of. Hold it as written once, or hold"
                    + " it somewhere this does not read.");
        }
        Method handedOver;
        try {
            handedOver = type.getMethod(part);
        } catch (NoSuchMethodException _) {
            return new HandedOver(null, type.getName() + " holds `" + part + "` and hands it to"
                    + " nobody, so a comparison over what it is made of would pass it over without"
                    + " saying so. Hand it over, or hold it somewhere this does not read.");
        }
        if (!handedOver.getGenericReturnType().equals(field.getGenericType())) {
            return new HandedOver(null, type.getName() + " hands `" + part + "` over as "
                    + handedOver.getGenericReturnType() + " and holds it as "
                    + field.getGenericType()
                    + ", so what this walks and what it reads off the class are two things.");
        }
        return new HandedOver(handedOver, null);
    }

    /**
     * The types a part holds: itself, or what its container is of.
     *
     * <p>A container is read through rather than treated as a leaf, because what a reader of these
     * parts asks is about the values that arrive and a list of them is not one of those. What holds
     * no type a reader here can name — a type variable, a wildcard — holds nothing, and a reader
     * asking about it would be answering from the declaration site of something else.
     */
    static List<Class<?>> held(Type part) {
        if (part instanceof Class<?> plain) {
            return plain.isArray() ? List.of(plain.getComponentType()) : List.of(plain);
        }
        if (part instanceof ParameterizedType parameterized
                && parameterized.getRawType() instanceof Class<?> raw
                && (raw == List.class || raw == Set.class || raw == Optional.class
                        || raw == Map.class)) {
            List<Class<?>> of = new ArrayList<>();
            for (Type argument : parameterized.getActualTypeArguments()) {
                of.addAll(held(argument));
            }
            return of;
        }
        return List.of();
    }
}
