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
 * holds, which is the shape a record has and the one a form written by hand keeps. Nothing reaches
 * into what a form does not hand out.
 *
 * <p>Whether one does is what decides how it is compared, and a form that hands part of itself over
 * and keeps the rest is not half read: it is a form nothing here can take apart. A form of the
 * grammar is refused instead, being one the walk goes inside whatever it holds.
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
     * <p>Whether there is a representation to read, and not how the class happens to have been
     * written. A form keeping its whole state in final fields it hands out is one a reader can take
     * apart whatever the reason it was written as a class rather than as a record — and the reasons
     * are their own: a form whose construction is closed to everyone but the world that mints it is
     * written by hand for that, and nothing about it says how two of them are to be compared.
     *
     * <p>A form of the grammar is asked something else first. It is walked into whatever it holds,
     * so a part it keeps back is refused here rather than turning it into a form the walk stops at:
     * the tree's own kinds are compared part by part, and one of them quietly becoming a leaf is a
     * comparison left to whatever equality that form happens to have.
     */
    static boolean areHandedOver(Class<?> type) {
        if (type.isRecord()) {
            return true;
        }
        if (DeclarationAgreement.isAFormOfTheGrammar(type)) {
            refuseWhatIsKeptBack(type, inspect(type));
            return true;
        }
        // Nothing to read off one of these, whatever fields the platform wrote inside it: a case of
        // a closed set stands for itself, and an array and an interface are not a form at all.
        if (type.isInterface() || type.isEnum() || type.isArray() || type.isPrimitive()) {
            return false;
        }
        Inspection inspected = inspect(type);
        return inspected.keptBack().isEmpty() && !inspected.handedOver().isEmpty();
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
        Inspection inspected = inspect(type);
        refuseWhatIsKeptBack(type, inspected);
        List<Part> parts = new ArrayList<>(inspected.handedOver());
        parts.sort(Comparator.comparing(Part::name));
        return parts;
    }

    /**
     * What reading a class for parts found: the ones it hands over, and what it does with each of
     * the rest.
     *
     * <p>One reading, because the two callers here would otherwise come apart. Whether parts can be
     * read off a form decides how it is compared, and which parts those are is what the comparison
     * then walks; worked out twice, a form would be taken apart by one rule and chosen for by
     * another.
     */
    private record Inspection(List<Part> handedOver, List<String> keptBack) {}

    /**
     * What {@code type} hands over and what it keeps back.
     *
     * <p>A part is handed over by a final instance field with a no-argument method of the same name
     * answering the type the field holds, which is the shape a record has. Each of the three is what
     * it is for: what a part may hold is read off the field and what it does hold off the method, so
     * a method answering something else is the two readers looking at two things; and a field that
     * can be written again is a form compared for what it says now and asked about for what it can
     * ever say.
     */
    private static Inspection inspect(Class<?> type) {
        List<Part> handedOver = new ArrayList<>();
        List<String> keptBack = new ArrayList<>();
        for (Field field : type.getDeclaredFields()) {
            if (Modifier.isStatic(field.getModifiers()) || field.isSynthetic()) {
                continue;
            }
            String part = field.getName();
            if (!Modifier.isFinal(field.getModifiers())) {
                keptBack.add("can write `" + part + "` again, so what it is made of is not what it"
                        + " was made of. Hold it as written once, or hold it somewhere this does"
                        + " not read");
                continue;
            }
            Method reads;
            try {
                reads = type.getMethod(part);
            } catch (NoSuchMethodException e) {
                keptBack.add("holds `" + part + "` and hands it to nobody, so a comparison over what"
                        + " it is made of would pass it over without saying so. Hand it over, or"
                        + " hold it somewhere this does not read");
                continue;
            }
            if (!reads.getGenericReturnType().equals(field.getGenericType())) {
                keptBack.add("hands `" + part + "` over as " + reads.getGenericReturnType()
                        + " and holds it as " + field.getGenericType() + ", so what this walks and"
                        + " what it reads off the class are two things");
                continue;
            }
            handedOver.add(new Part(part, field.getGenericType(), reads));
        }
        return new Inspection(handedOver, keptBack);
    }

    /**
     * Refuses a form that keeps a part back where being read is not optional.
     *
     * <p>Asked of a form the walk goes inside — one of the grammar's own, and whatever else a reader
     * has already decided to take apart. A part nothing can read is a part a comparison would decide
     * without, and saying so where the reading happens is what keeps it from being decided by
     * nobody.
     */
    private static void refuseWhatIsKeptBack(Class<?> type, Inspection inspected) {
        if (!inspected.keptBack().isEmpty()) {
            throw new IllegalStateException(type.getName() + " " + inspected.keptBack().get(0) + ".");
        }
    }

}
