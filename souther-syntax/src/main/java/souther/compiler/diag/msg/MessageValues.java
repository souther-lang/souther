package souther.compiler.diag.msg;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.RecordComponent;
import java.util.LinkedHashMap;
import java.util.Map;

/** The values a {@link Message} carries, by the names its catalog entry writes them under. */
public final class MessageValues {

    private MessageValues() {
    }

    /** {@code message}'s components, in the order it declares them. */
    public static Map<String, Object> of(Message message) {
        Map<String, Object> values = new LinkedHashMap<>();
        for (RecordComponent component : message.getClass().getRecordComponents()) {
            values.put(component.getName(), read(component, message));
        }
        return values;
    }

    /** The names {@code message} carries, without reading any of them — what the build checks a
     * catalog entry against. */
    public static java.util.List<String> namesOf(Class<? extends Message> message) {
        java.util.List<String> names = new java.util.ArrayList<>();
        for (RecordComponent component : message.getRecordComponents()) {
            names.add(component.getName());
        }
        return names;
    }

    private static Object read(RecordComponent component, Message message) {
        try {
            return component.getAccessor().invoke(message);
        } catch (IllegalAccessException | InvocationTargetException e) {
            // A record's accessor is public and does nothing but answer a field, so this is a
            // message declared in a form that is not one — a fault of the compiler, not of the
            // source it was reporting on.
            throw new IllegalStateException(
                    "a message answers its own components, and " + message.getClass().getName()
                            + " did not answer `" + component.getName() + "`", e);
        }
    }
}
