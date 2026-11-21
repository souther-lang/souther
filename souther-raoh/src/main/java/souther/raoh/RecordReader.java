package souther.raoh;

import org.jooq.Field;
import org.jooq.Record;
import org.jspecify.annotations.Nullable;
import souther.runtime.boundary.TreeReader;

import java.util.AbstractMap;
import java.util.Arrays;
import java.util.Map;

/**
 * The reader of a jOOQ {@code Record}, as an object of its columns: a field reads the column of its
 * name, and a column is read as the value it holds. A column holds no object, so a field whose type
 * is one is refused at that field as not of its kind. A {@code java.sql} date or time a column holds
 * is handed over as it is, and refused by the decoder (spec {@code [#codec-generation]}).
 */
final class RecordReader implements TreeReader {

    static final RecordReader INSTANCE = new RecordReader();

    private RecordReader() {}

    @Override
    public Shape shapeOf(Object node) {
        return node instanceof Record ? Shape.OBJECT : PLAIN.shapeOf(node);
    }

    @Override
    public @Nullable Object member(Object object, String name) {
        if (!(object instanceof Record record)) {
            return PLAIN.member(object, name);
        }
        Field<?> field = record.field(name);
        return field == null ? null : record.get(field);
    }

    @Override
    public Iterable<? extends Map.Entry<?, ?>> members(Object object) {
        if (!(object instanceof Record record)) {
            return PLAIN.members(object);
        }
        return () -> Arrays.stream(record.fields())
                .<Map.Entry<?, ?>>map(field ->
                        new AbstractMap.SimpleImmutableEntry<>(field.getName(), record.get(field)))
                .iterator();
    }

    @Override
    public Iterable<?> elements(Object array) {
        return PLAIN.elements(array);
    }

    @Override
    public Object scalar(Object node) {
        return node;
    }

    @Override
    public String describe(Object node) {
        return node instanceof Record ? "record" : PLAIN.describe(node);
    }
}
