package souther.runtime.boundary;

import org.jspecify.annotations.Nullable;

import java.math.BigDecimal;
import java.time.Instant;
import java.time.LocalDate;
import java.time.LocalDateTime;
import java.time.LocalTime;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * The parts a derived encoder is generated from (spec {@code [#encoder-derivation]}): a scalar
 * written as itself or as its text, and a list and a map written member by member. Generated code
 * calls these.
 */
public final class Encoding {

    private Encoding() {}

    /** A {@code String}, as itself. */
    public static Encoder<String, Object> string() {
        return v -> v;
    }

    /** An {@code Int}, as itself. */
    public static Encoder<Long, Object> integer() {
        return v -> v;
    }

    /** A {@code Bool}, as itself. */
    public static Encoder<Boolean, Object> bool() {
        return v -> v;
    }

    /** A {@code Decimal}, as itself. */
    public static Encoder<BigDecimal, Object> decimal() {
        return v -> v;
    }

    /** A {@code Date}, as its text. */
    public static Encoder<LocalDate, Object> date() {
        return LocalDate::toString;
    }

    /** A {@code Time}, as its text. */
    public static Encoder<LocalTime, Object> time() {
        return LocalTime::toString;
    }

    /** A {@code DateTime}, as its text. */
    public static Encoder<LocalDateTime, Object> dateTime() {
        return LocalDateTime::toString;
    }

    /** An {@code Instant}, as its text. */
    public static Encoder<Instant, Object> instant() {
        return Instant::toString;
    }

    /** A list, each element written by {@code element}. */
    public static <T> Encoder<List<T>, Object> list(Encoder<T, Object> element) {
        return values -> written(values, element);
    }

    /**
     * {@code values} in their external form: a host list, because an absent element is written as
     * {@code null} where it stands (spec {@code [#collections]}), which no {@code List} of the
     * language holds.
     */
    private static <T> List<@Nullable Object> written(List<T> values, Encoder<T, Object> element) {
        List<@Nullable Object> out = new ArrayList<>(values.size());
        for (T value : values) {
            out.add(element.encode(value));
        }
        return Collections.unmodifiableList(out);
    }

    /** A map with text keys, each value written by {@code value}. */
    public static <V> Encoder<Map<String, V>, Object> map(Encoder<V, Object> value) {
        return values -> {
            Map<String, Object> out = LinkedHashMap.newLinkedHashMap(values.size());
            values.forEach((key, v) -> out.put(key, value.encode(v)));
            return out;
        };
    }
}
