package souther.raoh;

import net.unit8.raoh.ErrorCodes;
import net.unit8.raoh.Issue;
import net.unit8.raoh.Issues;
import net.unit8.raoh.MessageKeys;
import net.unit8.raoh.Path;
import net.unit8.raoh.Result;
import org.jooq.Record;
import org.jspecify.annotations.Nullable;
import souther.runtime.boundary.Decoder;
import souther.runtime.boundary.Refusal;
import souther.runtime.boundary.Refusals;
import souther.runtime.boundary.TreeReader;
import tools.jackson.databind.JsonNode;

import java.math.BigDecimal;
import java.util.HashMap;
import java.util.Locale;
import java.util.Map;

/**
 * The Raoh decoder binding (spec {@code [#raoh-binding]}): a derived decoder presented as a Raoh
 * decoder, reading a {@code Map}, a Jackson {@code JsonNode} or a jOOQ {@code Record}, and its
 * refusals reported as Raoh issues.
 *
 * <p>It decides nothing. A decode answers the same value or the same refusals through it as without
 * it; what it adds is the vocabulary a {@code MessageResolver} keyed on Raoh's codes reads.
 */
public final class RaohBinding {

    private RaohBinding() {}

    /** A derived decoder as a Raoh decoder of maps, lists and the JDK's values. */
    public static <T> net.unit8.raoh.decode.Decoder<Object, T> decoder(Decoder<T> derived) {
        return through(derived, TreeReader.PLAIN);
    }

    /** A derived decoder as a Raoh decoder of a Jackson {@code JsonNode}. */
    public static <T> net.unit8.raoh.decode.Decoder<JsonNode, T> jsonDecoder(Decoder<T> derived) {
        return through(derived, JsonNodeReader.INSTANCE);
    }

    /** A derived decoder as a Raoh decoder of a jOOQ {@code Record}, read as an object of its
     *  columns. */
    public static <T> net.unit8.raoh.decode.Decoder<Record, T> recordDecoder(Decoder<T> derived) {
        return through(derived, RecordReader.INSTANCE);
    }

    private static <I, T> net.unit8.raoh.decode.Decoder<I, T> through(Decoder<T> derived, TreeReader reader) {
        return (in, path) -> switch (derived.decode(in, reader)) {
            case souther.runtime.Result.Ok<T, Refusals>(T value) -> Result.ok(value);
            case souther.runtime.Result.Err<T, Refusals>(Refusals refusals) -> Result.err(issues(refusals, path));
        };
    }

    /** The refusals of a decode as Raoh issues, each at its path under {@code base}. */
    public static Issues issues(Refusals refusals, Path base) {
        Issues out = Issues.EMPTY;
        for (Refusal refusal : refusals.asList()) {
            out = out.add(issue(refusal, base));
        }
        return out;
    }

    private static Issue issue(Refusal refusal, Path base) {
        Path at = base;
        // Raoh's path is the text of each step, as a JSON Pointer writes it
        for (souther.runtime.boundary.Path.Segment segment : refusal.path().segments()) {
            at = at.append(segment.text());
        }
        return switch (refusal) {
            case Refusal.Absent _ -> Issue.of(at, ErrorCodes.REQUIRED, "is required", Map.of());
            case Refusal.NotOfItsKind r -> notOfItsKind(at, r);
            case Refusal.NotOneOfTheNames r -> Issue.of(at, ErrorCodes.NOT_ALLOWED,
                    "must be one of " + r.names(), Map.of("allowed", r.names(), "actual", r.written()));
            case Refusal.NotInItsForm r -> Issue.of(at, ErrorCodes.INVALID_FORMAT, r.reason(), Map.of());
            case Refusal.OneKeyTwice _ -> Issue.of(at, "duplicate_key",
                    "two keys are the same key once decoded", Map.of());
            case Refusal.Constraint r -> constraint(at, r);
            case Refusal.Clause r -> Issue.of(at, "invariant_violation", r.failure().toString(),
                    r.failure().meta());
        };
    }

    private static Issue notOfItsKind(Path at, Refusal.NotOfItsKind r) {
        Map<String, Object> meta = new HashMap<>();
        meta.put("expected", r.expected());
        if (r.found() != null) {
            meta.put("actual", r.found());
        }
        String key = r.found() == null ? MessageKeys.TYPE_MISMATCH_NUMERIC_RANGE
                : r.expected().equals("object with string keys") ? MessageKeys.TYPE_MISMATCH_STRING_KEYS
                : ErrorCodes.TYPE_MISMATCH;
        return Issue.of(at, ErrorCodes.TYPE_MISMATCH, key, r.reason(), meta);
    }

    /**
     * A constraint as the Raoh constraint that states it: its code, message key, metadata and
     * default message. One it does not know is reported under {@code invalid_value} with the
     * constraint's name as the message key and its data as the metadata, so a constraint the
     * language adds is still reported, and told apart, before this binding knows it.
     */
    private static Issue constraint(Path at, Refusal.Constraint r) {
        Map<String, Object> d = r.data();
        Object actual = d.get("actual");
        return switch (r.name()) {
            case "minLength" -> Issue.of(at, ErrorCodes.TOO_SHORT,
                    format("must be at least %s characters", d.get("min")), d);
            case "maxLength" -> Issue.of(at, ErrorCodes.TOO_LONG,
                    format("must be at most %s characters", d.get("max")), d);
            case "length" -> Issue.of(at, ErrorCodes.INVALID_LENGTH,
                    format("must be exactly %s characters", d.get("length")),
                    Map.of("expected", d.get("length"), "actual", actual));
            case "pattern" -> Issue.of(at, ErrorCodes.INVALID_FORMAT, "invalid format", d);
            case "min" -> Issue.of(at, ErrorCodes.OUT_OF_RANGE, MessageKeys.OUT_OF_RANGE_MINIMUM,
                    format("must be at least %s", d.get("min")), d);
            case "max" -> Issue.of(at, ErrorCodes.OUT_OF_RANGE, MessageKeys.OUT_OF_RANGE_MAXIMUM,
                    format("must be at most %s", d.get("max")), d);
            case "positive" -> Issue.of(at, ErrorCodes.OUT_OF_RANGE, MessageKeys.OUT_OF_RANGE_POSITIVE,
                    "must be positive",
                    Map.of("min", actual instanceof BigDecimal ? BigDecimal.ZERO : 1L, "actual", actual));
            case "nonNegative" -> Issue.of(at, ErrorCodes.OUT_OF_RANGE, MessageKeys.OUT_OF_RANGE_NON_NEGATIVE,
                    "must be non-negative",
                    Map.of("min", actual instanceof BigDecimal ? BigDecimal.ZERO : 0L, "actual", actual));
            case "nonEmpty" -> Issue.of(at, ErrorCodes.TOO_SMALL, MessageKeys.TOO_SMALL_NONEMPTY,
                    "must not be empty", d);
            case "minSize" -> Issue.of(at, ErrorCodes.TOO_SMALL,
                    format("must have at least %s elements", d.get("min")), d);
            case "maxSize" -> Issue.of(at, ErrorCodes.TOO_BIG,
                    format("must have at most %s elements", d.get("max")), d);
            case "size" -> Issue.of(at, ErrorCodes.INVALID_SIZE,
                    format("must have exactly %s elements", d.get("size")),
                    Map.of("expected", d.get("size"), "actual", actual));
            case "unique" -> Issue.of(at, ErrorCodes.DUPLICATE_ELEMENT,
                    "must not contain duplicates: " + d.get("duplicates"), d);
            default -> Issue.of(at, ErrorCodes.INVALID_VALUE, r.name(), r.name() + " " + d, d);
        };
    }

    private static String format(String template, @Nullable Object value) {
        return String.format(Locale.ROOT, template, value);
    }

    /** The reader of a Jackson {@code JsonNode} tree. */
    public static TreeReader jsonReader() {
        return JsonNodeReader.INSTANCE;
    }

    /** The reader of a jOOQ {@code Record}, as an object of its columns. */
    public static TreeReader recordReader() {
        return RecordReader.INSTANCE;
    }
}
