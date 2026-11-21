package souther.runtime.boundary;

import org.jspecify.annotations.Nullable;
import souther.runtime.BoundaryScalars;
import souther.runtime.InvariantFailure;
import souther.runtime.Lists;
import souther.runtime.Option;
import souther.runtime.PersistentVector;
import souther.runtime.Result;
import souther.runtime.Sets;
import souther.runtime.Strings;
import souther.runtime.Temporals;
import souther.runtime.TextAdmission;
import souther.temporal.TemporalForms;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.time.Instant;
import java.time.LocalDate;
import java.time.LocalDateTime;
import java.time.LocalTime;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;

/**
 * The parts a derived decoder is generated from (spec {@code [#decoder-derivation]},
 * {@code [#codec-generation]}). Generated code calls these; they are not a library for writing
 * decoders by hand, which is done over the derived ones (spec {@code [#custom-codec]}).
 *
 * <p>Everything a decode decides is decided here or in the generated code that calls it: which
 * carrier is read as which scalar, which text is in a form, which name is a case, which constraint
 * a value breaks. The {@link TreeReader} a decode is handed only says what the tree holds.
 */
public final class Decoding {

    /** What a string's half of a surrogate pair is said as. */
    public static final String HALF_A_PAIR = "holds half of a surrogate pair, which is not a character";

    /** What text whose canonical value is longer than a {@code String} holds is said as. */
    public static final String NO_PLACE = "is longer than a String holds once canonicalized";

    private Decoding() {}

    /** The one refusal, as what a decode answers. */
    public static <T> Result<T, Refusals> refuse(Refusal refusal) {
        return Result.err(Refusals.of(refusal));
    }

    /** {@code more} after what was refused so far, which is null where nothing was. */
    public static Refusals and(@Nullable Refusals soFar, Refusals more) {
        return soFar == null ? more : soFar.and(more);
    }

    /** A construction's failure at {@code path}, as the clause it names: what a decode answers where
     *  the value it read breaks a clause the decoder did not check before constructing. */
    public static <T> Result<T, Refusals> refusedBy(InvariantFailure failure, Path path) {
        return refuse(new Refusal.Clause(path, failure));
    }

    // --- what a node is

    /**
     * The refusal of a node that is not an object, or null where it is one. A product and a sum are
     * read as an object, and a node of another shape is one fact about one node, refused at it,
     * rather than one refusal for each field it was asked for.
     */
    public static @Nullable Refusals notAnObject(@Nullable Object node, Path path, TreeReader reader) {
        if (node == null || reader.shapeOf(node) == TreeReader.Shape.NULL) {
            return Refusals.of(new Refusal.Absent(path));
        }
        if (reader.shapeOf(node) != TreeReader.Shape.OBJECT) {
            return Refusals.of(mismatch(path, "object", reader.describe(node)));
        }
        return null;
    }

    private static boolean isAbsent(@Nullable Object node, TreeReader reader) {
        return node == null || reader.shapeOf(node) == TreeReader.Shape.NULL;
    }

    private static Refusal.NotOfItsKind mismatch(Path path, String expected, @Nullable String found) {
        return new Refusal.NotOfItsKind(path, expected, found, "expected " + expected);
    }

    /** The scalar a node holds, or the refusal of a node that holds none: absent, or an object or an
     *  array where a scalar stands. */
    private static Result<Object, Refusals> scalarOf(@Nullable Object node, Path path, TreeReader reader,
                                                     String expected) {
        if (node == null || isAbsent(node, reader)) {
            return refuse(new Refusal.Absent(path));
        }
        if (reader.shapeOf(node) != TreeReader.Shape.SCALAR) {
            return refuse(mismatch(path, expected, reader.describe(node)));
        }
        return Result.ok(reader.scalar(node));
    }

    // --- scalars

    /** A {@code String}: text, canonical, and within what a {@code String} holds (spec
     *  {@code [#string-canonical]}, {@code [#what-a-string-holds]}). */
    public static Decoder<String> string() {
        return (node, path, reader) -> switch (scalarOf(node, path, reader, "string")) {
            case Result.Err<Object, Refusals>(Refusals r) -> Result.err(r);
            case Result.Ok<Object, Refusals>(Object value) -> value instanceof String text
                    ? text(text, path)
                    : refuse(mismatch(path, "string", value.getClass().getSimpleName()));
        };
    }

    private static Result<String, Refusals> text(String text, Path path) {
        return switch (Strings.admission(text)) {
            case TextAdmission.Admitted a -> Result.ok(a.text());
            case TextAdmission.NotText _ -> refuse(new Refusal.NotInItsForm(path, "text", HALF_A_PAIR));
            case TextAdmission.NoPlace _ -> refuse(new Refusal.NotInItsForm(path, "text", NO_PLACE));
        };
    }

    /** An {@code Int}: from an integer representation within 64 bits, and nothing else (spec
     *  {@code [#a-boundary-scalar-is-read-not-converted]}). */
    public static Decoder<Long> integer() {
        return (node, path, reader) -> switch (scalarOf(node, path, reader, "long")) {
            case Result.Err<Object, Refusals>(Refusals r) -> Result.err(r);
            case Result.Ok<Object, Refusals>(Object value) -> integer(value, path);
        };
    }

    private static Result<Long, Refusals> integer(Object value, Path path) {
        String refused = BoundaryScalars.intRefusal(value);
        if (refused != null) {
            return refuse(new Refusal.NotOfItsKind(path, "integer", value.getClass().getSimpleName(),
                    refused));
        }
        return switch (value) {
            case Long l -> Result.ok(l);
            case Integer i -> Result.ok((long) i);
            case Short s -> Result.ok((long) s);
            case Byte b -> Result.ok((long) b);
            case BigInteger bi when bi.getClass() == BigInteger.class -> within64Bits(bi, path);
            // scale 0, the refusal above having taken every other: the digits are the integer
            case BigDecimal bd when bd.getClass() == BigDecimal.class -> within64Bits(bd.unscaledValue(), path);
            default -> refuse(mismatch(path, "long", value.getClass().getSimpleName()));
        };
    }

    private static Result<Long, Refusals> within64Bits(BigInteger value, Path path) {
        return value.bitLength() < Long.SIZE
                ? Result.ok(value.longValue())
                : refuse(new Refusal.NotOfItsKind(path, "long", null, "value is outside the long range"));
    }

    /** A {@code Decimal}: from an exact number. A {@code double} or a {@code float} may have been
     *  rounded before it arrived, and is refused. */
    public static Decoder<BigDecimal> decimal() {
        return (node, path, reader) -> switch (scalarOf(node, path, reader, "number")) {
            case Result.Err<Object, Refusals>(Refusals r) -> Result.err(r);
            case Result.Ok<Object, Refusals>(Object value) -> decimal(value, path);
        };
    }

    private static Result<BigDecimal, Refusals> decimal(Object value, Path path) {
        String refused = BoundaryScalars.decimalRefusal(value);
        if (refused != null) {
            return refuse(new Refusal.NotOfItsKind(path, "exact number",
                    value.getClass().getSimpleName(), refused));
        }
        BigDecimal number = switch (value) {
            case BigDecimal v when v.getClass() == BigDecimal.class -> v;
            case BigInteger bi when bi.getClass() == BigInteger.class -> new BigDecimal(bi);
            case Long l -> BigDecimal.valueOf(l);
            case Integer i -> BigDecimal.valueOf(i);
            case Short s -> BigDecimal.valueOf(s);
            case Byte b -> BigDecimal.valueOf(b);
            default -> null;
        };
        return number == null
                ? refuse(mismatch(path, "number", value.getClass().getSimpleName()))
                : Result.ok(number);
    }

    /** A {@code Bool}. */
    public static Decoder<Boolean> bool() {
        return (node, path, reader) -> switch (scalarOf(node, path, reader, "boolean")) {
            case Result.Err<Object, Refusals>(Refusals r) -> Result.err(r);
            case Result.Ok<Object, Refusals>(Object value) -> value instanceof Boolean b
                    ? Result.ok(b)
                    : refuse(mismatch(path, "boolean", value.getClass().getSimpleName()));
        };
    }

    /** A {@code Date}: a {@code LocalDate}, or its text (spec {@code [#temporal-text]}). */
    public static Decoder<LocalDate> date() {
        return temporal(TemporalForms.Kind.DATE, "date", "date", LocalDate.class, LocalDate::parse);
    }

    /** A {@code Time}: a {@code LocalTime}, or its text, held to the second. */
    public static Decoder<LocalTime> time() {
        return temporal(TemporalForms.Kind.TIME, "time", "time", LocalTime.class, LocalTime::parse);
    }

    /** A {@code DateTime}: a {@code LocalDateTime}, or its text, held to the second. */
    public static Decoder<LocalDateTime> dateTime() {
        return temporal(TemporalForms.Kind.DATETIME, "dateTime", "date-time", LocalDateTime.class,
                LocalDateTime::parse);
    }

    /** An {@code Instant}: a {@code java.time.Instant}, or its text with an offset. The text may name
     *  the end of a day as hour 24, which is the next day's start; {@code Instant.parse} reads that
     *  where an {@code OffsetDateTime} refuses it. */
    public static Decoder<Instant> instant() {
        return temporal(TemporalForms.Kind.INSTANT, "instant", "instant", Instant.class,
                Instant::parse);
    }

    private static <T> Decoder<T> temporal(TemporalForms.Kind kind, String form, String expected,
                                           Class<T> carrier, Function<String, T> parse) {
        return (node, path, reader) -> switch (scalarOf(node, path, reader, expected)) {
            case Result.Err<Object, Refusals>(Refusals r) -> Result.err(r);
            case Result.Ok<Object, Refusals>(Object value) -> {
                if (value instanceof String text) {
                    String refused = TemporalForms.atBoundary(kind, text)
                            .map(why -> TemporalForms.says(kind, why)).orElse(null);
                    yield refused != null
                            ? refuse(new Refusal.NotInItsForm(path, form, refused))
                            : Result.ok(parse.apply(text));
                }
                if (!carrier.isInstance(value)) {
                    yield refuse(mismatch(path, expected, value.getClass().getSimpleName()));
                }
                yield Temporals.toTheSecond(value)
                        ? Result.ok(carrier.cast(value))
                        : refuse(new Refusal.NotInItsForm(path, form,
                                TemporalForms.says(kind, TemporalForms.Refusal.SUB_SECOND)));
            }
        };
    }

    // --- positions

    /** What is under the member {@code key} of an object, which must be there. The node is an object:
     *  the decoder of the object has asked ({@link #notAnObject}). */
    public static <T> Decoder<T> field(String key, Decoder<T> dec) {
        return (node, path, reader) -> {
            Path at = path.append(key);
            Object member = node == null ? null : reader.member(node, key);
            return isAbsent(member, reader) ? refuse(new Refusal.Absent(at)) : dec.decode(member, at, reader);
        };
    }

    /** What is under the member {@code key}, or none where the key is missing or holds null. */
    public static <T> Decoder<Option<T>> optionalField(String key, Decoder<T> dec) {
        return (node, path, reader) -> {
            Object member = node == null ? null : reader.member(node, key);
            return isAbsent(member, reader)
                    ? Result.ok(Option.none())
                    : dec.decode(member, path.append(key), reader).map(Option::some);
        };
    }

    /** An optional where there is no key to be missing — an element, a map's value: null is the whole
     *  of what absence is there (spec {@code [#absence-is-written-as-null]}). */
    public static <T> Decoder<Option<T>> nullable(Decoder<T> dec) {
        return (node, path, reader) -> isAbsent(node, reader)
                ? Result.ok(Option.none())
                : dec.decode(node, path, reader).map(Option::some);
    }

    /** A list, every element read by {@code element} and every element's refusals kept. */
    public static <T> Decoder<List<T>> list(Decoder<T> element) {
        return (node, path, reader) -> {
            if (node == null || isAbsent(node, reader)) {
                return refuse(new Refusal.Absent(path));
            }
            if (reader.shapeOf(node) != TreeReader.Shape.ARRAY) {
                return refuse(mismatch(path, "array", reader.describe(node)));
            }
            List<Object> out = Lists.builder();
            Refusals refused = null;
            int index = 0;
            for (Object each : reader.elements(node)) {
                switch (element.decode(each, path.append(index++), reader)) {
                    case Result.Ok<T, Refusals>(T value) -> out.add(value);
                    case Result.Err<T, Refusals>(Refusals r) -> refused = refused == null ? r : refused.and(r);
                }
            }
            @SuppressWarnings("unchecked")   // every element added was a T
            List<T> read = (List<T>) (List<?>) Lists.sealed(out);
            return refused != null ? Result.err(refused) : Result.ok(read);
        };
    }

    /** An object read as a map from its member names, every value read by {@code value}. A key that
     *  is not a string is refused at the object (spec {@code [#an-object-is-a-mapping]}). */
    public static <V> Decoder<Map<String, V>> map(Decoder<V> value) {
        return (node, path, reader) -> {
            if (node == null || isAbsent(node, reader)) {
                return refuse(new Refusal.Absent(path));
            }
            if (reader.shapeOf(node) != TreeReader.Shape.OBJECT) {
                return refuse(mismatch(path, "object", reader.describe(node)));
            }
            Iterable<? extends Map.Entry<?, ?>> members = reader.members(node);
            for (Map.Entry<?, ?> member : members) {
                if (!(member.getKey() instanceof String)) {
                    String keyType = member.getKey() == null ? "null" : member.getKey().getClass().getSimpleName();
                    return refuse(new Refusal.NotOfItsKind(path, "object with string keys", keyType,
                            "expected object with string keys, found " + keyType + " key"));
                }
            }
            Map<String, V> out = new LinkedHashMap<>();
            Refusals refused = null;
            for (Map.Entry<?, ?> member : members) {
                String key = (String) member.getKey();
                switch (value.decode(member.getValue(), path.append(key), reader)) {
                    case Result.Ok<V, Refusals>(V v) -> out.put(key, v);
                    case Result.Err<V, Refusals>(Refusals r) -> refused = refused == null ? r : refused.and(r);
                }
            }
            return refused != null ? Result.err(refused) : Result.ok(Collections.unmodifiableMap(out));
        };
    }

    /**
     * The step that reads the keys of a map whose values are read: each key read by {@code key} as
     * the text it is, at its own path. Two keys that are one once read are refused at the second
     * rather than one of their values kept in place of the other.
     */
    public static <K, V> Decoder.Step<Map<String, V>, Map<K, V>> keys(Decoder<K> key) {
        return (map, path) -> {
            Map<K, V> out = new LinkedHashMap<>();
            Refusals refused = null;
            for (Map.Entry<String, V> entry : map.entrySet()) {
                Path at = path.append(entry.getKey());
                switch (key.decode(entry.getKey(), at, TreeReader.PLAIN)) {
                    case Result.Err<K, Refusals>(Refusals r) -> refused = refused == null ? r : refused.and(r);
                    case Result.Ok<K, Refusals>(K k) -> {
                        if (out.containsKey(k)) {
                            Refusals twice = Refusals.of(new Refusal.OneKeyTwice(at));
                            refused = refused == null ? twice : refused.and(twice);
                        } else {
                            out.put(k, entry.getValue());
                        }
                    }
                }
            }
            return refused != null ? Result.err(refused) : Result.ok(out);
        };
    }

    // --- sums

    /**
     * A sum's dispatch: the object's member {@code key} read as a tag, and the object handed to the
     * decoder of the case that tag names (spec {@code [#sum-discrimination]}). A tag no case answers
     * to is refused at the tag, carrying the case names in code point order.
     */
    @SuppressWarnings("unchecked")
    public static <T> Decoder<T> discriminate(String key, String[] tags, Decoder<?>[] cases) {
        Map<String, Decoder<?>> byTag = new LinkedHashMap<>();
        for (int i = 0; i < tags.length; i++) {
            byTag.put(tags[i], cases[i]);
        }
        List<String> names = inCodePointOrder(byTag.keySet());
        Decoder<String> tag = field(key, string());
        return (node, path, reader) -> {
            Refusals shape = notAnObject(node, path, reader);
            if (shape != null) {
                return Result.err(shape);
            }
            return switch (tag.decode(node, path, reader)) {
                case Result.Err<String, Refusals>(Refusals r) -> Result.err(r);
                case Result.Ok<String, Refusals>(String written) -> {
                    Decoder<?> dec = byTag.get(written);
                    yield dec == null
                            ? refuse(new Refusal.NotOneOfTheNames(path.append(key), names, written))
                            : (Result<T, Refusals>) dec.decode(node, path, reader);
                }
            };
        };
    }

    /** An enumeration's name: text, one of {@code names}, compared exactly, case and all. */
    public static Decoder<String> oneOf(String... names) {
        Set<String> allowed = Set.of(names);
        List<String> sorted = inCodePointOrder(allowed);
        return string().then((written, path) -> allowed.contains(written)
                ? Result.ok(written)
                : refuse(new Refusal.NotOneOfTheNames(path, sorted, written)));
    }

    private static List<String> inCodePointOrder(Set<String> names) {
        return Lists.sort((a, b) -> compareCodePoints((String) a, (String) b),
                PersistentVector.from(names));
    }

    private static int compareCodePoints(String a, String b) {
        int i = 0;
        int j = 0;
        while (i < a.length() && j < b.length()) {
            int ca = a.codePointAt(i);
            int cb = b.codePointAt(j);
            if (ca != cb) {
                return Integer.compare(ca, cb);
            }
            i += Character.charCount(ca);
            j += Character.charCount(cb);
        }
        return Integer.compare(a.length() - i, b.length() - j);
    }

    // --- a newtype's clauses (spec [#what-an-invariant-refusal-says])

    /** A clause stated as no constraint: the value refused as the clause, carrying {@code failure}. */
    public static <T> Decoder<T> clause(Decoder<T> dec, Predicate<? super T> holds, InvariantFailure failure) {
        return dec.then((value, path) -> holds.test(value)
                ? Result.ok(value)
                : refuse(new Refusal.Clause(path, failure)));
    }

    private static <T> Decoder<T> constraint(Decoder<T> dec, Predicate<? super T> holds, String name,
                                             Function<? super T, Map<String, Object>> data) {
        return dec.then((value, path) -> holds.test(value)
                ? Result.ok(value)
                : refuse(new Refusal.Constraint(path, name, data.apply(value))));
    }

    /** A constraint's data, in the order the constraint states it: its bound first, then what the
     *  value was found to be (spec {@code [#what-an-invariant-refusal-says]}). */
    private static Map<String, Object> stated(String name, Object value) {
        Map<String, Object> data = new LinkedHashMap<>();
        data.put(name, value);
        return data;
    }

    private static Map<String, Object> stated(String bound, Object limit, String found, Object actual) {
        Map<String, Object> data = stated(bound, limit);
        data.put(found, actual);
        return data;
    }

    private static int codePoints(String s) {
        return s.codePointCount(0, s.length());
    }

    /** At least {@code n} characters. */
    public static Decoder<String> minLength(Decoder<String> dec, int n) {
        return constraint(dec, s -> codePoints(s) >= n, "minLength",
                s -> stated("min", n, "actual", codePoints(s)));
    }

    /** At most {@code n} characters. */
    public static Decoder<String> maxLength(Decoder<String> dec, int n) {
        return constraint(dec, s -> codePoints(s) <= n, "maxLength",
                s -> stated("max", n, "actual", codePoints(s)));
    }

    /** Exactly {@code n} characters. */
    public static Decoder<String> length(Decoder<String> dec, int n) {
        return constraint(dec, s -> codePoints(s) == n, "length",
                s -> stated("length", n, "actual", codePoints(s)));
    }

    /** The whole string matches the pattern {@code written}, run as {@code machine}. */
    public static Decoder<String> pattern(Decoder<String> dec, Predicate<String> machine, String written) {
        return constraint(dec, machine, "pattern", s -> stated("pattern", written));
    }

    /** An {@code Int} at least {@code n}. */
    public static Decoder<Long> min(Decoder<Long> dec, long n) {
        return constraint(dec, v -> v >= n, "min", v -> stated("min", n, "actual", v));
    }

    /** An {@code Int} at most {@code n}. */
    public static Decoder<Long> max(Decoder<Long> dec, long n) {
        return constraint(dec, v -> v <= n, "max", v -> stated("max", n, "actual", v));
    }

    /** An {@code Int} above nought. */
    public static Decoder<Long> positive(Decoder<Long> dec) {
        return constraint(dec, v -> v > 0, "positive", v -> stated("actual", v));
    }

    /** An {@code Int} not below nought. */
    public static Decoder<Long> nonNegative(Decoder<Long> dec) {
        return constraint(dec, v -> v >= 0, "nonNegative", v -> stated("actual", v));
    }

    /** A {@code Decimal} at least {@code n}. */
    public static Decoder<BigDecimal> decimalMin(Decoder<BigDecimal> dec, BigDecimal n) {
        return constraint(dec, v -> v.compareTo(n) >= 0, "min", v -> stated("min", n, "actual", v));
    }

    /** A {@code Decimal} at most {@code n}. */
    public static Decoder<BigDecimal> decimalMax(Decoder<BigDecimal> dec, BigDecimal n) {
        return constraint(dec, v -> v.compareTo(n) <= 0, "max", v -> stated("max", n, "actual", v));
    }

    /** A {@code Decimal} above nought. */
    public static Decoder<BigDecimal> decimalPositive(Decoder<BigDecimal> dec) {
        return constraint(dec, v -> v.signum() > 0, "positive", v -> stated("actual", v));
    }

    /** A {@code Decimal} not below nought. */
    public static Decoder<BigDecimal> decimalNonNegative(Decoder<BigDecimal> dec) {
        return constraint(dec, v -> v.signum() >= 0, "nonNegative", v -> stated("actual", v));
    }

    /** At least one element or entry. */
    public static <C> Decoder<C> nonEmpty(Decoder<C> dec) {
        return constraint(dec, c -> size(c) >= 1, "nonEmpty", c -> stated("min", 1, "actual", size(c)));
    }

    /** At least {@code n} elements or entries. */
    public static <C> Decoder<C> minSize(Decoder<C> dec, int n) {
        return constraint(dec, c -> size(c) >= n, "minSize", c -> stated("min", n, "actual", size(c)));
    }

    /** At most {@code n} elements or entries. */
    public static <C> Decoder<C> maxSize(Decoder<C> dec, int n) {
        return constraint(dec, c -> size(c) <= n, "maxSize", c -> stated("max", n, "actual", size(c)));
    }

    /** Exactly {@code n} elements. */
    public static <C> Decoder<C> size(Decoder<C> dec, int n) {
        return constraint(dec, c -> size(c) == n, "size", c -> stated("size", n, "actual", size(c)));
    }

    /**
     * No element twice, compared as the language compares. Each element found repeated is carried
     * once, in the order its repetition was found, in the form {@code form} writes it, which is a scalar form (spec
     * {@code [#what-an-invariant-refusal-says]}).
     */
    public static <T> Decoder<List<T>> unique(Decoder<List<T>> dec, Function<? super T, Object> form) {
        return dec.then((list, path) -> {
            List<T> repeated = Sets.repeated(list);
            if (repeated.isEmpty()) {
                return Result.ok(list);
            }
            List<Object> duplicates = Lists.builder();
            for (T element : repeated) {
                duplicates.add(form.apply(element));
            }
            return refuse(new Refusal.Constraint(path, "unique",
                    stated("duplicates", Lists.sealed(duplicates))));
        });
    }

    private static int size(Object collection) {
        return switch (collection) {
            case Collection<?> c -> c.size();
            case Map<?, ?> m -> m.size();
            default -> throw new IllegalArgumentException("not a collection: " + collection.getClass());
        };
    }
}
