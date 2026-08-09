package souther.compiler.observe;

import souther.compiler.types.TypeName;

import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * A value an {@code example} row handed a behavior, in a form the compiler owns.
 *
 * <p>A row's input is built by running the derived decoder, so what comes back is an instance of a
 * class the {@code MemoryClassLoader} defined for this compile. Keeping that instance is what a query
 * answer must not do: the answer is memoised, so it would hold the loader, and the loader holds every
 * generated class of that revision. In a language server, where a revision arrives on every save, the
 * classes of every previous revision would stay reachable through the answers that named them.
 *
 * <p>So the decoded value is read once, here, into records that name types by {@link TypeName} and
 * hold nothing that came from the generated classes. It is bounded as well as owned ({@link Limits}):
 * taking the value out of its loader does not make it small, and an answer that keeps a ten-thousand
 * element list keeps it for as long as it is memoised.
 *
 * <p>Being a record is not being immutable. The collection-holding cases copy what they are given, so
 * a caller that keeps its list cannot change what an answer already reported.
 *
 * <p>Nothing here is ordered by a hash. Where an observation is written out — JSON, a snapshot, a
 * message — the writer sorts, because a report that changes between runs cannot be compared between
 * runs.
 */
public sealed interface ObservedValue {

    record Bool(boolean value) implements ObservedValue {}

    /** A whole number: Souther's {@code Int}, and the inner value of a newtype over one. */
    record Integer(long value) implements ObservedValue {}

    record Decimal(BigDecimal value) implements ObservedValue {}

    record Text(String value) implements ObservedValue {}

    /** A {@code Date} or {@code DateTime}, kept as the ISO text it was written as. Separate from
     * {@link Text} so a rule over dates is never compared against a rule over strings. */
    record Temporal(String iso) implements ObservedValue {}

    /** A unit data — a case that carries nothing. Its identity is its name. */
    record Unit(TypeName type) implements ObservedValue {}

    /**
     * A data with fields, and a newtype, whose single field is {@code value} (spec §data). A field
     * whose value is an empty optional is present here with {@link Absent}, rather than left out, so
     * that reading a field chain answers "empty" instead of "not there".
     */
    record Constructed(TypeName type, Map<String, ObservedValue> fields) implements ObservedValue {
        public Constructed {
            fields = Map.copyOf(fields);
        }

        public ObservedValue field(String name) {
            return fields.get(name);
        }
    }

    /** A {@code List} or a {@code Set}. Which one it was is the declared type's to say, not the value's. */
    record Sequence(List<ObservedValue> elements) implements ObservedValue {
        public Sequence {
            elements = List.copyOf(elements);
        }
    }

    /** A {@code Map}, as its entries. Not a {@link Sequence} of pairs: an entry has a key and a value,
     * and flattening it would make the reader restate which is which. */
    record Mapping(List<Entry> entries) implements ObservedValue {
        public Mapping {
            entries = List.copyOf(entries);
        }
    }

    record Entry(ObservedValue key, ObservedValue value) {}

    /** An optional that holds nothing. A present optional is the value it holds, as a fixture writes it. */
    record Absent() implements ObservedValue {}

    /** A value that could not be read back. Carries why, so a measure can say it could not decide
     * rather than reporting a gap it did not see. */
    record Unknown(String reason) implements ObservedValue {}

    /**
     * An observation {@link Limits} stopped. Not the same as a large value: the node budget is one
     * for the whole walk, so a small value observed after a large sibling arrives here too.
     *
     * <p>Nothing about it but that it happened. It carried the size and a fingerprint, for a rule
     * over the value's size to read and for telling two of these apart — and a position is divided
     * by the cases of its type or by where a rule cuts its range, never by how large a value is, so
     * a size was written only where nothing classifies and was {@code -1} wherever anything did.
     * Nothing compares two observations either.
     *
     * <p>Which leaves the case, and the case is read: a row this stands in is one no class holds,
     * and the report says an observation was stopped by a limit. Two of these being equal is Java
     * saying they carry the same nothing, and is not two observations being the same value.
     */
    record Truncated() implements ObservedValue {}

    /** An empty map with a stable iteration order, for building a {@link Constructed}. */
    static Map<String, ObservedValue> fields() {
        return new LinkedHashMap<>();
    }
}
