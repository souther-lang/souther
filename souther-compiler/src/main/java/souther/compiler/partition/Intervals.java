package souther.compiler.partition;

import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.Granularity;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Turning the lines a model draws through one numeric position into the ranges between them.
 *
 * <p>Several rules can cut the same position, and they are one partition however they were written.
 * {@code x < 0} and {@code x < 10} are three ranges, not two overlapping pairs, and a report built on
 * the pairs would count a value twice and never reach a hundred percent.
 *
 * <p>The type's own domain comes into it. A newtype's invariant bounds what can be constructed at all,
 * so a range outside it holds no value a row could write and is not a range to cover:
 *
 * <pre>invariant x &gt;= 0   with   guard x &lt; 10   is   0 &lt;= x &lt; 10  and  10 &lt;= x</pre>
 *
 * and not a third range below zero.
 */
final class Intervals {

    /** One range of a position's values. A null bound is the domain's own edge. */
    record Interval(BigDecimal lo, boolean loInclusive, BigDecimal hi, boolean hiInclusive) {

        boolean holds(BigDecimal v) {
            if (lo != null) {
                int c = v.compareTo(lo);
                if (c < 0 || (c == 0 && !loInclusive)) {
                    return false;
                }
            }
            if (hi != null) {
                int c = v.compareTo(hi);
                return c < 0 || (c == 0 && hiInclusive);
            }
            return true;
        }

        /** Whether any value at all is in here. Two cuts at one place leave nothing between them. */
        boolean inhabited() {
            if (lo == null || hi == null) {
                return true;
            }
            int c = lo.compareTo(hi);
            return c < 0 || (c == 0 && loInclusive && hiInclusive);
        }

        String label() {
            String low = lo == null ? "" : (loInclusive ? lo.toPlainString() + " <= " : lo.toPlainString() + " < ");
            String high = hi == null ? "" : (hiInclusive ? " <= " + hi.toPlainString() : " < " + hi.toPlainString());
            if (lo == null && hi == null) {
                return "any";
            }
            return (low + "x" + high).trim();
        }
    }

    /** A place a rule cuts the position, and which side the value itself falls on. */
    private record Split(BigDecimal value, boolean valueBelongsBelow) {}

    /**
     * The ranges {@code thresholds} leave, inside what the position holds.
     *
     * <p>The outer ends are the position's own, and they are taken as they are: an end the position
     * stops short of is an end of the first range too, and rebuilding it as one the range holds puts
     * the value back that the rules had taken away. Thresholds outside what the position holds are
     * dropped — they cut a range no row can reach — and the end itself is outside it as much as
     * anything past it is.
     */
    static List<Interval> of(List<Threshold> thresholds, Endpoint min, Endpoint max) {
        // Keyed by the number and not by the BigDecimal: `0.00` and `0` are one line, and
        // BigDecimal's own equality says they are two, which would leave two ranges holding zero.
        Map<String, Split> distinct = new LinkedHashMap<>();
        for (Threshold each : thresholds) {
            if (!Endpoint.someValueLiesBetween(min, Endpoint.inclusive(each.value()))
                    || !Endpoint.someValueLiesBetween(Endpoint.inclusive(each.value()), max)) {
                continue;
            }
            distinct.putIfAbsent(each.value().stripTrailingZeros().toPlainString(),
                    new Split(each.value(), each.valueBelongsBelow()));
        }
        List<Split> splits = new ArrayList<>(distinct.values());
        splits.sort(Comparator.comparing(Split::value));

        List<Interval> out = new ArrayList<>();
        BigDecimal lo = min == null ? null : min.value();
        boolean loInclusive = min == null || min.inclusive();
        for (Split split : splits) {
            Interval range = new Interval(lo, loInclusive, split.value(), split.valueBelongsBelow());
            if (range.inhabited()) {
                out.add(range);
            }
            lo = split.value();
            loInclusive = !split.valueBelongsBelow();
        }
        Interval last = new Interval(lo, loInclusive, max == null ? null : max.value(),
                max == null || max.inclusive());
        if (last.inhabited()) {
            out.add(last);
        }
        return out.size() < 2 ? List.of() : List.copyOf(out);
    }

    /** The classes those ranges are, on a position of {@code type}. */
    static List<PartitionClass> classesOf(List<Interval> intervals, TermPath path, Type type,
                                          Symbols symbols) {
        boolean decimal = TypeOps.base(type, symbols) == Type.DECIMAL;
        souther.compiler.types.TypeName wrapper = type instanceof Type.Ref ref
                && TypeOps.isSingleValueNewtype(type, symbols) ? ref.name() : null;
        List<PartitionClass> classes = new ArrayList<>();
        for (Interval range : intervals) {
            String id = path + "/" + range.label();
            BigDecimal inside = representative(range, decimal);
            Classifier is = v -> switch (read(v)) {
                case Read.Number number -> Membership.of(range.holds(number.value()));
                case Read.Missing missing -> new Membership.Incomplete(missing.code());
            };
            classes.add(inside == null
                    ? PartitionClass.ungeneratable(id, range.label(), is,
                            "no value of this range can be written without a smallest step")
                    : PartitionClass.of(id, range.label(), is,
                            RepresentativeSource.of(written(inside, wrapper, decimal))));
        }
        return List.copyOf(classes);
    }

    /** A value inside a range, or null where it holds none. Asked of the ends, which is where whether
     * the range holds the value it stops at is written down. */
    private static BigDecimal representative(Interval range, boolean decimal) {
        return Endpoint.valueBetween(
                range.lo() == null ? null : new Endpoint(range.lo(), range.loInclusive()),
                range.hi() == null ? null : new Endpoint(range.hi(), range.hiInclusive()),
                decimal ? Granularity.DENSE : Granularity.DISCRETE);
    }

    /** The number a value holds, or why it holds none. */
    private sealed interface Read {

        record Number(BigDecimal value) implements Read {}

        record Missing(souther.compiler.observe.Incompleteness.Code code) implements Read {}
    }

    /**
     * The number at a value, keeping why there is none where there is none.
     *
     * <p>A newtype is not a step in a path, so the value at a position may be the construction and
     * the number one inside it. Which is why this walk exists, and why the reason it stops has to
     * come back with it: read as a bare {@code null}, an observation a limit stopped is the same
     * answer as a value that is not a number.
     */
    private static Read read(ObservedValue v) {
        Membership.Incomplete unread = Membership.unread(v);
        if (unread != null) {
            return new Read.Missing(unread.code());
        }
        return switch (v) {
            case ObservedValue.Integer i -> new Read.Number(BigDecimal.valueOf(i.value()));
            case ObservedValue.Decimal d -> new Read.Number(d.value());
            case ObservedValue.Constructed c when c.field("value") != null -> read(c.field("value"));
            default -> new Read.Missing(souther.compiler.observe.Incompleteness.Code.VALUE_UNREADABLE);
        };
    }

    /** The number at a value, for a caller that has nothing to say about why there is none. */
    static BigDecimal numberOf(ObservedValue v) {
        return read(v) instanceof Read.Number number ? number.value() : null;
    }

    private static FixtureTemplate written(BigDecimal value, souther.compiler.types.TypeName wrapper,
                                           boolean decimal) {
        FixtureTemplate literal = decimal ? FixtureTemplate.decimal(value)
                : FixtureTemplate.integer(value.longValueExact());
        return wrapper == null ? literal : FixtureTemplate.newtype(wrapper, literal);
    }

    private Intervals() {}
}
