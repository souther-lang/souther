package souther.compiler.partition;

import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
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
     * The ranges {@code thresholds} leave, inside the domain {@code min}..{@code max} the type allows.
     * Thresholds outside that domain are dropped: they cut a range no row can reach.
     */
    static List<Interval> of(List<Threshold> thresholds, BigDecimal min, BigDecimal max) {
        // Keyed by the number and not by the BigDecimal: `0.00` and `0` are one line, and
        // BigDecimal's own equality says they are two, which would leave two ranges holding zero.
        Map<String, Split> distinct = new LinkedHashMap<>();
        for (Threshold each : thresholds) {
            if (min != null && each.value().compareTo(min) < 0) {
                continue;
            }
            if (max != null && each.value().compareTo(max) > 0) {
                continue;
            }
            distinct.putIfAbsent(each.value().stripTrailingZeros().toPlainString(),
                    new Split(each.value(), each.valueBelongsBelow()));
        }
        List<Split> splits = new ArrayList<>(distinct.values());
        splits.sort(Comparator.comparing(Split::value));

        List<Interval> out = new ArrayList<>();
        BigDecimal lo = min;
        boolean loInclusive = true;
        for (Split split : splits) {
            Interval range = new Interval(lo, loInclusive, split.value(), split.valueBelongsBelow());
            if (range.inhabited()) {
                out.add(range);
            }
            lo = split.value();
            loInclusive = !split.valueBelongsBelow();
        }
        Interval last = new Interval(lo, loInclusive, max, true);
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
            Classifier is = v -> {
                BigDecimal number = numberOf(v);
                return number != null && range.holds(number);
            };
            classes.add(inside == null
                    ? PartitionClass.ungeneratable(id, range.label(), is,
                            "no value of this range can be written without a smallest step")
                    : PartitionClass.of(id, range.label(), is,
                            RepresentativeSource.of(written(inside, wrapper, decimal))));
        }
        return List.copyOf(classes);
    }

    /** A value inside a range, or null where the type cannot name one — a decimal range open at the
     * end it would have to step away from. */
    private static BigDecimal representative(Interval range, boolean decimal) {
        BoundaryDomain domain = decimal ? BoundaryDomain.DECIMAL : BoundaryDomain.INT;
        if (range.lo() != null && range.hi() != null) {
            BigDecimal lo = range.loInclusive() ? range.lo() : step(range.lo(), domain, decimal, true);
            if (lo == null) {
                return null;
            }
            return range.holds(lo) ? lo : null;
        }
        if (range.lo() != null) {
            return range.loInclusive() ? range.lo() : step(range.lo(), domain, decimal, true);
        }
        if (range.hi() != null) {
            return range.hiInclusive() ? range.hi() : step(range.hi(), domain, decimal, false);
        }
        return BigDecimal.ZERO;
    }

    private static BigDecimal step(BigDecimal from, BoundaryDomain domain, boolean decimal,
                                   boolean up) {
        ObservedValue at = decimal ? new ObservedValue.Decimal(from)
                : new ObservedValue.Integer(from.longValueExact());
        return (up ? domain.successor(at) : domain.predecessor(at))
                .map(Intervals::numberOf).orElse(null);
    }

    static BigDecimal numberOf(ObservedValue v) {
        return switch (v) {
            case ObservedValue.Integer i -> BigDecimal.valueOf(i.value());
            case ObservedValue.Decimal d -> d.value();
            case ObservedValue.Constructed c when c.field("value") != null -> numberOf(c.field("value"));
            case null, default -> null;
        };
    }

    private static FixtureTemplate written(BigDecimal value, souther.compiler.types.TypeName wrapper,
                                           boolean decimal) {
        FixtureTemplate literal = decimal ? FixtureTemplate.decimal(value)
                : FixtureTemplate.integer(value.longValueExact());
        return wrapper == null ? literal : FixtureTemplate.newtype(wrapper, literal);
    }

    private Intervals() {}
}
