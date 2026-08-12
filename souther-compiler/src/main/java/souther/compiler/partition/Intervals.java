package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.CountDomain;
import souther.compiler.numeric.Endpoint;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

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

    /** One range of a position's counts. A null bound is the domain's own edge. */
    record Interval(Place lo, boolean loInclusive, Place hi, boolean hiInclusive) {

        boolean holds(Place v) {
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

        String label(Carrier carrier) {
            String low = lo == null ? ""
                    : (loInclusive ? carrier.written(lo) + " <= " : carrier.written(lo) + " < ");
            String high = hi == null ? ""
                    : (hiInclusive ? " <= " + carrier.written(hi) : " < " + carrier.written(hi));
            if (lo == null && hi == null) {
                return "any";
            }
            return (low + "x" + high).trim();
        }
    }

    /** A place a rule cuts the position, and which side the count itself falls on. */
    private record Split(Place value, boolean valueBelongsBelow) {}

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
        // Keyed by the number and not by the count's own equality: `0.00` and `0` are one line, and
        // BigDecimal's equality says they are two, which would leave two ranges holding zero.
        Map<String, Split> distinct = new LinkedHashMap<>();
        for (Threshold each : thresholds) {
            if (!Endpoint.someValueLiesBetween(min, Endpoint.inclusive(each.value()))
                    || !Endpoint.someValueLiesBetween(Endpoint.inclusive(each.value()), max)) {
                continue;
            }
            distinct.putIfAbsent(each.value().key(),
                    new Split(each.value(), each.valueBelongsBelow()));
        }
        List<Split> splits = new ArrayList<>(distinct.values());
        splits.sort(Comparator.comparing(Split::value));

        List<Interval> out = new ArrayList<>();
        Place lo = min == null ? null : min.at();
        boolean loInclusive = min == null || min.inclusive();
        for (Split split : splits) {
            Interval range = new Interval(lo, loInclusive, split.value(), split.valueBelongsBelow());
            if (range.inhabited()) {
                out.add(range);
            }
            lo = split.value();
            loInclusive = !split.valueBelongsBelow();
        }
        Interval last = new Interval(lo, loInclusive, max == null ? null : max.at(),
                max == null || max.inclusive());
        if (last.inhabited()) {
            out.add(last);
        }
        return out.size() < 2 ? List.of() : List.copyOf(out);
    }

    /**
     * The classes those ranges are, on the term {@code of} at a position of {@code type}.
     *
     * <p>The term says how a row's value is read into a number and how its numbers are spaced; the
     * type says what a value written at one of them looks like. A range of lengths has the first and
     * not the second: five is not what is written at the position, a string of five characters is,
     * and which values carry a count is asked of what builds them rather than settled here.
     */
    static List<PartitionClass> classesOf(List<Interval> intervals, NumericTerm of, Type type,
                                          Symbols symbols) {
        // What the counts in a label stand for. A day count is a carrier and never a name for the
        // line, so the class an author reads is spelled in dates where the position holds them.
        Carrier carrier = of.carrierAt(type, symbols);
        List<PartitionClass> classes = new ArrayList<>();
        for (Interval range : intervals) {
            String label = range.label(carrier);
            String id = of + "/" + label;
            Place inside = representative(range, carrier);
            Classifier is = v -> switch (of.read(v, carrier)) {
                case NumericTerm.Reading.Number number -> Membership.of(range.holds(number.value()));
                case NumericTerm.Reading.Missing missing ->
                        new Membership.Incomplete(missing.code());
                case NumericTerm.Reading.NotNumber _ -> Membership.NO_MATCH;
            };
            if (inside == null) {
                classes.add(PartitionClass.ungeneratable(id, label, is,
                        "no value this position can hold lies inside this range"));
                continue;
            }
            List<FixtureTemplate> values = standingIn(of, inside, type, carrier, symbols);
            classes.add(values.isEmpty()
                    ? PartitionClass.ungeneratable(id, label, is,
                            "nothing here writes a value whose " + measureOf(of) + " is in this range")
                    : PartitionClass.of(id, label, is,
                            RepresentativeSource.of(values.toArray(new FixtureTemplate[0]))));
        }
        return List.copyOf(classes);
    }

    private static String measureOf(NumericTerm of) {
        return of instanceof NumericTerm.SizeOf size ? size.measure().qualified() : "value";
    }

    /**
     * A value inside a range, or null where it holds none. Asked of the ends, which is where whether
     * the range holds the value it stops at is written down.
     *
     * <p>How the values step is the carrier's to say and is asked of it. Carried as "is it a decimal"
     * it was a second spelling of the same fact, and a carrier that is dense without being the
     * decimal — a date-time — answered no to it: the range between two moments a nanosecond apart
     * came back as one holding no value, which is what a whole step would leave and not what the
     * values do.
     */
    private static Place representative(Interval range, Carrier carrier) {
        Place between = carrier.somethingInside(
                range.lo() == null ? null : new Endpoint(range.lo(), range.loInclusive()),
                range.hi() == null ? null : new Endpoint(range.hi(), range.hiInclusive()));
        if (between == null) {
            return null;
        }
        // What the carrier can hold, and then whether the range still holds it. Spacing answers what
        // a strict bound may be sharpened onto and is not a promise that every number between two
        // counts is one — asking it for both is how a class open at both ends came to offer the
        // count at one of its ends.
        Place held = carrier.onTheGrid(between);
        return held != null && range.holds(held) ? held : null;
    }

    /**
     * Values of the position that read as {@code inside} on this term, or none where the term is one
     * nothing here can put a value on.
     *
     * <p>A number the term reads out of the value is written into it; a number the term counts of the
     * value is a value carrying that many, which is {@link Witnesses}'s question rather than this
     * one's. Asked of it rather than answered here, so that this says a range has no representative
     * only when the thing that builds them has none to give.
     */
    private static List<FixtureTemplate> standingIn(NumericTerm of, Place inside, Type type,
                                                    Carrier carrier, Symbols symbols) {
        if (of instanceof NumericTerm.ValueOf) {
            FixtureTemplate standing = Witnesses.wrapped(type,
                    FixtureTemplate.on(carrier, inside, symbols::reach), symbols);
            return standing == null ? List.of() : List.of(standing);
        }
        int size = CountDomain.asCount(inside);
        if (size < 0) {
            return List.of();
        }
        List<FixtureTemplate> out = new ArrayList<>();
        for (FixtureTemplate each
                : Witnesses.ofSize(TypeOps.base(type, symbols), size, symbols, Set.of()).values()) {
            out.add(Witnesses.wrapped(type, each, symbols));
        }
        return List.copyOf(out);
    }

    private Intervals() {}
}
