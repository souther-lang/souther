package souther.compiler.partition;

import souther.compiler.types.ModelOccurrences;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Which copies of the model's code put each thing on one way to a line or a rule.
 *
 * <p>Of one way, and carried with it from where it was walked. A helper called twice is one
 * construct copied twice, and what its comparison asks of a row is put on the way once by each
 * copy the way goes through — and only by those. Asked afterwards of every way a reading walked,
 * the same value would answer with the calls of ways this one never took.
 *
 * <p>Keyed by the value, within the way. Two copies on one way asking one thing of a row ask it
 * twice, and both are what put it there.
 *
 * @param entries what each entry on the way was put there by, inside an alternative as much as
 *                beside one
 * @param stated  what each demand on the answers was asked by
 * @param unstated what each demand this reading could not state was asked by
 */
public record SaidOnTheWay(Map<OnTheWay, ModelOccurrences> entries,
                           Map<AnswerDemand, ModelOccurrences> stated,
                           Map<DemandGap.Unstated, ModelOccurrences> unstated) {

    /** A way no copy of anybody's code put anything on. */
    public static final SaidOnTheWay NONE = new SaidOnTheWay(Map.of(), Map.of(), Map.of());

    public SaidOnTheWay {
        entries = ordered(entries);
        stated = ordered(stated);
        unstated = ordered(unstated);
    }

    /** The copies that put on the way what {@code gap} is about, in the order they were met. */
    public ModelOccurrences of(ConditionGap gap) {
        ModelOccurrences by = switch (gap) {
            case ConditionGap.OfTheInput(ReachabilityGap.Unstated(var declined)) ->
                    entries.get(declined);
            case ConditionGap.OfTheInput(ReachabilityGap.Uncomposed(var taken, var _)) ->
                    entries.get(taken);
            case ConditionGap.OfTheInput(ReachabilityGap.LookedAlongWhole(var oneOf, var _)) ->
                    entries.get(oneOf);
            case ConditionGap.OfTheInput(ReachabilityGap.ProvedImpossible(var taken)) ->
                    entries.get(taken);
            case ConditionGap.OfADemand(DemandGap.Unstated unread) -> unstated.get(unread);
            case ConditionGap.OfADemand(DemandGap.Uncomposed(var demand, var _)) ->
                    stated.get(demand);
        };
        return by == null ? ModelOccurrences.NONE : by;
    }

    /** Every copy anything on the way was read off, each once, in the order met. */
    public ModelOccurrences copies() {
        ModelOccurrences.Gathering out = new ModelOccurrences.Gathering();
        for (Map<?, ModelOccurrences> each : List.of(entries, stated, unstated)) {
            each.values().forEach(out::add);
        }
        return out.gathered();
    }

    /**
     * The same, with {@code demands} asked by every copy anything on the way was read off.
     *
     * <p>For the demands of one condition, which it asks of the answers out of what it states: they
     * were read off what the condition's statement was, and not off any one entry of it.
     */
    public SaidOnTheWay asking(AnswersDemanded demands) {
        ModelOccurrences every = copies();
        Map<AnswerDemand, ModelOccurrences> asked = new LinkedHashMap<>(stated);
        Map<DemandGap.Unstated, ModelOccurrences> declined = new LinkedHashMap<>(unstated);
        if (!every.isEmpty()) {
            demands.stated().forEach(demand -> asked.put(demand, every));
            demands.declined().forEach(demand -> declined.put(demand, every));
        }
        return new SaidOnTheWay(entries, asked, declined);
    }

    /**
     * The same, with what {@code other} says {@code from} was read off told of {@code onto}, entry
     * for entry: {@code from} is the same condition asked again, and {@code onto} what it asked
     * the first time.
     *
     * <p>By place and not by value. One condition asked twice asks the same things in the same
     * order, but an entry a reading names where it met it is a different value each time, and
     * matched by value the second asking would be told of nothing on the way. Where the two do not
     * line up — different numbers of entries, or one of several things where the other has none —
     * what the second was read off is kept beside the first by value, which is all that is left.
     */
    public SaidOnTheWay retold(List<OnTheWay> onto, List<OnTheWay> from, SaidOnTheWay other) {
        Map<OnTheWay, ModelOccurrences> told = new LinkedHashMap<>(entries);
        if (!retoldInto(onto, from, other, told)) {
            return and(other);
        }
        SaidOnTheWay demands = new SaidOnTheWay(Map.of(), other.stated, other.unstated);
        return new SaidOnTheWay(told, stated, unstated).and(demands);
    }

    private static boolean retoldInto(List<OnTheWay> onto, List<OnTheWay> from,
                                      SaidOnTheWay other,
                                      Map<OnTheWay, ModelOccurrences> into) {
        if (onto.size() != from.size()) {
            return false;
        }
        for (int at = 0; at < onto.size(); at++) {
            OnTheWay mine = onto.get(at);
            OnTheWay theirs = from.get(at);
            if (mine.getClass() != theirs.getClass()) {
                return false;
            }
            filedAlone(mine, other.entries.getOrDefault(theirs, ModelOccurrences.NONE), into);
            if (mine instanceof OnTheWay.OneOf one && theirs instanceof OnTheWay.OneOf two) {
                if (one.alternatives().size() != two.alternatives().size()) {
                    return false;
                }
                for (int each = 0; each < one.alternatives().size(); each++) {
                    if (!retoldInto(one.alternatives().get(each), two.alternatives().get(each),
                            other, into)) {
                        return false;
                    }
                }
            }
        }
        return true;
    }

    /** Both, as what put things on a way two ways of reaching one line or rule share. */
    public SaidOnTheWay and(SaidOnTheWay other) {
        return allOf(List.of(this, other));
    }

    /**
     * Every one of {@code ways}, as what put things on a way they all reach one line or rule by:
     * {@link #and} taken over them in order.
     *
     * <p>Put together at once rather than two at a time. A thing on a way is filed under its value,
     * which is a tree, and taking the ways two at a time files everything gathered so far again at
     * each step — so a line read once per call of a helper paid for its ways once per call for
     * every call before it.
     */
    public static SaidOnTheWay allOf(List<SaidOnTheWay> ways) {
        Map<OnTheWay, ModelOccurrences.Gathering> entries = new LinkedHashMap<>();
        Map<AnswerDemand, ModelOccurrences.Gathering> stated = new LinkedHashMap<>();
        Map<DemandGap.Unstated, ModelOccurrences.Gathering> unstated = new LinkedHashMap<>();
        for (SaidOnTheWay way : ways) {
            into(entries, way.entries);
            into(stated, way.stated);
            into(unstated, way.unstated);
        }
        return new SaidOnTheWay(gathered(entries), gathered(stated), gathered(unstated));
    }

    /** What {@code entries} were put on a way by: {@code by}, for each of them and every entry
     *  inside an alternative of one. */
    static void filed(List<OnTheWay> entries, ModelOccurrences by,
                      Map<OnTheWay, ModelOccurrences> into) {
        for (OnTheWay each : entries) {
            filedAlone(each, by, into);
            if (each instanceof OnTheWay.OneOf several) {
                several.alternatives().forEach(one -> filed(one, by, into));
            }
        }
    }

    /** What {@code entry} itself was put on a way by, leaving what its alternatives were put
     *  there by to whoever made them. */
    static void filedAlone(OnTheWay entry, ModelOccurrences by,
                           Map<OnTheWay, ModelOccurrences> into) {
        if (!by.isEmpty()) {
            into.merge(entry, by, ModelOccurrences::and);
        }
    }

    /** {@code from} gathered into {@code out}: each key where it was first met. */
    private static <K> void into(Map<K, ModelOccurrences.Gathering> out,
                                 Map<K, ModelOccurrences> from) {
        from.forEach((key, copies) ->
                out.computeIfAbsent(key, _ -> new ModelOccurrences.Gathering()).add(copies));
    }

    private static <K> Map<K, ModelOccurrences> gathered(
            Map<K, ModelOccurrences.Gathering> gathering) {
        Map<K, ModelOccurrences> out = new LinkedHashMap<>();
        gathering.forEach((key, copies) -> out.put(key, copies.gathered()));
        return out;
    }

    /** Each key in the order it was met, which is the order a reader is told them in. */
    private static <K> Map<K, ModelOccurrences> ordered(Map<K, ModelOccurrences> map) {
        return Collections.unmodifiableMap(new LinkedHashMap<>(map));
    }
}
