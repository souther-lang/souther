package souther.compiler.partition;

import souther.compiler.types.ModelOccurrence;

import java.util.ArrayList;
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
public record SaidOnTheWay(Map<OnTheWay, List<ModelOccurrence>> entries,
                           Map<AnswerDemand, List<ModelOccurrence>> stated,
                           Map<DemandGap.Unstated, List<ModelOccurrence>> unstated) {

    /** A way no copy of anybody's code put anything on. */
    public static final SaidOnTheWay NONE = new SaidOnTheWay(Map.of(), Map.of(), Map.of());

    public SaidOnTheWay {
        entries = ordered(entries);
        stated = ordered(stated);
        unstated = ordered(unstated);
    }

    /** The copies that put on the way what {@code gap} is about, in the order they were met. */
    public List<ModelOccurrence> of(ConditionGap gap) {
        List<ModelOccurrence> by = switch (gap) {
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
        return by == null ? List.of() : by;
    }

    /** Every copy anything on the way was read off, each once, in the order met. */
    public List<ModelOccurrence> copies() {
        List<ModelOccurrence> out = new ArrayList<>();
        for (Map<?, List<ModelOccurrence>> each : List.of(entries, stated, unstated)) {
            each.values().forEach(copies -> copies.stream().filter(copy -> !out.contains(copy))
                    .forEach(out::add));
        }
        return out;
    }

    /**
     * The same, with {@code demands} asked by every copy anything on the way was read off.
     *
     * <p>For the demands of one condition, which it asks of the answers out of what it states: they
     * were read off what the condition's statement was, and not off any one entry of it.
     */
    public SaidOnTheWay asking(AnswersDemanded demands) {
        List<ModelOccurrence> every = copies();
        Map<AnswerDemand, List<ModelOccurrence>> asked = new LinkedHashMap<>(stated);
        Map<DemandGap.Unstated, List<ModelOccurrence>> declined = new LinkedHashMap<>(unstated);
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
        Map<OnTheWay, List<ModelOccurrence>> told = new LinkedHashMap<>();
        entries.forEach((key, copies) -> told.put(key, new ArrayList<>(copies)));
        if (!retoldInto(onto, from, other, told)) {
            return and(other);
        }
        SaidOnTheWay demands = new SaidOnTheWay(Map.of(), other.stated, other.unstated);
        return new SaidOnTheWay(told, stated, unstated).and(demands);
    }

    private static boolean retoldInto(List<OnTheWay> onto, List<OnTheWay> from,
                                      SaidOnTheWay other,
                                      Map<OnTheWay, List<ModelOccurrence>> into) {
        if (onto.size() != from.size()) {
            return false;
        }
        for (int at = 0; at < onto.size(); at++) {
            OnTheWay mine = onto.get(at);
            OnTheWay theirs = from.get(at);
            if (mine.getClass() != theirs.getClass()) {
                return false;
            }
            filedAlone(mine, other.entries.getOrDefault(theirs, List.of()), into);
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
        return new SaidOnTheWay(together(entries, other.entries), together(stated, other.stated),
                together(unstated, other.unstated));
    }

    /** What {@code entries} were put on a way by: {@code by}, for each of them and every entry
     *  inside an alternative of one. */
    static void filed(List<OnTheWay> entries, List<ModelOccurrence> by,
                      Map<OnTheWay, List<ModelOccurrence>> into) {
        for (OnTheWay each : entries) {
            filedAlone(each, by, into);
            if (each instanceof OnTheWay.OneOf several) {
                several.alternatives().forEach(one -> filed(one, by, into));
            }
        }
    }

    /** What {@code entry} itself was put on a way by, leaving what its alternatives were put
     *  there by to whoever made them. */
    static void filedAlone(OnTheWay entry, List<ModelOccurrence> by,
                           Map<OnTheWay, List<ModelOccurrence>> into) {
        if (by.isEmpty()) {
            return;
        }
        List<ModelOccurrence> copies = into.computeIfAbsent(entry, _ -> new ArrayList<>());
        by.stream().filter(copy -> !copies.contains(copy)).forEach(copies::add);
    }

    private static <K> Map<K, List<ModelOccurrence>> together(Map<K, List<ModelOccurrence>> one,
                                                               Map<K, List<ModelOccurrence>> other) {
        Map<K, List<ModelOccurrence>> out = new LinkedHashMap<>();
        one.forEach((key, copies) -> out.put(key, new ArrayList<>(copies)));
        other.forEach((key, copies) -> {
            List<ModelOccurrence> held = out.computeIfAbsent(key, _ -> new ArrayList<>());
            copies.stream().filter(copy -> !held.contains(copy)).forEach(held::add);
        });
        return out;
    }

    /** In the order the copies were met, which is the order a reader is told them in. */
    private static <K> Map<K, List<ModelOccurrence>> ordered(Map<K, List<ModelOccurrence>> map) {
        Map<K, List<ModelOccurrence>> out = new LinkedHashMap<>();
        map.forEach((key, copies) -> out.put(key, List.copyOf(copies)));
        return Collections.unmodifiableMap(out);
    }
}
