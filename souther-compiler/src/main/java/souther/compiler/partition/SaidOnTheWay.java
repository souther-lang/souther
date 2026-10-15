package souther.compiler.partition;

import souther.compiler.types.ModelOccurrence;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

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

    /**
     * What put the entries of {@code way} on it, and what was asked of the answers, and nothing
     * else this says: what put an entry on another way read with this one is no account of this
     * one.
     *
     * <p>Asked where several ways were walked as one reading and are filed one by one — a
     * comparison and each case of where a line of it decides. Every copy a reader is told put
     * something on a line's way is then a copy that put something on that way.
     */
    public SaidOnTheWay along(List<OnTheWay> way) {
        Map<OnTheWay, List<ModelOccurrence>> on = new LinkedHashMap<>();
        alongInto(way, on);
        return new SaidOnTheWay(on, stated, unstated);
    }

    private void alongInto(List<OnTheWay> way, Map<OnTheWay, List<ModelOccurrence>> on) {
        for (OnTheWay each : way) {
            List<ModelOccurrence> by = entries.get(each);
            if (by != null) {
                on.putIfAbsent(each, by);
            }
            if (each instanceof OnTheWay.OneOf several) {
                several.alternatives().forEach(one -> alongInto(one, on));
            }
        }
    }

    /** Every copy anything on the way was read off, each once, in the order met. */
    public List<ModelOccurrence> copies() {
        Set<ModelOccurrence> out = new LinkedHashSet<>();
        for (Map<?, List<ModelOccurrence>> each : List.of(entries, stated, unstated)) {
            each.values().forEach(out::addAll);
        }
        return List.copyOf(out);
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
        Map<OnTheWay, List<ModelOccurrence>> entries = new LinkedHashMap<>();
        Map<AnswerDemand, List<ModelOccurrence>> stated = new LinkedHashMap<>();
        Map<DemandGap.Unstated, List<ModelOccurrence>> unstated = new LinkedHashMap<>();
        for (SaidOnTheWay way : ways) {
            into(entries, way.entries);
            into(stated, way.stated);
            into(unstated, way.unstated);
        }
        return new SaidOnTheWay(entries, stated, unstated);
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
        eachOnce(by, into.computeIfAbsent(entry, _ -> new ArrayList<>()));
    }

    /**
     * {@code copies} added to {@code held}, each where it was first met and once.
     *
     * <p>Through a set of what is held and not by asking the list: one condition may be written
     * over many constructs, each a copy of its own, and one list asked of each of them in turn is
     * their number squared.
     */
    static void eachOnce(Collection<ModelOccurrence> copies, List<ModelOccurrence> held) {
        Set<ModelOccurrence> there = new HashSet<>(held);
        for (ModelOccurrence copy : copies) {
            if (there.add(copy)) {
                held.add(copy);
            }
        }
    }

    /** {@code from} taken into {@code out}: each key where it was first met, and each copy once. */
    private static <K> void into(Map<K, List<ModelOccurrence>> out,
                                 Map<K, List<ModelOccurrence>> from) {
        from.forEach((key, copies) ->
                eachOnce(copies, out.computeIfAbsent(key, _ -> new ArrayList<>())));
    }

    /** In the order the copies were met, which is the order a reader is told them in. */
    private static <K> Map<K, List<ModelOccurrence>> ordered(Map<K, List<ModelOccurrence>> map) {
        Map<K, List<ModelOccurrence>> out = new LinkedHashMap<>();
        map.forEach((key, copies) -> out.put(key, List.copyOf(copies)));
        return Collections.unmodifiableMap(out);
    }
}
