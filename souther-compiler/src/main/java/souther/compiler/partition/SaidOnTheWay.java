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

    /** Both, as what put things on a way two ways of reaching one line or rule share. */
    public SaidOnTheWay and(SaidOnTheWay other) {
        return new SaidOnTheWay(together(entries, other.entries), together(stated, other.stated),
                together(unstated, other.unstated));
    }

    /** What {@code entries} were put on a way by: {@code by}, for each of them and every entry
     *  inside an alternative of one. */
    static void filed(List<OnTheWay> entries, ModelOccurrence by,
                      Map<OnTheWay, List<ModelOccurrence>> into) {
        for (OnTheWay each : entries) {
            List<ModelOccurrence> copies = into.computeIfAbsent(each, _ -> new ArrayList<>());
            if (!copies.contains(by)) {
                copies.add(by);
            }
            if (each instanceof OnTheWay.OneOf several) {
                several.alternatives().forEach(one -> filed(one, by, into));
            }
        }
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
