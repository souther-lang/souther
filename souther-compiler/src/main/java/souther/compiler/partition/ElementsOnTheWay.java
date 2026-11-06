package souther.compiler.partition;

import souther.compiler.inputs.ElementsNamed;
import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.types.BindingId;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Which conditions on a way may be composed as statements of one value.
 *
 * <p>A region, a requirement and a truth asked are each keyed by position, and a position inside a
 * container's elements says an element and not which one: composed together, {@code a.n < 0} and
 * {@code b.n >= 1} over {@code x.items} say one element is both, and a way {@code [-1, 1]} takes is
 * shown taken by none. So for each element of a container, the conditions read of it through one
 * name are taken in and the ones read through another are declined. The region a way leaves is then
 * still every row that arrives, since what it does not take in only leaves it wider, and a condition
 * on the row itself is never given up for it.
 *
 * <p>The name kept is the one the border is read through, where the border reads that element:
 * what is looked for there is a value of that element. Elsewhere it is the first name the way met
 * it by. Where the border reads one element through two names, nothing on the way is kept for it.
 *
 * <p>Only what the names say. A condition whose names stood for no element is the row's, and one
 * whose names were not worked out names nothing here; both are taken as they stand. A condition of
 * several ways, or a count of statements, is declined whole where something inside it is: what it
 * states is one statement of all of its parts.
 */
final class ElementsOnTheWay {

    private ElementsOnTheWay() {}

    /**
     * Why a condition read of another element than the one the way holds was not taken in: what
     * it states was read, and the way has no place for a second element beside the first.
     */
    static final List<WhyNotTaken> ANOTHER_ELEMENT = List.of(new WhyNotTaken.OutsideDomain(
            WhyNotTaken.DomainLimit.ANOTHER_ELEMENT_THAN_THE_WAY_HOLDS));

    /**
     * {@code way} with every condition read of an element through a name other than the one kept
     * for that element declined — {@code way} itself where none is.
     *
     * @param border the elements the border is read of, which decide the name kept for each of
     *               them; {@link ElementsNamed#NONE} where the way is asked of no border
     */
    static List<OnTheWay> keptToOneElementEach(List<OnTheWay> way, ElementsNamed border) {
        Map<ElementsNamed.Slot, BindingId> kept = new LinkedHashMap<>();
        Set<ElementsNamed.Slot> keptNone = new HashSet<>();
        border.named().forEach((slot, names) -> {
            if (names.size() == 1) {
                kept.put(slot, names.iterator().next());
            } else {
                keptNone.add(slot);
            }
        });
        keptNone.addAll(border.unnamed());
        boolean anyNamed = !border.isEmpty();
        for (OnTheWay each : way) {
            ElementsNamed named = namedIn(each);
            anyNamed |= !named.isEmpty();
            named.named().forEach((slot, names) -> {
                if (names.size() == 1 && !keptNone.contains(slot)) {
                    kept.putIfAbsent(slot, names.iterator().next());
                }
            });
        }
        if (!anyNamed) {
            return way;
        }
        List<OnTheWay> out = null;
        for (int at = 0; at < way.size(); at++) {
            OnTheWay each = way.get(at);
            if (agrees(namedIn(each), kept)) {
                if (out != null) {
                    out.add(each);
                }
                continue;
            }
            if (out == null) {
                out = new ArrayList<>(way.subList(0, at));
            }
            out.add(declined(each));
        }
        return out == null ? way : List.copyOf(out);
    }

    /** Whether every element {@code named} reads is read through the name kept for it: none
     *  through a name whose element is not known. */
    private static boolean agrees(ElementsNamed named, Map<ElementsNamed.Slot, BindingId> kept) {
        if (!named.unnamed().isEmpty()) {
            return false;
        }
        for (Map.Entry<ElementsNamed.Slot, Set<BindingId>> each : named.named().entrySet()) {
            BindingId one = kept.get(each.getKey());
            if (one == null || !each.getValue().equals(Set.of(one))) {
                return false;
            }
        }
        return true;
    }

    /** The elements the names in {@code entry} stood for, inside every way it leaves a row and
     *  every statement it counts as well. */
    static ElementsNamed namedIn(OnTheWay entry) {
        return switch (entry) {
            case OnTheWay.TakenIn taken -> taken.named().elements();
            case OnTheWay.Narrowed narrowed -> narrowed.named().elements();
            case OnTheWay.OneOf several -> {
                ElementsNamed out = ElementsNamed.NONE;
                for (List<OnTheWay> one : several.alternatives()) {
                    for (OnTheWay each : one) {
                        out = out.and(namedIn(each));
                    }
                }
                yield out;
            }
            case OnTheWay.Counted counted -> {
                ElementsNamed out = ElementsNamed.NONE;
                for (OnTheWay each : counted.parts()) {
                    out = out.and(namedIn(each));
                }
                yield out;
            }
            case OnTheWay.Settled _, OnTheWay.Declined _ -> ElementsNamed.NONE;
        };
    }

    /** {@code entry}, which reads an element through another name than the way holds it by,
     *  declined at its condition. */
    private static OnTheWay declined(OnTheWay entry) {
        return new OnTheWay.Declined(conditionOf(entry), entry.anchor(), ANOTHER_ELEMENT);
    }

    /** The condition {@code entry} was read off: one that names an element names it. */
    static ConditionOccurrence conditionOf(OnTheWay entry) {
        return switch (entry) {
            case OnTheWay.TakenIn taken -> taken.named().condition();
            case OnTheWay.Narrowed narrowed -> narrowed.named().condition();
            case OnTheWay.OneOf several -> several.condition();
            case OnTheWay.Counted counted -> counted.condition();
            case OnTheWay.Settled _, OnTheWay.Declined _ -> throw new IllegalStateException(
                    "a condition that names no element is never declined for one: " + entry);
        };
    }
}
