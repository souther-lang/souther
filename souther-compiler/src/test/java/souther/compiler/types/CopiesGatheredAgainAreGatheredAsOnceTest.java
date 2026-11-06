package souther.compiler.types;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Copies gathered are each copy once, in the order first met, however the values they came in
 * were handed over: one value handed again, one equal to it, one sharing copies with another, or
 * one copy by itself. Held against every copy of every value put into one set in turn, over every
 * order of a few of them.
 */
class CopiesGatheredAgainAreGatheredAsOnceTest {

    private static ModelOccurrence copy(int ordinal) {
        return new ModelOccurrence(SourceConstructOrigin.written(new WrittenOwner.Body("demo", "go"),
                ordinal, SourceConstruct.IF), ExpansionLineage.ORIGINAL);
    }

    /** One step of gathering: a value of copies, or a copy by itself. */
    private record Step(ModelOccurrences copies, ModelOccurrence alone) {

        void into(ModelOccurrences.Gathering gathering) {
            if (copies != null) {
                gathering.add(copies);
            } else {
                gathering.add(alone);
            }
        }

        void into(Set<ModelOccurrence> held) {
            if (copies != null) {
                copies.forEach(held::add);
            } else {
                held.add(alone);
            }
        }
    }

    @Test
    void everyOrderOfAFewIsWhatOneSetOfTheirCopiesHolds() {
        ModelOccurrences ab = ModelOccurrences.of(List.of(copy(0), copy(1)));
        ModelOccurrences bc = ModelOccurrences.of(List.of(copy(1), copy(2)));
        ModelOccurrences abAgain = ModelOccurrences.of(List.of(copy(0), copy(1)));
        List<Step> steps = List.of(new Step(ab, null), new Step(bc, null),
                new Step(abAgain, null), new Step(ModelOccurrences.NONE, null),
                new Step(null, copy(3)), new Step(null, copy(0)));
        List<List<Step>> orders = new ArrayList<>();
        orders.add(List.of());
        for (int length = 1; length <= 4; length++) {
            List<List<Step>> longer = new ArrayList<>();
            for (List<Step> order : orders) {
                if (order.size() == length - 1) {
                    for (Step next : steps) {
                        List<Step> one = new ArrayList<>(order);
                        one.add(next);
                        longer.add(one);
                    }
                }
            }
            orders.addAll(longer);
        }
        for (List<Step> order : orders) {
            ModelOccurrences.Gathering gathering = new ModelOccurrences.Gathering();
            Set<ModelOccurrence> held = new LinkedHashSet<>();
            for (Step step : order) {
                step.into(gathering);
                step.into(held);
            }
            assertEquals(List.copyOf(held), gathering.gathered().inOrder(), order.toString());
        }
    }
}
