package souther.compiler.partition;

import java.util.ArrayList;
import java.util.EnumSet;
import java.util.List;
import java.util.Set;

/**
 * What a row can be held to for the decisions of a combination, and what is left to the run.
 *
 * <p>A decision nothing here can state a demand for ({@link HeldOutcome.Bringing.NothingFound}) is
 * left out and does not stop the others being held to. What a demand does for a combination is
 * steer a search: what says a row made it is a run, which watches every decision whether it was
 * held to or not. Held to all of them or to none, as a row repaired past a guard is, a combination
 * with one decision this reads no demand for would never be looked for along the others.
 *
 * <p>A decision no value stands on a side of is read all the same: it is the answer that no row
 * holds the decisions together, and the parts held together say so.
 *
 * @param readable what holds each decision a demand could be read for, or that no value stands on
 *                 the side it comes out on
 * @param cutShort the figures that left the ways of holding a decision unlooked at, which is the
 *                 plan being cut short
 */
record ReadableDemands(List<HeldOutcome.Bringing> readable, Set<CompositionBudget> cutShort) {

    ReadableDemands {
        readable = List.copyOf(readable);
        cutShort = InDeclaredOrder.of(cutShort);
    }

    /** What {@code each}, what holds one decision apiece, comes to. */
    static ReadableDemands of(List<HeldOutcome.Bringing> each) {
        List<HeldOutcome.Bringing> readable = new ArrayList<>();
        Set<CompositionBudget> cutShort = EnumSet.noneOf(CompositionBudget.class);
        for (HeldOutcome.Bringing one : each) {
            switch (one) {
                case HeldOutcome.Bringing.Found _, HeldOutcome.Bringing.NoValueCanStandThere _ ->
                        readable.add(one);
                case HeldOutcome.Bringing.LeftUnlooked(Set<CompositionBudget> figures) ->
                        cutShort.addAll(figures);
                case HeldOutcome.Bringing.NothingFound _ -> { }
            }
        }
        return new ReadableDemands(readable, cutShort);
    }
}
