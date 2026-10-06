package souther.compiler.partition;

import souther.compiler.inputs.TermPath;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

/**
 * Which containers of a row are to hold the value at another position, and which are to hold
 * nothing equal to it — what the demands on a way ask that no region places.
 *
 * <p>Positions on both sides and no values. Which value stands at a position is known only once
 * the parameter it is under has been composed, and the container may be under another parameter
 * altogether; so this says what is asked, and the values are put in where the container is
 * composed ({@link #contentsOf}).
 *
 * <p>Read off the demands and nowhere else: {@link RowDemand.SameAs} on some element is a value
 * written in, and {@link RowDemand.DifferentFrom} on every element is a value kept out. The other
 * two pairings are not composed here — some element unequal to a value, or every element equal to
 * one — and are said as not composed rather than left out.
 *
 * @param asked each container and the value it is to hold or hold nothing equal to, in the order
 *              the way asked them
 */
record ContentsAsked(List<Asked> asked) {

    /** Nothing asked. */
    static final ContentsAsked NONE = new ContentsAsked(List.of());

    ContentsAsked {
        asked = List.copyOf(asked);
    }

    /**
     * That the container at {@code container} holds the value at {@code value}, or holds nothing
     * equal to it.
     */
    record Asked(TermPath container, TermPath value, boolean holding) {}

    /** What {@code way} asks of containers' contents. */
    static ContentsAsked of(List<OnTheWay.TakenIn> way) {
        List<Asked> out = new ArrayList<>();
        for (OnTheWay.TakenIn each : way) {
            switch (each.demand()) {
                case RowDemand.Relational _ -> { }
                case RowDemand.Exists exists -> {
                    for (RowDemand.OfAnElement one : exists.ofAnElement()) {
                        if (one instanceof RowDemand.SameAs(TermPath value)) {
                            out.add(new Asked(exists.container(), value, true));
                        }
                    }
                }
                case RowDemand.ForAll every -> {
                    for (RowDemand.OfAnElement one : every.ofEachElement()) {
                        if (one instanceof RowDemand.DifferentFrom(TermPath value)) {
                            out.add(new Asked(every.container(), value, false));
                        }
                    }
                }
            }
        }
        return new ContentsAsked(out);
    }

    /**
     * What the plan of the parameter {@code head} has to hold for these to be composed: the
     * containers under it that are handed values, and the positions under it a value is read at —
     * for a container of its own or of another parameter's.
     */
    ConstructionPlan.ContentsComposed composedUnder(String head) {
        Set<TermPath> holdingOne = new LinkedHashSet<>();
        Set<TermPath> keepingOut = new LinkedHashSet<>();
        Set<TermPath> read = new LinkedHashSet<>();
        for (Asked each : asked) {
            if (each.container().head().equals(head)) {
                (each.holding() ? holdingOne : keepingOut).add(each.container());
            }
            if (each.value().head().equals(head)) {
                read.add(each.value());
            }
        }
        return new ConstructionPlan.ContentsComposed(holdingOne, keepingOut, read);
    }

    /**
     * Each parameter whose containers are handed a value read off another parameter, with those
     * others: the parameters it has to be composed after.
     */
    Map<String, Set<String>> composedAfter() {
        Map<String, Set<String>> out = new LinkedHashMap<>();
        for (Asked each : asked) {
            String container = each.container().head();
            String value = each.value().head();
            if (!container.equals(value)) {
                out.computeIfAbsent(container, _ -> new LinkedHashSet<>()).add(value);
            }
        }
        return out;
    }

    /**
     * What the container at {@code container} is handed, with each value read by
     * {@code valueAt} — or null where one of them has nothing standing for it.
     */
    ContainerContents contentsOf(TermPath container,
                                 Function<TermPath, FixtureTemplate> valueAt) {
        List<FixtureTemplate> holding = new ArrayList<>();
        List<FixtureTemplate> keptOut = new ArrayList<>();
        for (Asked each : asked) {
            if (!each.container().equals(container)) {
                continue;
            }
            FixtureTemplate value = valueAt.apply(each.value());
            if (value == null) {
                return null;
            }
            (each.holding() ? holding : keptOut).add(value);
        }
        return new ContainerContents(holding, keptOut);
    }
}
