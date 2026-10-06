package souther.compiler.partition;

import souther.compiler.inputs.NameReach;
import souther.compiler.inputs.Requirements;
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
     * Every way of writing what is asked under cases a row that is already {@code trying} can be,
     * in the order the model declares the cases.
     *
     * <p><b>The place a container or a value is named is where a row writes it, except at a name
     * every case of a sum spreads.</b> There the row writes one of the cases, and the container
     * stands under whichever it is — so a container asked for at the sum's own name is no position
     * of the row at all, and composed there it would be composed nowhere. Each way says where under
     * the cases every container and value of it stands, which is a position the plan of the
     * parameter holds; what the case it stands under requires travels with the path.
     *
     * <p><b>Every case and not one of them,</b> for the reason a number at such a name is written
     * every way ({@code Generator.waysToWrite}): which case the row is decides which rules hold of
     * the value, so it is not settled here. And all of them under cases the row can be at once:
     * two names of one sum are written under one case, and a way that put them under two would be
     * a value that is both.
     *
     * <p>A case whose reading stopped before putting the name anywhere is no place to write it, and
     * is not a way.
     */
    List<ContentsAsked> ways(NameReach reach, Requirements trying) {
        Set<TermPath> named = new LinkedHashSet<>();
        for (Asked each : asked) {
            named.add(each.container());
            named.add(each.value());
        }
        List<TermPath> paths = List.copyOf(named);
        List<List<NameReach.CaseStanding>> standings = new ArrayList<>();
        for (TermPath each : paths) {
            standings.add(standingsOf(reach, each, Requirements.NONE, 0));
        }
        List<ContentsAsked> out = new ArrayList<>();
        written(paths, standings, 0, trying, new LinkedHashMap<>(), out);
        return List.copyOf(out);
    }

    /** The ways from the {@code next}-th named path on, under what the ones before it took. */
    private void written(List<TermPath> paths, List<List<NameReach.CaseStanding>> standings,
                         int next, Requirements trying, Map<TermPath, TermPath> at,
                         List<ContentsAsked> out) {
        if (next == paths.size()) {
            List<Asked> under = new ArrayList<>();
            for (Asked each : asked) {
                under.add(new Asked(at.get(each.container()), at.get(each.value()),
                        each.holding()));
            }
            out.add(new ContentsAsked(under));
            return;
        }
        for (NameReach.CaseStanding standing : standings.get(next)) {
            if (trying.merge(standing.assuming()) instanceof Requirements.Merge.Merged(
                    Requirements taken)
                    && taken.merge(standing.position().requirements())
                            instanceof Requirements.Merge.Merged(Requirements both)) {
                at.put(paths.get(next), standing.position());
                written(paths, standings, next + 1, both, at, out);
                at.remove(paths.get(next));
            }
        }
    }

    /**
     * Where the name at {@code path} stands under the cases it crosses, with what each case
     * requires — or the path itself, requiring nothing, where nothing crosses.
     *
     * <p>Followed one crossing at a time, since a name under two sums is moved by the outer one
     * before the inner one can see it ({@link NameReach#standingOf}); bounded by the crossings the
     * walk recorded, because each step takes one of them.
     */
    private static List<NameReach.CaseStanding> standingsOf(NameReach reach, TermPath path,
                                                            Requirements assuming, int crossed) {
        if (crossed > reach.crossings().size()) {
            throw new IllegalStateException(
                    "a name was followed past every crossing this reading recorded: " + path);
        }
        List<NameReach.CaseStanding> under = switch (reach.standingOf(path)) {
            case NameReach.Standing.AtThePathItself _ -> null;
            case NameReach.Standing.UnderTheCases(var standings) -> standings;
            case NameReach.Standing.CasesIncomplete(var standings, var _) -> standings;
        };
        if (under == null) {
            return List.of(new NameReach.CaseStanding(assuming, path));
        }
        List<NameReach.CaseStanding> out = new ArrayList<>();
        for (NameReach.CaseStanding each : under) {
            if (assuming.merge(each.assuming()) instanceof Requirements.Merge.Merged(
                    Requirements both)) {
                out.addAll(standingsOf(reach, each.position(), both, crossed + 1));
            }
        }
        return out;
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
