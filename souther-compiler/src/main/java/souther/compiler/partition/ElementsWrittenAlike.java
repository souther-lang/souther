package souther.compiler.partition;

import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.TermPath;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * The ways a row whose containers' elements are written alike meets what its way asks of the
 * elements, where an element may meet some of it several ways ({@link RowDemand.AnElementMeets}).
 *
 * <p>A composer writing the elements of a container alike writes one element into every one of
 * them, so it meets a demand of several ways by choosing one of them, and every demand on the same
 * container by choosing ways one element meets together. Each such choice is a way of its own:
 * the demands rewritten to the way chosen, which every reader composing alike reads as it stands.
 *
 * <p>Ways no one element meets together are left out — two cases asked of one position inside
 * it, a truth and its denial, relations nothing the rules leave meets at once. Left out and not
 * proved closed: elements that differ may meet both, so what is said of a row past them is that
 * the elements were written alike, never that no row is ({@link ReachabilityGap.Why.ElementsWrittenAlike}).
 */
final class ElementsWrittenAlike {

    private ElementsWrittenAlike() {
    }

    /**
     * The ways of writing a way's elements alike that were looked along, and the figure that
     * stopped the looking where one did — which the way composed as it stands past them says,
     * since along a way left out its elements would have been written against more.
     *
     * @param ways      each way that one element may meet, as the way with every demand of several
     *                  ways rewritten to one of them
     * @param stoppedBy the figure the looking stopped at, or null where every way was looked at
     */
    record Choices(List<Reachability.Reaching> ways, CompositionBudget stoppedBy) {

        static final Choices NONE = new Choices(List.of(), null);

        Choices {
            ways = List.copyOf(ways);
        }
    }

    /**
     * Each way of writing {@code reaching}'s elements alike that one element may meet; none where
     * it has no such demand, or where no way is one an element meets.
     */
    static Choices of(Reachability.Reaching reaching) {
        if (reaching.boundedOnTheWay().stream()
                .allMatch(cut -> RowDemand.writtenAlikeAsItStands(cut.demand()))) {
            return Choices.NONE;
        }
        OneOfEach.Walked<OnTheWay.TakenIn> walked = OneOfEach.walk(reaching.boundedOnTheWay(),
                new OneElement(reaching), CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT,
                CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG);
        List<Reachability.Reaching> out = new ArrayList<>();
        for (List<OnTheWay.TakenIn> way : walked.ways()) {
            out.add(new Reachability.Reaching(reaching.region(), reaching.requirements(),
                    reaching.truths(), way, reaching.ways(), reaching.declined()));
        }
        return new Choices(out, walked.stoppedBy());
    }

    /**
     * What the elements written alike are asked so far: the cases the row and its elements are
     * required to be, the truths asked inside an element, and the relations asked of the element of
     * each container.
     */
    private record Written(Requirements required, List<RowDemand.ATruth> truths,
                           Map<TermPath, List<TakenConstraint>> relations) {}

    /** The demands of a way as one element written into every element of a container meets
     *  them. */
    private record OneElement(Reachability.Reaching reaching)
            implements OneOfEach.Vocabulary<OnTheWay.TakenIn, Written> {

        @Override
        public List<List<OnTheWay.TakenIn>> alternatives(OnTheWay.TakenIn entry) {
            if (RowDemand.writtenAlikeAsItStands(entry.demand())) {
                return null;
            }
            List<List<OnTheWay.TakenIn>> out = new ArrayList<>();
            switch (entry.demand()) {
                // One way of it is less than the statement, so it is no count of the statement.
                case RowDemand.Exists(var container, var meets, var holdingOne, var _) -> {
                    for (List<RowDemand.OfAnElement> way : meets.ways()) {
                        out.add(List.of(new OnTheWay.TakenIn(entry.anchor(),
                                new RowDemand.Exists(container,
                                        RowDemand.AnElementMeets.only(way), holdingOne,
                                        Optional.empty()))));
                    }
                }
                case RowDemand.ForAll(var container, var meets, var holdingNone, var _) -> {
                    for (List<RowDemand.OfAnElement> way : meets.ways()) {
                        out.add(List.of(new OnTheWay.TakenIn(entry.anchor(),
                                new RowDemand.ForAll(container,
                                        RowDemand.AnElementMeets.only(way), holdingNone,
                                        Optional.empty()))));
                    }
                }
                case RowDemand.Relational _, RowDemand.ATruth _, RowDemand.SoMany _,
                     RowDemand.ForTheRun _ -> throw new IllegalStateException(
                        "a demand of one way is written as it stands: " + entry);
            }
            return out;
        }

        @Override
        public Set<TermPath> positions(OnTheWay.TakenIn entry) {
            return entry.demand().positions();
        }

        @Override
        public Written nothing() {
            return new Written(reaching.requirements(), List.of(), Map.of());
        }

        @Override
        public Written with(Written so, OnTheWay.TakenIn entry) {
            TermPath container;
            List<RowDemand.OfAnElement> asked;
            switch (entry.demand()) {
                case RowDemand.Exists exists -> {
                    container = exists.container();
                    asked = exists.ofAnElement().theWay();
                }
                case RowDemand.ForAll every -> {
                    container = every.container();
                    asked = every.ofEachElement().theWay();
                }
                case RowDemand.Relational _, RowDemand.ATruth _, RowDemand.SoMany _,
                     RowDemand.ForTheRun _ -> {
                    return so;
                }
            }
            Requirements required = so.required();
            List<RowDemand.ATruth> truths = new ArrayList<>(so.truths());
            List<TakenConstraint> relations =
                    new ArrayList<>(so.relations().getOrDefault(container, List.of()));
            int had = relations.size();
            for (RowDemand.OfAnElement each : asked) {
                switch (each) {
                    case RowDemand.InCases cases -> {
                        if (!(required.merge(cases.requirements())
                                instanceof Requirements.Merge.Merged(Requirements both))) {
                            return null;
                        }
                        required = both;
                    }
                    case RowDemand.ATruth truth -> truths.add(truth);
                    case RowDemand.Relational(var relation) -> relations.add(relation);
                    case RowDemand.SameAs _, RowDemand.DifferentFrom _, RowDemand.KeyedAs _,
                         RowDemand.NotKeyedAs _, RowDemand.WithinIt _ -> { }
                }
            }
            if (!(TruthsAsked.of(truths) instanceof TruthsAsked.Merge.Merged)) {
                return null;
            }
            if (relations.size() > had
                    && TakenConstraint.nothingMeetsAll(relations, reaching.region())) {
                return null;
            }
            Map<TermPath, List<TakenConstraint>> byContainer = new LinkedHashMap<>(so.relations());
            byContainer.put(container, List.copyOf(relations));
            return new Written(required, List.copyOf(truths), byContainer);
        }
    }
}
