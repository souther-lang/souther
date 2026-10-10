package souther.compiler.partition;

import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.TermPath;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Which value each {@code Bool} position inside an element is asked to hold, and which case each
 * value inside one is asked to be — what a way asks of the elements of its containers that no
 * region places.
 *
 * <p>Apart from what the way asks of the row ({@link TruthsAsked}, {@link Requirements}), because
 * the two say different things where they cannot hold together. Two values asked of one position
 * of the row are a way no row takes. Two values asked of a position inside an element are two
 * elements, and a row whose elements differ meets both — so where these cannot be written
 * together, or beside what the row is asked, it is the composer, which writes the elements of a
 * container alike, that wrote no row, and never the model that has none.
 *
 * <p>Read off the demands and nowhere else: what some element meets ({@link RowDemand.Exists})
 * and what every element meets ({@link RowDemand.ForAll}), each a truth or a case of a position
 * inside the element.
 *
 * @param truths what each position is asked to hold, in the order the way asked them
 * @param cases  each case asked, in the order the way asked them
 */
record ElementWrites(List<RowDemand.ATruth> truths, List<RowDemand.InCases> cases) {

    ElementWrites {
        truths = List.copyOf(truths);
        cases = List.copyOf(cases);
    }

    /** What {@code way} asks of the elements of its containers. */
    static ElementWrites of(List<OnTheWay.TakenIn> way) {
        List<RowDemand.ATruth> truths = new ArrayList<>();
        List<RowDemand.InCases> cases = new ArrayList<>();
        for (OnTheWay.TakenIn each : way) {
            List<RowDemand.OfAnElement> asked = switch (each.demand()) {
                case RowDemand.Exists exists -> exists.ofAnElement();
                case RowDemand.ForAll every -> every.ofEachElement();
                case RowDemand.Relational _, RowDemand.ATruth _, RowDemand.SoMany _,
                     RowDemand.ForTheRun _ -> List.of();
            };
            for (RowDemand.OfAnElement one : asked) {
                switch (one) {
                    case RowDemand.ATruth truth -> truths.add(truth);
                    case RowDemand.InCases inCases -> cases.add(inCases);
                    case RowDemand.Relational _, RowDemand.SameAs _, RowDemand.DifferentFrom _,
                         RowDemand.WithinIt _ -> { }
                }
            }
        }
        return new ElementWrites(truths, cases);
    }

    /**
     * {@code asked} with every case asked here as well, or the position the two ask for two
     * cases: a value inside an element asked to be what another value there is not.
     */
    Requirements.Merge requiredBeside(Requirements asked) {
        Requirements out = asked;
        for (RowDemand.InCases each : cases) {
            Requirements.Merge both = out.merge(each.requirements());
            if (!(both instanceof Requirements.Merge.Merged(Requirements merged))) {
                return both;
            }
            out = merged;
        }
        return new Requirements.Merge.Merged(out);
    }

    /**
     * {@code asked} with every truth asked here as well, each at the position {@code standing}
     * says its name stands at — or the position asked for both values.
     */
    TruthsAsked.Merge truthsBeside(TruthsAsked asked, Map<TermPath, TermPath> standing) {
        List<RowDemand.ATruth> all = new ArrayList<>();
        asked.at().forEach((at, held) -> all.add(new RowDemand.ATruth(at, held)));
        for (RowDemand.ATruth each : truths) {
            all.add(new RowDemand.ATruth(standing.getOrDefault(each.at(), each.at()),
                    each.held()));
        }
        return TruthsAsked.of(all);
    }

    /** Every position a truth is asked at here, which a row writes a value at. */
    Set<TermPath> truthsAt() {
        Set<TermPath> out = new LinkedHashSet<>();
        truths.forEach(each -> out.add(each.at()));
        return out;
    }

    /** The position named where these could not be written beside what the row is asked, as a
     *  sentence an author reads. */
    static String writtenAlike(TermPath at) {
        return "`" + at + "` is asked of elements written alike to hold two values at once;"
                + " elements that differ may meet both";
    }
}
