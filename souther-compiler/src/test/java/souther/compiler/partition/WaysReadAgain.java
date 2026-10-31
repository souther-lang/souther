package souther.compiler.partition;

import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * Ways past the figure made of choices of truths, read again for a relation on {@code x} and
 * {@code y}: what the reading again does with its choices, with nothing of a model beside them.
 *
 * <p>A truth is in no region and asked of no rule here, so whether what a choice asks apart is met
 * turns on the truths alone: every truth a choice made by {@link #met} asks holds beside every
 * other, and a choice made by {@link #notMet} asks one to fail that the way asks to hold.
 */
final class WaysReadAgain {

    /** The positions the relation reads. */
    static final TermPath X = TermPath.of("x");
    static final TermPath Y = TermPath.of("y");

    /** An element of the list {@code xs}, which two conditions on a way may each ask of a
     *  different element. */
    static final TermPath AN_ELEMENT = TermPath.of("xs").element();

    /** How many {@code Bool}s the met choices ask of, each asked by several. */
    private static final int TRUTHS = 16;

    /** Nothing tied but a place and what is inside it, and no rule naming anything. */
    private static final AWayReadForARelation.Declarations NOTHING_DECLARED =
            new AWayReadForARelation.Declarations() {
                @Override
                public boolean tie(TermPath one, TermPath other) {
                    return one.isAtOrUnder(other) || other.isAtOrUnder(one);
                }

                @Override
                public boolean nameNothingAt(TermPath at) {
                    return true;
                }

                @Override
                public NumericDomain.Bounds leaveEveryValueBetween(NumericTerm term) {
                    return null;
                }

                @Override
                public boolean leaveAValueOf(TypeSymbol leaf) {
                    return true;
                }
            };

    private static final SearchRegion REGION = region();

    private WaysReadAgain() {}

    /** {@code way} read again for the relation, its choices the conditions of several ways on it. */
    static AWayReadForARelation.ReadAgain readAgain(List<OnTheWay> way) {
        return AWayReadForARelation.of(new Reachability.Ways.Whole(
                        way.stream().filter(OnTheWay::splitsTheWay).toList(),
                        CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG, List.of(),
                        new Reachability.ReadFrom(new WayToTheBorder(way), REGION)),
                Set.of(X, Y, AN_ELEMENT), NOTHING_DECLARED);
    }

    /** {@code count} choices of two truths each, every truth asked to hold, numbered from
     *  {@code from}. */
    static List<OnTheWay> met(int count, int from) {
        List<OnTheWay> out = new ArrayList<>();
        for (int at = from; at < from + count; at++) {
            ConditionReportAnchor anchor = anchor(at);
            out.add(OnTheWay.OneOf.of(occurrence(at), anchor, List.of(
                    List.of(truth(anchor, "t" + at % TRUTHS, true)),
                    List.of(truth(anchor, "t" + (at * 7 + 3) % TRUTHS, true))),
                    Optional.empty()));
        }
        return out;
    }

    /**
     * {@code count} choices numbered from {@code from}, each asking a truth of its own to fail
     * on every alternative, and before them the way asking each of those truths to hold.
     */
    static List<OnTheWay> notMet(int count, int from) {
        List<OnTheWay> out = new ArrayList<>();
        for (int at = from; at < from + count; at++) {
            out.add(truth(anchor(at), "u" + at, true));
        }
        for (int at = from; at < from + count; at++) {
            ConditionReportAnchor anchor = anchor(at);
            OnTheWay failing = truth(anchor, "u" + at, false);
            out.add(OnTheWay.OneOf.of(occurrence(at), anchor, List.of(
                    List.of(failing), List.of(failing, truth(anchor, "t0", true))),
                    Optional.empty()));
        }
        return out;
    }

    /** The choice numbered {@code at} of {@code alternatives}. */
    static OnTheWay oneOf(int at, List<List<OnTheWay>> alternatives) {
        return OnTheWay.OneOf.of(occurrence(at), anchor(at), alternatives, Optional.empty());
    }

    /** {@code weight * x rel threshold}, asked of a number the relation reads. */
    static OnTheWay x(long weight, Rel rel, long threshold) {
        return number(X, weight, rel, threshold);
    }

    /** {@code weight * y rel threshold}, asked of the other number the relation reads. */
    static OnTheWay y(long weight, Rel rel, long threshold) {
        return number(Y, weight, rel, threshold);
    }

    /** {@code weight * xs[*] rel threshold}, asked of an element the relation reads. */
    static OnTheWay anElement(long weight, Rel rel, long threshold) {
        return number(AN_ELEMENT, weight, rel, threshold);
    }

    private static OnTheWay number(TermPath at, long weight, Rel rel, long threshold) {
        return new OnTheWay.TakenIn(anchor(0), new RowDemand.Relational(new TakenConstraint.Affine(
                new LinearForm<>(ExactRatio.of(-threshold),
                        Map.of(new NumericTerm.ValueOf(at), ExactRatio.of(weight))), rel)));
    }

    /** The {@code Bool} at {@code at} asked to be {@code held}, apart from the relation. */
    static OnTheWay truth(String at, boolean held) {
        return truth(anchor(0), at, held);
    }

    private static ConditionOccurrence occurrence(int at) {
        return new ConditionOccurrence("f", ConditionOccurrence.Reading.DIVIDING, at);
    }

    private static ConditionReportAnchor anchor(int at) {
        return new ConditionReportAnchor.WhereTheReadingMetIt("m", occurrence(at));
    }

    private static OnTheWay truth(ConditionReportAnchor anchor, String at, boolean held) {
        return new OnTheWay.TakenIn(anchor, new RowDemand.ATruth(TermPath.of(at), held));
    }

    /** What the declarations leave the numbers the relation reads. */
    private static SearchRegion region() {
        Compilation compilation = Compilation.ofSource("""
                module m
                data Yes
                behavior f : (x: Int, y: Int, xs: List<Int>) -> Yes
                let f (x, y, xs) = Yes
                """, "Main");
        return compilation.db().ask(new Adequacy.Inputs("m")).value().get("f")
                .reading(RuleReadings.of(compilation, "m")).quantities().region();
    }
}
