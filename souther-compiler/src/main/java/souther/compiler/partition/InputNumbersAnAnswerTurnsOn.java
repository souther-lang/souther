package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.meaning.AnswerAsAnInput;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * The numbers of the input a statement about an answer turns on, put at values before the answer is
 * composed.
 *
 * <p>Which value a dependency has to answer with is a function of what the row writes at the
 * input: "some element is at most {@code on}" is met by an element for one {@code on} and by
 * another for the next. Composed apart from the row, the answer would be a value for a row nobody
 * wrote. So the numbers are put at values first, the answer is composed for those, and the row is
 * held to the same values — a pair that meets the statement together, which neither half composed
 * alone could promise.
 *
 * <p><b>One value for each number, taken from what the way leaves it.</b> A value outside what the
 * rules on the way allow is a row that does not arrive, so each is looked for among the ones the
 * region of the way holds, and put only where the region takes the pin in. Where none is, the
 * number is left out and the statement is one no value was composed against: said by the caller in
 * the words it already has, and not read as the statement having no value.
 *
 * <p>A search and not a proof. The first value that serves is the one taken, so a statement that
 * needs another is one this composes nothing for, and what comes back says nothing about whether a
 * value exists.
 */
public final class InputNumbersAnAnswerTurnsOn {

    private final Map<NumericTerm, ExactRatio> values;
    private final Reachability.Reaching reaching;

    private InputNumbersAnAnswerTurnsOn(Map<NumericTerm, ExactRatio> values,
                                        Reachability.Reaching reaching) {
        this.values = Collections.unmodifiableMap(new LinkedHashMap<>(values));
        this.reaching = reaching;
    }

    /** The value each number was put at. */
    public Map<NumericTerm, ExactRatio> values() {
        return values;
    }

    /** The way, with each of those numbers held at its value. */
    public Reachability.Reaching reaching() {
        return reaching;
    }

    /**
     * The numbers {@code demands} turn on, put at values the way leaves them.
     *
     * <p>The way itself where no statement names a number of the input, which is every way over an
     * answer alone.
     */
    public static InputNumbersAnAnswerTurnsOn of(AnswersDemanded demands,
                                                 Reachability.Reaching reaching) {
        Set<NumericTerm> terms = new LinkedHashSet<>();
        ConditionReportAnchor anchor = null;
        for (AnswerDemand each : demands.stated()) {
            if (!(each instanceof AnswerDemand.AStatement statement)) {
                continue;
            }
            Set<NumericTerm> named = AnswerAsAnInput.inputNumbersIn(statement.statement());
            if (named != null && !named.isEmpty()) {
                terms.addAll(named);
                anchor = anchor == null ? statement.anchor() : anchor;
            }
        }
        if (terms.isEmpty()) {
            return new InputNumbersAnAnswerTurnsOn(Map.of(), reaching);
        }
        SearchRegion region = reaching.region();
        Map<NumericTerm, ExactRatio> values = new LinkedHashMap<>();
        List<OnTheWay.TakenIn> held = new ArrayList<>();
        for (NumericTerm term : terms) {
            for (ExactRatio candidate : candidatesFor(region, term)) {
                LinearForm<NumericTerm> pin = new LinearForm<>(candidate.negated(),
                        Map.of(term, ExactRatio.ONE));
                if (region.assuming(pin, Rel.EQ) instanceof SearchRegion.Assumption.Taken(
                        SearchRegion narrowed)) {
                    region = narrowed;
                    values.put(term, candidate);
                    held.add(new OnTheWay.TakenIn(anchor, new RowDemand.Relational(
                            new TakenConstraint.Affine(pin, Rel.EQ))));
                    break;
                }
            }
        }
        List<OnTheWay.TakenIn> cuts = new ArrayList<>(reaching.boundedOnTheWay());
        cuts.addAll(held);
        return new InputNumbersAnAnswerTurnsOn(values, new Reachability.Reaching(region,
                reaching.requirements(), reaching.truths(), cuts, reaching.ways()));
    }

    /**
     * The values {@code term} may be put at, in the order they are tried: the ends of what the way
     * holds of it, the values just inside them, and then nought and one.
     */
    private static List<ExactRatio> candidatesFor(SearchRegion region, NumericTerm term) {
        if (!(region.projectionOf(term)
                instanceof NumericDomain.FormProjection.Within(NumericDomain.Bounds bounds))) {
            return List.of();
        }
        List<ExactRatio> out = new ArrayList<>();
        if (bounds.min() != null && bounds.min().at() instanceof Count low) {
            out.add(low.exactly());
            out.add(low.plus(1).exactly());
        }
        if (bounds.max() != null && bounds.max().at() instanceof Count high) {
            out.add(high.exactly());
            out.add(high.minus(1).exactly());
        }
        out.add(ExactRatio.ZERO);
        out.add(ExactRatio.ONE);
        List<ExactRatio> inside = new ArrayList<>();
        for (ExactRatio each : out) {
            if (!inside.contains(each) && admits(bounds, each)) {
                inside.add(each);
            }
        }
        return inside;
    }

    private static boolean admits(NumericDomain.Bounds bounds, ExactRatio value) {
        return Count.written(value) instanceof ExactAnswer.Held<Optional<Count>>(var written)
                && written.isPresent() && bounds.admits(written.get());
    }
}
