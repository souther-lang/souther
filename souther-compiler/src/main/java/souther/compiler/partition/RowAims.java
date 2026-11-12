package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;
import souther.compiler.numeric.ValueTransformation;
import souther.compiler.semantics.TakenAs;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * What the conditions a run to a comparison gets past ask of the collections of a row, as numbers
 * a collection is to hold: a total off nought is asked of a list as a list holding a number off
 * nought.
 *
 * <p>An aim is a request for a row to try and never a statement about the model. A row built to
 * one is run, and it is the run that says whether the comparison is reached; an aim nothing
 * builds, or one no run gets past, says nothing of whether a row exists.
 *
 * <p>Only a condition over one total of one list is read, since what a list holding one element
 * totals is that element, and what a condition over several numbers asks is not what a one-element
 * list can answer. The numbers offered are those next to where the condition turns, each held to
 * the condition itself.
 */
final class RowAims {

    private RowAims() {}

    /**
     * A collection and the numbers it is asked to hold, one at a time.
     *
     * @param container the collection, by the parameter it is in and the fields down to it
     * @param elements  the numbers, each of which a collection holding it alone totals to
     */
    record Aim(TermPath container, List<BigInteger> elements) {

        Aim {
            elements = List.copyOf(elements);
        }
    }

    /** The collections {@code conditions} ask something of, in the order first asked. */
    static List<Aim> of(List<TakenConstraint> conditions) {
        Map<TermPath, List<BigInteger>> asked = new LinkedHashMap<>();
        for (TakenConstraint each : conditions) {
            if (!(each instanceof TakenConstraint.Affine(var form, var rel, var _))
                    || form.coefs().size() != 1) {
                continue;
            }
            Map.Entry<NumericTerm, ExactRatio> only = form.coefs().entrySet().iterator().next();
            TermPath container = totalOfAList(only.getKey());
            if (container == null) {
                continue;
            }
            List<BigInteger> numbers = asked.computeIfAbsent(container, _ -> new ArrayList<>());
            for (BigInteger number : near(form.constant(), only.getValue(), rel)) {
                if (!numbers.contains(number)) {
                    numbers.add(number);
                }
            }
        }
        List<Aim> out = new ArrayList<>();
        asked.forEach((container, numbers) -> {
            if (!numbers.isEmpty()) {
                out.add(new Aim(container, numbers));
            }
        });
        return out;
    }

    /** The list {@code term} is the total of, or null where it is no such total. */
    private static TermPath totalOfAList(NumericTerm term) {
        TermPath subject = switch (term) {
            case NumericTerm.TakenOf of
                    when of.takenAs() instanceof TakenAs.TheSumOfWhatItHolds
                            && ValueTransformation.NONE.equals(of.transformation()) ->
                    of.position();
            case NumericTerm.TakenOver over
                    when over.takenAs() instanceof TakenAs.TheSumOfWhatItHolds
                            && over.source() instanceof RunSource.ProjectedOccurrences ->
                    over.subjectPath();
            default -> null;
        };
        if (subject == null) {
            return null;
        }
        List<TermPath.Step> steps = subject.steps();
        if (steps.isEmpty() || !(steps.getLast() instanceof TermPath.Step.Element)) {
            return subject;
        }
        return TermPath.of(subject.head(), steps.subList(0, steps.size() - 1));
    }

    /**
     * The whole numbers next to where {@code constant + weight * number rel 0} turns that meet it:
     * the ones either side of {@code -constant / weight}, and it itself where it is whole.
     */
    private static List<BigInteger> near(ExactRatio constant, ExactRatio weight, Rel rel) {
        if (weight.isZero()
                || !(constant.negated().dividedBy(weight)
                        instanceof ExactAnswer.Held<ExactRatio>(ExactRatio turns))
                || !(turns.floor() instanceof ExactAnswer.Held<BigInteger>(BigInteger below))
                || !(turns.ceiling() instanceof ExactAnswer.Held<BigInteger>(BigInteger above))) {
            return List.of();
        }
        List<BigInteger> out = new ArrayList<>();
        for (BigInteger number : List.of(below.subtract(BigInteger.ONE), below, above,
                above.add(BigInteger.ONE))) {
            if (!out.contains(number) && meets(constant, weight, rel, number)) {
                out.add(number);
            }
        }
        return out;
    }

    private static boolean meets(ExactRatio constant, ExactRatio weight, Rel rel,
                                 BigInteger number) {
        return weight.times(ExactRatio.of(number)) instanceof ExactAnswer.Held<ExactRatio>(
                    ExactRatio scaled)
                && constant.plus(scaled) instanceof ExactAnswer.Held<ExactRatio>(
                        ExactRatio value)
                && rel.holds(value.signum());
    }
}
