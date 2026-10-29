package souther.compiler.partition;

import souther.compiler.check.ProjectionEvidence;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.PositionBounds;
import souther.compiler.inputs.RepresentationBounds;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.regex.Language;
import souther.compiler.regex.PatternPlan;
import souther.compiler.values.AdmissibleSet;
import souther.compiler.values.ValueSet;

import net.unit8.notation199x.pattern.Meter;

import java.math.BigInteger;

/**
 * The strings a position holds, as far as they are shown to be all of them.
 *
 * <p>A position's set of values is read from the rules about its strings, and a rule about the
 * length of a string is a bound on a number the set does not read. Such a position is left wider
 * than it is by the set alone, and the bounds on the length are the rest of what the rules say: the
 * strings it holds are the strings of the set that have a length the bounds leave. That is shown
 * only where the bounds are shown to be the whole of the rules, the length is the one number they
 * bound, and no rule of a value the position sits in ties it to another place. Otherwise nothing
 * is said of the strings.
 *
 * <p>Asked in one place, so that what a relation is read over is the same strings wherever it is
 * asked.
 */
final class StringsHeld {

    private StringsHeld() { }

    /**
     * The strings {@code at} holds, or null where they are not shown to be all of them.
     *
     * <p>Null is that nothing is shown, and not that the position holds more.
     *
     * @param tiedToNothing whether no rule of a value the position sits in names it
     */
    static ValueSet at(Position at, boolean tiedToNothing) {
        ValueSet admitted = at.admitted().approximation();
        if (at.admitted().completeness() instanceof AdmissibleSet.Completeness.Complete) {
            return admitted;
        }
        if (!tiedToNothing || !(at.projection() instanceof ProjectionEvidence.CertifiedExact)) {
            return null;
        }
        Language language = UndividedByARelation.languageOf(admitted);
        Meter meter = PatternPlan.Budget.OF_THE_PIECES_OF_A_LANGUAGE.meter();
        for (PositionBounds each : at.bounds()) {
            if (language == null) {
                return null;
            }
            if (!(each.term() instanceof NumericTerm.TakenOf taken)
                    || !RepresentationBounds.isALength(taken)) {
                continue;
            }
            LengthsPastTheWay.Lengths lengths = lengthsOf(each.rangeLeft());
            if (lengths == null || !StringsReached.bindsNothing(at, each)) {
                return null;
            }
            language = Partitions.ofTheLengths(language, lengths, meter);
        }
        return language == null ? null : ValueSet.matching(language);
    }

    /** The lengths {@code bounds} leave, or null where an end is not a whole count. */
    private static LengthsPastTheWay.Lengths lengthsOf(NumericDomain.Bounds bounds) {
        if (bounds == null) {
            return new LengthsPastTheWay.Lengths(null, null);
        }
        BigInteger least = null;
        BigInteger most = null;
        if (bounds.min() != null) {
            least = fewestFrom(bounds.min());
            if (least == null) {
                return null;
            }
        }
        if (bounds.max() != null) {
            most = mostUpTo(bounds.max());
            if (most == null) {
                return null;
            }
        }
        return new LengthsPastTheWay.Lengths(least, most);
    }

    /** The fewest code points the end lets a string have, or null where it is no count. */
    private static BigInteger fewestFrom(Endpoint end) {
        if (!(end.at() instanceof Count count)
                || !(count.exactly().ceiling() instanceof ExactAnswer.Held<BigInteger>(
                        BigInteger whole))) {
            return null;
        }
        return count.exactly().isWhole() && !end.inclusive() ? whole.add(BigInteger.ONE) : whole;
    }

    /** The most code points the end lets a string have, or null where it is no count. */
    private static BigInteger mostUpTo(Endpoint end) {
        if (!(end.at() instanceof Count count)
                || !(count.exactly().floor() instanceof ExactAnswer.Held<BigInteger>(
                        BigInteger whole))) {
            return null;
        }
        return count.exactly().isWhole() && !end.inclusive() ? whole.subtract(BigInteger.ONE)
                : whole;
    }
}
