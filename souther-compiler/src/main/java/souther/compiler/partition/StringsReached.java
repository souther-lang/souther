package souther.compiler.partition;

import souther.compiler.check.ProjectionEvidence;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.PositionBounds;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.types.ValueName;
import souther.compiler.values.AdmissibleSet;
import souther.compiler.values.TextExtents;
import souther.compiler.values.ValueSet;

import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.function.IntPredicate;

/**
 * What the strings an input holds reach, asked of the positions and never of an axis.
 *
 * <p>A line is drawn at a number by the rules around a string, which know nothing of the format
 * the string is in. Whether a row can be written at an edge on that number is a question about the
 * strings the position holds: a format leaves some lengths out, a set of every string but a few
 * leaves out the one string of a length, and a position none of whose strings is a value leaves
 * the input no value to write. Held by position, it is the same answer for an axis a declaration
 * measured and one a body measured for the first time.
 *
 * <p>Worked out when the input is read and held as the facts it comes to, not as the sets it was
 * worked out from: this travels in an answer, whose equality is what a later reading is compared
 * on, and a language is a machine nobody compares.
 *
 * <p>Four things are kept apart, because each is a different claim and the strings of a position
 * ({@link TextExtents}) are a bound on its values, which proves none of the others by itself. A
 * position's values are bounded by its strings. A value is shown to exist at a position when its
 * strings show one. A number of it is reached only if, besides that, the rules around the
 * position were read whole ({@link ProjectionEvidence}) and no rule on another number of the same
 * position keeps the two apart: a length of nought and a sum of sixty-five are each a number of
 * some string and of no one string together. And an input holds a value only where its positions
 * that every value has do; a position inside a collection or a case need hold none.
 *
 * @param mandatoryPositionsHoldAValue whether every position that every value of the input has is
 *                         shown to hold a value by strings whose rules were read whole. A row at an
 *                         edge is a whole value of the input, so a position such a value must have
 *                         and that is not shown to hold one leaves every edge of the input
 *                         unproved. It says nothing of the positions between which a rule relates,
 *                         and an input they leave empty is another question's
 * @param countsReached    the positions whose strings have a value of every sum of code points
 *                         and every count of a class, which no rule on the position bounds at all
 * @param lengthsReached   the lengths of a position the rules leave it, where every one is the
 *                         length of some value and no rule on another number of the position
 *                         bounds it
 */
public record StringsReached(boolean mandatoryPositionsHoldAValue,
                             Set<TermPath> countsReached, Set<NumericTerm> lengthsReached) {

    /** An input none of whose positions is a string. */
    public static final StringsReached NONE = new StringsReached(true, Set.of(), Set.of());

    private static final String STRING = "String";

    public StringsReached {
        countsReached = Set.copyOf(countsReached);
        lengthsReached = Set.copyOf(lengthsReached);
    }

    /**
     * Whether an edge at {@code term} is one a row could be written at, as far as the strings of
     * the input say: the input has a whole value, which is every position every value has holding
     * one, and the number is one its strings reach. Two claims, and neither stands for the other.
     */
    public boolean allowsAnEdgeAt(NumericTerm term, Collection<ExactRatio> linesOnIt) {
        return mandatoryPositionsHoldAValue && reaches(term) && linesFitAString(term, linesOnIt);
    }

    /**
     * Whether every line drawn on {@code term} is below the most a {@code String} has of it, so
     * that the value beside the line on its far side is one a string can have. Reaching every
     * number the rules leave is not reaching a number past what a string holds: the rules leave
     * every number from nought up, and a string holds no more than {@link
     * TextExtents#LONGEST_STRING} code points.
     *
     * @param linesOnIt where the lines drawn on {@code term} fall
     */
    private static boolean linesFitAString(NumericTerm term, Collection<ExactRatio> linesOnIt) {
        ExactRatio most = mostAStringHas(term);
        return most == null || linesOnIt.stream().allMatch(at -> at.compareTo(most) < 0);
    }

    /** The most of {@code term} a string has, or null where it is no number of a string. */
    private static ExactRatio mostAStringHas(NumericTerm term) {
        return switch (term) {
            case NumericTerm.CodePointValueSum _ -> ExactRatio.of(
                    TextExtents.LONGEST_STRING * Character.MAX_CODE_POINT);
            case NumericTerm.CodePointClassCount _ -> ExactRatio.of(TextExtents.LONGEST_STRING);
            case NumericTerm.TakenOf taken when isOfAString(taken) ->
                    ExactRatio.of(TextExtents.LONGEST_STRING);
            case NumericTerm.TakenOf _, NumericTerm.ValueOf _, NumericTerm.CodePointAt _,
                 NumericTerm.TakenOver _, NumericTerm.OfAnElementsNeighbours _,
                 NumericTerm.OccurrencesOfItsValue _, NumericTerm.OccurrencesOfAKey _,
                 NumericTerm.GatheredUnderItsKey _, NumericTerm.GatheredUnderAKey _ -> null;
        };
    }

    /** What the strings at {@code positions} reach. */
    static StringsReached of(List<Position> positions) {
        boolean holds = true;
        Set<TermPath> counts = new LinkedHashSet<>();
        Set<NumericTerm> lengths = new LinkedHashSet<>();
        for (Position each : positions) {
            ValueSet admitted = each.admitted().approximation();
            // Only a string has a length, and the other numbers of a position that has one are
            // numbers of its strings.
            boolean isString = each.bounds().stream().anyMatch(b -> isLength(b.term()));
            // A position none of whose strings is shown to be a value leaves the input none. And
            // the strings of one are a bound on its values, which a rule not read may refuse
            // altogether: a row is a value of every parameter, so what is shown is shown of the
            // strings of all of them, and a position that is not shown holds back every edge.
            if (isMandatory(each.path())) {
                holds &= TextExtents.shownToHoldAValue(admitted) && !each.nothingExists()
                        && (!isString || isReadWhole(each));
            }
            // What the strings reach is read off a set that is a bound, so it is claimed only of a
            // position whose rules were read whole.
            if (!isString || !isReadWhole(each) || each.nothingExists()) {
                continue;
            }
            if (TextExtents.reachesEveryCount(admitted) && bindsNothing(each, null)) {
                counts.add(each.path());
            }
            for (PositionBounds bounds : each.bounds()) {
                if (isLength(bounds.term()) && bindsNothing(each, bounds)
                        && reachesEveryLengthLeft(admitted, bounds)) {
                    lengths.add(bounds.term());
                }
            }
        }
        return new StringsReached(holds, counts, lengths);
    }

    /**
     * Whether what the strings of {@code at} are and what they come to are the whole of what the
     * rules leave it: the set of its values was read in full, or the bounds were shown to be the
     * whole of the rules. A set that may be wider has a value in it that a rule not read refuses,
     * and the strings of it prove no value exists.
     */
    private static boolean isReadWhole(Position at) {
        return at.admitted().completeness() instanceof AdmissibleSet.Completeness.Complete
                || at.projection() instanceof ProjectionEvidence.CertifiedExact;
    }

    /**
     * Whether every value of the input has something at {@code path}: it is reached by fields
     * alone. A place inside a collection holds nothing when the collection does, and a place in a
     * case is not there in a value of another.
     */
    private static boolean isMandatory(TermPath path) {
        return path.steps().stream().allMatch(step -> step instanceof TermPath.Step.Field);
    }

    /**
     * Whether no rule of {@code at} bounds a number other than {@code own}. Where one does, a
     * number reached when asked alone may be reached by no string that keeps the rule's number
     * where it is held.
     */
    private static boolean bindsNothing(Position at, PositionBounds own) {
        for (PositionBounds other : at.bounds()) {
            if (other != own && !leavesEveryCount(other.rangeLeft())) {
                return false;
            }
        }
        return true;
    }

    /**
     * Whether {@code left} rules out no whole number from nought up, which is every number a
     * string has of any of its measures. Nought is the floor of all of them, so a range starting
     * there says nothing a number did not already.
     */
    private static boolean leavesEveryCount(NumericDomain.Bounds left) {
        if (left == null) {
            return true;
        }
        // An end that is not a count is a number of something other than a string's, which this
        // knows nothing of: it is taken as a rule.
        if (left.max() != null) {
            return false;
        }
        return left.min() == null
                || (left.min().at() instanceof Count count
                        && count.exactly().compareTo(ExactRatio.of(0)) <= 0);
    }

    /**
     * Whether every number {@code term} can take of the strings where it is read is the number of
     * some value there. True of a term this has no say in: what it reaches is another reading's.
     */
    public boolean reaches(NumericTerm term) {
        return switch (term) {
            case NumericTerm.TakenOf taken when isLength(taken) -> lengthsReached.contains(term)
                    || countsReached.contains(taken.position());
            // Any other number a string operation answers is shown only of strings nothing binds.
            case NumericTerm.TakenOf taken when isOfAString(taken) ->
                    countsReached.contains(taken.position());
            case NumericTerm.CodePointClassCount count -> countsReached.contains(count.position());
            case NumericTerm.CodePointValueSum sum -> countsReached.contains(sum.position());
            case NumericTerm.TakenOf _, NumericTerm.ValueOf _, NumericTerm.CodePointAt _,
                 NumericTerm.TakenOver _, NumericTerm.OfAnElementsNeighbours _,
                 NumericTerm.OccurrencesOfItsValue _, NumericTerm.OccurrencesOfAKey _,
                 NumericTerm.GatheredUnderItsKey _, NumericTerm.GatheredUnderAKey _ -> true;
        };
    }

    private static boolean isLength(NumericTerm term) {
        return term instanceof NumericTerm.TakenOf taken
                && taken.operation().equals(ValueName.Stdlib.operation(STRING, "length"));
    }

    /** Whether the number is what an operation of {@code String} answers. */
    private static boolean isOfAString(NumericTerm.TakenOf taken) {
        return taken.operation().alias().equals(STRING);
    }

    /**
     * Whether every length the rules leave the number {@code bounds} is about is the length of a
     * value of {@code at}.
     *
     * <p>The lengths the rules leave are what the numeric reading holds of it, which is the lengths
     * a rule written as a bound on the length excludes and nothing a format excludes: a format is
     * a bound on the strings, and the numbers around it do not know it. An edge can be at any of
     * them, so each has to be a length some value has.
     */
    private static boolean reachesEveryLengthLeft(ValueSet at, PositionBounds bounds) {
        NumericDomain.Bounds left =
                bounds.rangeLeft() == null ? NumericDomain.Bounds.OPEN : bounds.rangeLeft();
        IntPredicate wanted = each -> each >= 0 && left.admits(ExactRatio.of(each));
        return TextExtents.reachesEveryLength(at, wanted, left.max() == null);
    }
}
