package souther.compiler.partition;

import souther.compiler.meaning.OnOneElement;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.meaning.TheElementComesRound;
import souther.compiler.numeric.Congruences;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.numeric.WholeNumberRuns;
import souther.compiler.types.Type;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * What the statements only a run checks that a case of where a line decides puts on the way say
 * of the input's numbers, where one of them holds the case's element to one class and others
 * weigh it only in their remainders.
 *
 * <p>A statement of what a division leaves of the element alone, weighed by a whole number and
 * moved by one, against a number holds the element to the numbers some classes leave; where that
 * is one class, every element the statement admits is a member of it. A statement whose
 * remainders weighing the element come round over as few elements as the members are apart
 * ({@link TheElementComesRound#inItsRemainders}) leaves at every member what it leaves at any one
 * of them, so put at a member in its remainders ({@link OnOneElement#inItsRemainders}) it is a
 * statement every run passing both meets. Where that is a remainder of the input's numbers alone
 * against a number, what it leaves of the remainder is a condition on the input
 * ({@link RowDemand.OnARemainder}) — put on the way beside the statement, naming the statements it
 * follows from.
 *
 * <p>Only within one case, and only of a case weighing one element: the case is read at one
 * element wherever it weighs it ({@link ACaseAskedAtSomeElement}), so its statements are of one
 * value. What else is on the way may weigh the same binding at another application, and nothing
 * here reads it beside these.
 *
 * <p>Only what follows, and never in place of the statements: each is still the run's to check.
 * A class that is the element's beside the input's numbers, an element of something other than
 * whole numbers, a statement that weighs the element anywhere but its remainders, or one whose
 * remainders come round over more elements than the members are apart, says nothing here. Nor
 * does a class no element is in, or a statement leaving no remainder at the class: no condition
 * on the input says that, and the run is left to find it.
 */
final class RemaindersOfAnElement {

    private RemaindersOfAnElement() {
    }

    /**
     * {@code entries}, what {@code decides} puts on the way, with each condition on the input
     * that follows from its statements put beside the statement it follows from — inside an
     * alternative where that statement is, from the classes said beside the alternative and in it.
     * The entries themselves where {@code decides} weighs no one element.
     */
    static List<OnTheWay> withWhatFollows(Proposition decides, List<OnTheWay> entries) {
        return withWhatFollows(decides, entries, new Kept());
    }

    /**
     * {@link #withWhatFollows(Proposition, List)}, with what a statement put at the members of a
     * class leaves taken from {@code kept} where it was read for a case before.
     */
    static List<OnTheWay> withWhatFollows(Proposition decides, List<OnTheWay> entries, Kept kept) {
        Optional<Quantity.OfABinding> element = OnOneElement.theElementOf(decides);
        if (element.isEmpty()) {
            return entries;
        }
        return along(entries, element.get(), null, List.of(), kept);
    }

    /**
     * What each statement put at the members of a class leaves of a remainder of the input's
     * numbers, kept for the cases that put it there again: that is read off the statement, the
     * element and the class, and not off what else a case put beside it.
     */
    static final class Kept {

        private final Map<AtTheMembers, Optional<Left>> left = new HashMap<>();

        /** A statement put at the members of a class of an element. */
        private record AtTheMembers(Proposition.Compared stated, Quantity.OfABinding element,
                                    Congruences members) {}

        /** What a statement put at the members leaves of a remainder of the input's numbers. */
        private record Left(Quantity.RemainderOfADividend remainder, WholeNumberRuns leaves) {}
    }

    /**
     * {@code entries} with what follows put beside each statement, the element held to
     * {@code members} by {@code holding} before them — or to no class, where {@code members} is
     * null.
     */
    private static List<OnTheWay> along(List<OnTheWay> entries, Quantity.OfABinding element,
                                        Congruences members, List<RowDemand.ForTheRun> holding,
                                        Kept kept) {
        List<RowDemand.ForTheRun> held = new ArrayList<>(holding);
        Congruences in = members;
        for (OnTheWay entry : entries) {
            if (entry instanceof OnTheWay.TakenIn(var _, RowDemand.ForTheRun run)
                    && classOf(run, element) instanceof Congruences one) {
                Congruences both = in == null ? one : in.meet(one);
                if (both == null) {
                    return entries;
                }
                in = both;
                held.add(run);
            }
        }
        if (in == null) {
            return entries;
        }
        List<OnTheWay> out = new ArrayList<>(entries.size());
        boolean changed = false;
        for (OnTheWay entry : entries) {
            out.add(entry);
            if (entry instanceof OnTheWay.TakenIn(var anchor, RowDemand.ForTheRun run)
                    && putAt(run, element, in, held, kept)
                            instanceof RowDemand.OnARemainder follows) {
                out.add(new OnTheWay.TakenIn(anchor, follows));
                changed = true;
            } else if (entry instanceof OnTheWay.OneOf several) {
                List<List<OnTheWay>> ways = new ArrayList<>();
                boolean inside = false;
                for (List<OnTheWay> way : several.alternatives()) {
                    List<OnTheWay> each = along(way, element, in, held, kept);
                    inside |= each != way;
                    ways.add(each);
                }
                if (inside) {
                    out.set(out.size() - 1, OnTheWay.OneOf.of(several.condition(),
                            several.anchor(), ways, several.stated()));
                    changed = true;
                }
            }
        }
        return changed ? List.copyOf(out) : entries;
    }

    /**
     * The class {@code run} holds {@code element} to, where it states what a division leaves of
     * the element alone, weighed by a whole number and moved by one, against a number, and that
     * leaves one remainder — or null where it states no such thing, or leaves no class.
     */
    private static Congruences classOf(RowDemand.ForTheRun run, Quantity.OfABinding element) {
        if (!(run.statement() instanceof Proposition.Compared(Relation.Affine affine,
                boolean holds, var _))
                || affine.form().coefs().size() != 1
                || !(affine.form().coefs().keySet().iterator().next()
                        instanceof Quantity.RemainderOfADividend remainder)
                || remainder.dividend().coefs().size() != 1
                || !element.equals(remainder.dividend().coefs().keySet().iterator().next())
                || !element.type().equals(Type.INT)
                || !(whole(remainder.dividend().coefs().get(element)) instanceof BigInteger weight)
                || !(whole(remainder.dividend().constant()) instanceof BigInteger moved)) {
            return null;
        }
        Rel met = holds ? affine.proposition() : affine.proposition().denied();
        WholeNumberRuns leaves = RowDemand.OnARemainder.meeting(affine, met);
        if (leaves == null || leaves.runs().size() != 1
                || !leaves.runs().getFirst().isOneNumber()) {
            return null;
        }
        return Congruences.solving(weight, moved.subtract(leaves.runs().getFirst().from()),
                remainder.divisor());
    }

    /**
     * What {@code run} leaves of a remainder of the input's numbers alone with {@code element} at
     * the members of {@code members}, following from it and {@code holding} — or null where it is
     * no such statement there, or leaves none.
     */
    private static RowDemand.OnARemainder putAt(RowDemand.ForTheRun run,
                                                Quantity.OfABinding element,
                                                Congruences members,
                                                List<RowDemand.ForTheRun> holding, Kept kept) {
        if (holding.contains(run) || !(run.statement() instanceof Proposition.Compared stated)) {
            return null;
        }
        Optional<Kept.Left> left = kept.left.computeIfAbsent(
                new Kept.AtTheMembers(stated, element, members),
                _ -> Optional.ofNullable(leftAt(stated, element, members)));
        if (left.isEmpty()) {
            return null;
        }
        List<RowDemand.ForTheRun> from = new ArrayList<>(holding);
        from.add(run);
        return new RowDemand.OnARemainder(left.get().remainder(), left.get().leaves(), from);
    }

    /**
     * What {@code stated} leaves of a remainder of the input's numbers alone with
     * {@code element} at the members of {@code members}, or null where it is no such statement
     * there, or leaves none.
     */
    private static Kept.Left leftAt(Proposition.Compared stated, Quantity.OfABinding element,
                                    Congruences members) {
        if (!(TheElementComesRound.inItsRemainders(stated).orElse(null)
                        instanceof TheElementComesRound round)
                || !round.element().equals(element)
                || members.modulus().mod(round.every()).signum() != 0) {
            return null;
        }
        if (!(OnOneElement.inItsRemainders(stated, element,
                LinearForm.constant(ExactRatio.of(members.residue())))
                instanceof Proposition.Compared(Relation.Affine affine, boolean holds, var _))
                || affine.form().coefs().size() != 1
                || !(affine.form().coefs().keySet().iterator().next()
                        instanceof Quantity.RemainderOfADividend remainder)
                || remainder.overTheInput() == null) {
            return null;
        }
        WholeNumberRuns leaves = RowDemand.OnARemainder.meeting(affine,
                holds ? affine.proposition() : affine.proposition().denied());
        if (leaves == null || leaves.isNone()) {
            return null;
        }
        return new Kept.Left(remainder, leaves);
    }

    /** {@code ratio} as a whole number, or null where it is none. */
    private static BigInteger whole(ExactRatio ratio) {
        return ratio.isWhole() && ratio.floor() instanceof ExactAnswer.Held<BigInteger>(var held)
                ? held : null;
    }
}
