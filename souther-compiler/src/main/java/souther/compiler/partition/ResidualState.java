package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.PositionsAStatementReads.ReadSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;
import souther.compiler.numeric.WholeNumberRuns;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;

/**
 * What the parts chosen come to for the cases still to choose, as a value two histories share
 * when they leave the same question.
 *
 * <p>Two things about the parts chosen are told apart from the history that chose them, and each
 * is replaced only by what leaves every case still to choose the same question it left: what
 * stands in for a part is exact, never what holds wherever the part does.
 *
 * <p>The remainders of one form by one divisor, moved by constants, are one fact about the
 * remainder of the form: the remainders of the form unmoved they leave, whichever of them said it,
 * as the way holds them ({@link RemaindersHeld}, {@link ARemainderMoved}). A statement the owner
 * of remainders does not read as one stands as it was said: held as the remainders it may leave,
 * it would be every remainder, and two that say different things would be one state.
 *
 * <p>That some element of a container is a date, or none is, is a fact about that date alone when
 * the container is held to nothing and the date is none that anything still to choose, or the
 * line, asks of it. Then the container can be made to hold the dates said to be in it and none of
 * those said not to be, whatever else is chosen, so the fact is eliminated, and what it leaves
 * behind is that each date said to be in it is a date. The dates are one base moved by numbers,
 * so that is the base moved by the least and by the greatest of them being dates: both ends are
 * kept. Anything this cannot show is no fact eliminated, and the parts stand as they were chosen.
 */
final class ResidualState {

    private ResidualState() {
    }

    /** What the parts chosen leave of each remainder of a form unmoved ({@link
     *  RemaindersHeld#left}). */
    record Residues(Map<ARemainderMoved.Unmoved, WholeNumberRuns> left) {}

    /** The nearest and the farthest the dates said to be in a container are moved from one base,
     *  as the constants {@code element + base + at == 0} holds them with. */
    record Ends(TermPath container, Map<Quantity, ExactRatio> base, ExactRatio least,
                ExactRatio greatest) {}

    /** That some element of {@code container} is the date {@code base} moved by {@code at}, or
     *  that none is. */
    private record Member(TermPath container, Map<Quantity, ExactRatio> base, ExactRatio at,
                          boolean holds) {}

    /**
     * What {@code bearing} comes to beside {@code remaining}, or none where it is not shown to
     * come to a value two histories can share.
     *
     * @param positionsOf   what whether a part holds turns on, null where it turns on something
     *                      no position or value bound says
     * @param held          what the way to the comparison and the line are about
     * @param holdsNothing  whether the container at a position is shown to be held to nothing
     */
    static Optional<Set<Object>> of(List<Proposition> bearing, List<Proposition> remaining,
                                    Function<Proposition, Set<ReadSubject>> positionsOf,
                                    Set<ReadSubject> held, Predicate<TermPath> holdsNothing) {
        RemaindersHeld residues = RemaindersHeld.NONE;
        List<Member> chosen = new ArrayList<>();
        Set<Object> out = new LinkedHashSet<>();
        TermPath container = null;
        for (Proposition part : bearing) {
            RowDemand.OnARemainder remainder = remainderOf(part);
            if (remainder != null) {
                switch (residues.taking(remainder)) {
                    case RemaindersHeld.Taken.Held(var taken) -> residues = taken;
                    // No row meets the parts chosen; nothing is shared with such a history.
                    case RemaindersHeld.Taken.NoneLeft _ -> {
                        return Optional.empty();
                    }
                }
                continue;
            }
            Member member = memberOf(part);
            if (member != null) {
                if (container != null && !container.equals(member.container())) {
                    return Optional.empty();
                }
                container = member.container();
                chosen.add(member);
                continue;
            }
            out.add(part);
        }
        if (!residues.left().isEmpty()) {
            out.add(new Residues(residues.left()));
        }
        if (chosen.isEmpty()) {
            return Optional.of(out);
        }
        if (!eliminated(container, chosen, out, remaining, positionsOf, held, holdsNothing)) {
            return Optional.empty();
        }
        ExactRatio least = null;
        ExactRatio greatest = null;
        for (Member each : chosen) {
            if (each.holds()) {
                least = least == null || each.at().compareTo(least) < 0 ? each.at() : least;
                greatest = greatest == null || each.at().compareTo(greatest) > 0 ? each.at()
                        : greatest;
            }
        }
        if (least != null) {
            out.add(new Ends(container, chosen.getFirst().base(), least, greatest));
        }
        return Optional.of(out);
    }

    /** Whether the dates in {@code chosen} are shown to be the container's to hold or not hold,
     *  whatever else is chosen. */
    private static boolean eliminated(TermPath container, List<Member> chosen, Set<Object> kept,
                                      List<Proposition> remaining,
                                      Function<Proposition, Set<ReadSubject>> positionsOf,
                                      Set<ReadSubject> held, Predicate<TermPath> holdsNothing) {
        if (!holdsNothing.test(container) || touches(held, container)) {
            return false;
        }
        Map<Quantity, ExactRatio> base = chosen.getFirst().base();
        Set<ExactRatio> dates = new LinkedHashSet<>();
        for (Member each : chosen) {
            if (!each.base().equals(base) || !dates.add(each.at())) {
                return false;
            }
        }
        for (Object each : kept) {
            if (each instanceof Proposition part && touches(positionsOf.apply(part), container)) {
                return false;
            }
        }
        for (Proposition each : remaining) {
            Member member = memberOf(each);
            if (member != null) {
                if (!member.container().equals(container) || !member.base().equals(base)
                        || dates.contains(member.at())) {
                    return false;
                }
            } else if (touches(positionsOf.apply(each), container)) {
                return false;
            }
        }
        return true;
    }

    /** Whether what {@code places} reads may say something of the container ({@link
     *  ReadSubject#bearOnEachOther}). */
    private static boolean touches(Set<ReadSubject> places, TermPath container) {
        return ReadSubject.bearOnEachOther(places, Set.of(new ReadSubject.At(container)));
    }

    /**
     * {@code part} as the statement of a remainder of a form of the input's numbers it is — what
     * it leaves of that remainder — where the owner of remainders reads it as one
     * ({@link ARemainderMoved#of(RowDemand.OnARemainder)}), or null where it is no such statement.
     */
    private static RowDemand.OnARemainder remainderOf(Proposition part) {
        if (!(part instanceof Proposition.Compared compared)
                || !(compared.relation() instanceof Relation.Affine affine)
                || affine.form().coefs().size() != 1
                || !(affine.form().coefs().keySet().iterator().next()
                        instanceof Quantity.RemainderOfADividend remainder)
                || remainder.overTheInput() == null) {
            return null;
        }
        WholeNumberRuns leaves = RowDemand.OnARemainder.meeting(affine,
                compared.holds() ? affine.proposition() : affine.proposition().denied());
        if (leaves == null) {
            return null;
        }
        RowDemand.OnARemainder stated = new RowDemand.OnARemainder(remainder, leaves);
        return ARemainderMoved.of(stated).isPresent() ? stated : null;
    }

    /**
     * The date a part says some element of a container is, or none is — or null where it says
     * something else.
     *
     * <p>As {@code element + base + at == 0} whichever way round the form was written: the form
     * of an equality is put the way its terms are ordered, so the element may stand in it
     * weighed by minus one, and is then read off the form turned over.
     */
    private static Member memberOf(Proposition part) {
        if (!(part instanceof Proposition.Some some)
                || !(some.container() instanceof DecisionSubject.AnInput)
                || !(some.ofTheElement() instanceof Proposition.Compared compared)
                || !compared.holds()
                || !(compared.relation() instanceof Relation.Affine affine)
                || affine.proposition() != Rel.EQ) {
            return null;
        }
        TermPath container = some.container().inputPosition();
        if (container == null) {
            return null;
        }
        ExactRatio weight = null;
        for (Map.Entry<Quantity, ExactRatio> each : affine.form().coefs().entrySet()) {
            if (isTheElement(each.getKey(), container)) {
                if (weight != null) {
                    return null;
                }
                weight = each.getValue();
            }
        }
        boolean turned = ExactRatio.ONE.negated().equals(weight);
        if (!ExactRatio.ONE.equals(weight) && !turned) {
            return null;
        }
        Map<Quantity, ExactRatio> base = new LinkedHashMap<>();
        for (Map.Entry<Quantity, ExactRatio> each : affine.form().coefs().entrySet()) {
            if (!isTheElement(each.getKey(), container)) {
                base.put(each.getKey(), turned ? each.getValue().negated() : each.getValue());
            }
        }
        ExactRatio at = affine.form().constant();
        return new Member(container, base, turned ? at.negated() : at, some.holds());
    }

    /** Whether {@code term} is the value of an element of {@code container}. */
    private static boolean isTheElement(Quantity term, TermPath container) {
        return term instanceof DecisionAtom.OfTheInput(NumericTerm value)
                && value.atOnePosition() != null
                && value.atOnePosition().position().equals(container.element());
    }
}
