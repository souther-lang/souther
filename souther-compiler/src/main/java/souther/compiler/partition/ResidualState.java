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
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.numeric.WholeNumberRuns;

import java.math.BigInteger;
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
 * <p>Two things about the parts chosen are told apart from the history that chose them.
 *
 * <p>The remainders of one form by one divisor, moved by constants, are one fact about the
 * remainder of the form: the remainders it can have after all of them
 * ({@link ResiduesAStatementLeaves}), whichever of them said it. Held as the parts, the same
 * remainders left by different histories are different questions.
 *
 * <p>That some element of a container is a date, or none is, is a fact about that date alone when
 * the container is held to nothing and the date is none that anything still to choose, or the
 * line, asks of it. Then the container can be made to hold the dates said to be in it and none of
 * those said not to be, whatever else is chosen, so the fact is eliminated, and what it leaves
 * behind is that a date said to be in it is a date: the farthest of those from the base is kept.
 * Anything this cannot show is no fact eliminated, and the parts stand as they were chosen.
 */
final class ResidualState {

    private ResidualState() {
    }

    /** The remainders of one form by one divisor the parts chosen leave. */
    record Residues(LinearForm<NumericTerm> form, BigInteger divisor, WholeNumberRuns left) {}

    /** The farthest of the dates said to be in a container, of one base. */
    record Farthest(TermPath container, Map<Quantity, ExactRatio> base, ExactRatio at) {}

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
        Map<ResidueKey, WholeNumberRuns> residues = new LinkedHashMap<>();
        List<Member> chosen = new ArrayList<>();
        Set<Object> out = new LinkedHashSet<>();
        TermPath container = null;
        for (Proposition part : bearing) {
            ResidueKey key = residueKeyOf(part);
            if (key != null) {
                WholeNumberRuns runs = ResiduesAStatementLeaves.of(part, key.form(), key.divisor());
                residues.merge(key, runs, WholeNumberRuns::and);
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
        residues.forEach((key, runs) -> out.add(new Residues(key.form(), key.divisor(), runs)));
        if (chosen.isEmpty()) {
            return Optional.of(out);
        }
        if (!eliminated(container, chosen, out, remaining, positionsOf, held, holdsNothing)) {
            return Optional.empty();
        }
        Member farthest = null;
        for (Member each : chosen) {
            if (each.holds() && (farthest == null || each.at().compareTo(farthest.at()) < 0)) {
                farthest = each;
            }
        }
        if (farthest != null) {
            out.add(new Farthest(container, farthest.base(), farthest.at()));
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

    /**
     * Whether {@code places} are not known, or one is the container or at or under it — or is a
     * value a binding holds, which may be one an element of the container was worked into, and
     * is not shown to be anything else.
     */
    private static boolean touches(Set<ReadSubject> places, TermPath container) {
        if (places == null) {
            return true;
        }
        for (ReadSubject each : places) {
            if (!(each instanceof ReadSubject.At(TermPath path)) || path.isAtOrUnder(container)) {
                return true;
            }
        }
        return false;
    }

    private record ResidueKey(LinearForm<NumericTerm> form, BigInteger divisor) {}

    /** The form and divisor of a part that is a comparison of one remainder of a form of the
     *  input's numbers, or null where it is not. */
    private static ResidueKey residueKeyOf(Proposition part) {
        if (!(part instanceof Proposition.Compared compared)
                || !(compared.relation() instanceof Relation.Affine affine)
                || affine.form().coefs().size() != 1
                || !(affine.form().coefs().keySet().iterator().next()
                        instanceof Quantity.RemainderOfADividend remainder)) {
            return null;
        }
        LinearForm<NumericTerm> over = remainder.overTheInput();
        if (over == null || !over.constant().isWhole()) {
            return null;
        }
        return new ResidueKey(new LinearForm<>(ExactRatio.ZERO, over.coefs()),
                remainder.divisor());
    }

    /** The date a part says some element of a container is, or none is — or null where it says
     *  something else. */
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
        Map<Quantity, ExactRatio> base = new LinkedHashMap<>();
        int elements = 0;
        for (Map.Entry<Quantity, ExactRatio> each : affine.form().coefs().entrySet()) {
            if (each.getKey() instanceof DecisionAtom.OfTheInput(NumericTerm term)
                    && term.atOnePosition() != null
                    && term.atOnePosition().position().equals(container.element())) {
                if (!ExactRatio.ONE.equals(each.getValue())) {
                    return null;
                }
                elements++;
            } else {
                base.put(each.getKey(), each.getValue());
            }
        }
        return elements == 1 ? new Member(container, base, affine.form().constant(), some.holds())
                : null;
    }
}
