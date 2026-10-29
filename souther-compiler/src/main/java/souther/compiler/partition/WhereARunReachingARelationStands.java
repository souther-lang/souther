package souther.compiler.partition;

import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Where a run that reaches a relation can stand, as far as the places the relation reads say.
 *
 * <p>A run reaches a relation only with its sides read, and each place a side is made of is a
 * place of that run: a value at it, in the cases of each sum the path to it goes through. So a
 * place the path of which needs a sum value to be in a case that value is not in, with the places
 * read, is a place no such run stands at, and an operation worked out there is worked out by no
 * run that reaches the relation.
 *
 * <p>The answer is {@link #mayStandAt}, which is false only where no run does. The other answer
 * is the unsafe one: a place said to be stood at by no run is a stop let go of, so what is decided
 * here is when that is so, and everything not shown is taken as a place a run may stand at. Three
 * things are shown before a place is left out:
 *
 * <ul>
 *   <li>It is one value. What a path asks of a sum value is asked of the value the path reaches by
 *       fields and cases alone, which is one value of a row. Under an element or a key a path
 *       reaches one value for each element or key the row holds, and two paths under an element
 *       may reach two elements, one in each case, which a run applying a closure to every element
 *       stands at both of. What a path asks beyond its first element or key is not asked here.</li>
 *   <li>The cases are apart. Every place read, and the place asked, ask the value to be in cases,
 *       and a value in the cases of all of them is a value in the cases they have in common: where
 *       they have none, no row has all of them. That is the count of all the places read together,
 *       and not of two of them at a time, which three narrowings with something in common two at
 *       a time and nothing in all three would pass.</li>
 *   <li>The place read is read by the run. The places are those a side is made of
 *       ({@code UndividedByARelation.Side#madeOf}), each the place of an argument the side was
 *       read at ({@code Pullback#whatAnOperationAnswers}), and no place a value may have come
 *       from: a union of the places of several ways a value is made would put a run in a case it
 *       is not in.</li>
 * </ul>
 *
 * <p>And the places read agree. Where no row has them all, a relation is reached by no run, and
 * what that says of the relation is not this answer's to decide: nothing is left out.
 */
final class WhereARunReachingARelationStands {

    /** The cases each value of a row is in, for every value the places read go through. */
    private final Map<String, Set<Refinement>> inCasesOfAll;
    private final boolean agree;

    /**
     * @param reads the places a run that reaches the relation reads, all of them at once
     */
    WhereARunReachingARelationStands(List<TermPath> reads) {
        Map<String, Set<Refinement>> together = new HashMap<>();
        boolean agreeing = true;
        for (TermPath read : reads) {
            agreeing &= meet(together, askedOfValues(read));
        }
        this.inCasesOfAll = together;
        this.agree = agreeing;
    }

    /** Whether some run that reaches the relation stands at {@code place}, or is not shown not
     *  to. */
    boolean mayStandAt(TermPath place) {
        if (!agree) {
            return true;
        }
        Map<String, Set<Refinement>> with = new HashMap<>();
        inCasesOfAll.forEach((value, cases) -> with.put(value, new HashSet<>(cases)));
        return meet(with, askedOfValues(place));
    }

    /**
     * Whether the path is one value of a row: it goes through fields and cases only, and no
     * element or key, under which it is one value for each element or key the row holds.
     */
    static boolean isOneValueOfARow(TermPath path) {
        return path.steps().stream().allMatch(WhereARunReachingARelationStands::isOneValue);
    }

    private static boolean isOneValue(TermPath.Step step) {
        return step instanceof TermPath.Step.Field || step instanceof TermPath.Step.Refine;
    }

    /**
     * The cases the path asks each value it goes through to be in, down to its first element or
     * key. A value is named by the path to it: a case narrows a value to some of its cases, and
     * what is read under it is read of the value in those, so the name of what is under includes
     * the cases.
     */
    private static Map<String, Set<Refinement>> askedOfValues(TermPath path) {
        Map<String, Set<Refinement>> asked = new HashMap<>();
        StringBuilder value = new StringBuilder(path.head());
        for (TermPath.Step step : path.steps()) {
            if (!isOneValue(step)) {
                break;
            }
            if (step instanceof TermPath.Step.Refine(var cases)) {
                List<Refinement> atoms = new ArrayList<>(cases.atoms());
                asked.merge(value.toString(), new HashSet<>(atoms), (had, now) -> {
                    had.retainAll(now);
                    return had;
                });
                value.append('@').append(atoms.stream().map(Refinement::spelled).sorted().toList());
            } else {
                value.append('.').append(step);
            }
        }
        return asked;
    }

    /** Puts {@code asked} into {@code together}; false where some value is then in no case. */
    private static boolean meet(Map<String, Set<Refinement>> together,
                                Map<String, Set<Refinement>> asked) {
        boolean someCaseIsLeft = true;
        for (Map.Entry<String, Set<Refinement>> each : asked.entrySet()) {
            Set<Refinement> now = together.computeIfAbsent(each.getKey(),
                    value -> new HashSet<>(each.getValue()));
            now.retainAll(each.getValue());
            someCaseIsLeft &= !now.isEmpty();
        }
        return someCaseIsLeft;
    }
}
