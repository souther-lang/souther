package souther.compiler.partition;

import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.WhereAnApplicationIsMade;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * The containers of the input a closure that operations apply is applied over, and what has to
 * hold for a run to be inside it: one of them holding something.
 *
 * <p>One answer for every reader that enters such a closure. The reading of the comparisons puts
 * it on each application ({@link ClosureApplications}); the reading of what arrives where takes it
 * in on the way into the closure, so a closure over a container the rules hold to none is one no
 * run enters, for both.
 *
 * @param containers       the positions of the containers, in the order the closure is handed them
 * @param holdingSomething one of them holding something: an option its one value, and any other
 *                         container anything
 */
public record WhereAClosureIsApplied(List<TermPath> containers, Proposition holdingSomething) {

    public WhereAClosureIsApplied {
        containers = List.copyOf(containers);
        if (containers.isEmpty()) {
            throw new IllegalArgumentException("a closure applied over containers, over none");
        }
    }

    /**
     * Where a closure handed the elements of {@code appliedOver} is applied, or empty where it is
     * handed none or one of them stands at no position of the input: a run may be inside the
     * closure by the operation over that one with every other empty, so saying one of the rest
     * holds something would be saying more than is known.
     *
     * <p>A container holding a position's elements only under a condition ({@link
     * ElementsHeldFrom}) holds something where the condition holds and the position does.
     */
    public static Optional<WhereAClosureIsApplied> of(List<InputReads.AppliedOver> appliedOver,
                                                      InputReading read) {
        List<TermPath> containers = new ArrayList<>();
        List<Proposition> holding = new ArrayList<>();
        for (InputReads.AppliedOver each : appliedOver) {
            Optional<ElementsHeldFrom> held = ElementsHeldFrom.of(each.container(), read);
            Optional<TermPath> at = held.isPresent() ? held.map(ElementsHeldFrom::position)
                    : Pullback.positionHoldingWhatItHolds(each.container(), read);
            if (at.isEmpty()) {
                return Optional.empty();
            }
            containers.add(at.get());
            List<DecisionSubject> it = List.of(new DecisionSubject.AnInput(at.get()));
            holding.add(WhereAnApplicationIsMade.whereOneOfTheContainersHoldsSomething(
                    held.map(ElementsHeldFrom::where)
                            .orElseGet(WhereAnApplicationIsMade::nothingAsked),
                    each.anOption() ? List.of() : it, each.anOption() ? it : List.of()));
        }
        if (containers.isEmpty()) {
            return Optional.empty();
        }
        return Optional.of(new WhereAClosureIsApplied(containers,
                WhereAnApplicationIsMade.alongOneOf(holding)));
    }
}
