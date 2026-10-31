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
 * The containers a closure that operations apply is applied over, and what has to hold for a run
 * to be inside it: one of them holding something.
 *
 * <p>One answer for every reader that enters such a closure. The reading of the comparisons puts
 * it on each application ({@link ClosureApplications}); the reading of what arrives where takes it
 * in on the way into the closure, so a closure over a container the rules hold to none is one no
 * run enters, for both.
 *
 * @param containers       each container as a proof names it, in the order the closure is handed
 *                         them: the position of one the input holds, and the call that made one an
 *                         operation built
 * @param holdingSomething one of them holding something: an option its one value, and any other
 *                         container anything
 */
public record WhereAClosureIsApplied(List<String> containers, Proposition holdingSomething) {

    public WhereAClosureIsApplied {
        containers = List.copyOf(containers);
        if (containers.isEmpty()) {
            throw new IllegalArgumentException("a closure applied over containers, over none");
        }
    }

    /**
     * Where a closure handed the elements of {@code appliedOver} is applied, or empty where it is
     * handed none, or where what one of them holding something states was not read through: a run
     * may be inside the closure by the operation over that one with every other empty, so saying
     * one of the rest holds something would be saying more than is known.
     *
     * <p>A container holding a position's elements only under a condition ({@link
     * ElementsHeldFrom}) holds something where the condition holds and the position does. One at
     * no position holds something where what the library says of the operation that made it
     * holding something does ({@link WhatConditionsState#holdingSomething}): a list of every whole
     * number between two holds one where the second is not below the first. An option at no
     * position is not asked.
     */
    public static Optional<WhereAClosureIsApplied> of(List<InputReads.AppliedOver> appliedOver,
                                                      InputReading read) {
        List<String> containers = new ArrayList<>();
        List<Proposition> holding = new ArrayList<>();
        for (InputReads.AppliedOver each : appliedOver) {
            Optional<ElementsHeldFrom> held = ElementsHeldFrom.of(each.container(), read);
            Optional<TermPath> at = held.isPresent() ? held.map(ElementsHeldFrom::position)
                    : Pullback.positionHoldingWhatItHolds(each.container(), read);
            if (at.isEmpty()) {
                if (each.anOption()) {
                    return Optional.empty();
                }
                Proposition made = WhatConditionsState.of(read).holdingSomething(
                        each.container().value(), each.container().at(), read).proposition();
                if (Proposition.firstStopIn(made) != null) {
                    return Optional.empty();
                }
                // Named as the call that made it, and not as whatever name it was handed on as.
                containers.add(ComparisonAssessment.written(each.container().at().standing(
                        each.container().value(), read.rules().symbols(), read.rules().newtypes())
                        .value()));
                holding.add(WhereAnApplicationIsMade.past(WhereAnApplicationIsMade.nothingAsked(),
                        made));
                continue;
            }
            containers.add(at.get().toString());
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
