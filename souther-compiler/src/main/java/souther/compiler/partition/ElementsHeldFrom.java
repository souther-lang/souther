package souther.compiler.partition;

import souther.compiler.check.Choice;
import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.core.Core;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.PathResolution;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.WhereAnApplicationIsMade;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.Optional;

/**
 * A container of the body whose elements are, on every run, the elements standing at one position
 * of the input in the row's order where {@code where} holds, and none where it does not.
 *
 * <p>A container at a position is that position wherever a row is. One chosen between that
 * position and a list written empty — {@code if c.open then c.items else []} — is the position
 * where an arm answering it is taken, and holds nothing on every other run. A closure an operation
 * applies over it is applied over the position's elements in their order and only where
 * {@code where} holds, so an element an operation stopped at is an element of the position, and a
 * run inside the closure is one where {@code where} holds and the position holds something.
 *
 * <p>Only arms answering the one position or a list written empty. An arm answering another
 * position, or anything made of one, holds other elements or the same ones in another order, and
 * the container is not this.
 *
 * @param position where the elements stand
 * @param where    what has to hold for the container to hold them
 */
record ElementsHeldFrom(TermPath position, Proposition where) {

    ElementsHeldFrom {
        Objects.requireNonNull(position, "the elements stand somewhere");
        Objects.requireNonNull(where, "and are held under something, if only nothing");
    }

    /** The position {@code container}'s elements are held from, or empty where they are not
     *  those of one position of the input. */
    static Optional<ElementsHeldFrom> of(Denotation container, InputReading read) {
        DeclarationNewtypes newtypes = read.newtypes();
        if (container.at().pathOf(container.value(), newtypes) instanceof PathResolution.At(
                TermPath at)) {
            return Optional.of(new ElementsHeldFrom(at, WhereAnApplicationIsMade.nothingAsked()));
        }
        Denotation whole = container.at().standing(container.value(), read.symbols(), newtypes);
        Core fork = Core.withoutStanding(whole.value());
        Choice choice = Choice.of(fork);
        if (choice == null) {
            return Optional.empty();
        }
        WhatConditionsState conditions = WhatConditionsState.of(read);
        TermPath position = null;
        List<Proposition> taken = new ArrayList<>();
        for (int part = 0; part < choice.arms().size(); part++) {
            Choice.Arm arm = choice.arms().get(part);
            if (Core.withoutStanding(arm.answers()) instanceof Core.ListLit written
                    && written.elements().isEmpty()) {
                continue;
            }
            Optional<ElementsHeldFrom> inTheArm = of(new Denotation(arm.answers(),
                    whole.at().choosing(arm.decidedBy(), read.symbols(), newtypes)), read);
            if (inTheArm.isEmpty()
                    || (position != null && !position.equals(inTheArm.get().position()))) {
                return Optional.empty();
            }
            position = inTheArm.get().position();
            taken.add(WhereAnApplicationIsMade.past(
                    conditions.arm(fork, part, whole.at()).proposition(), inTheArm.get().where()));
        }
        return position == null ? Optional.empty()
                : Optional.of(new ElementsHeldFrom(position,
                        WhereAnApplicationIsMade.alongOneOf(taken)));
    }
}
