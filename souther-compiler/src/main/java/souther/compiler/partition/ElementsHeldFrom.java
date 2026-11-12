package souther.compiler.partition;

import souther.compiler.check.AnOperationApplied;
import souther.compiler.check.BoundOperationFacts;
import souther.compiler.check.Choice;
import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.core.Core;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.PathResolution;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.WhereAnApplicationIsMade;
import souther.compiler.semantics.MapPart;

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
 * @param position where the container is: the position whose entries are walked, which what the
 *                 walk stops at and how many it holds are asked of
 * @param elements where the elements it holds stand: the position's own elements, or the keys of a
 *                 map whose keys the container lists, which a comparison made on one reads at
 * @param where    what has to hold for the container to hold them
 */
record ElementsHeldFrom(TermPath position, TermPath elements, Proposition where) {

    ElementsHeldFrom {
        Objects.requireNonNull(position, "the elements stand somewhere");
        Objects.requireNonNull(elements, "and each stands at some place of it");
        Objects.requireNonNull(where, "and are held under something, if only nothing");
    }

    /** The elements of the position {@code position}, held under {@code where}. */
    ElementsHeldFrom(TermPath position, Proposition where) {
        this(position, position.element(), where);
    }

    /**
     * The map a list is the keys or the values of, where that map is a position of the input: its
     * keys or its values are the map's own, in the order the map holds its entries.
     */
    private static Optional<ElementsHeldFrom> ofTheMapListed(Denotation list, InputReading read) {
        AnOperationApplied applied = AnOperationApplied.of(Core.withoutStanding(list.value()));
        BoundOperationFacts.Listed listed = applied == null ? null
                : DefaultBoundOperationFacts.get().listsAPartOf(applied.operation());
        if (listed == null || listed.part() == MapPart.ENTRIES
                || !(list.at().pathOf(applied.argument(listed.map()), read.newtypes())
                        instanceof PathResolution.At(TermPath map))) {
            return Optional.empty();
        }
        return Optional.of(new ElementsHeldFrom(map,
                listed.part() == MapPart.KEYS ? map.key() : map.element(),
                WhereAnApplicationIsMade.nothingAsked()));
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
        Optional<ElementsHeldFrom> listed = ofTheMapListed(whole, read);
        if (listed.isPresent()) {
            return listed;
        }
        Core fork = Core.withoutStanding(whole.value());
        Choice choice = Choice.of(fork);
        if (choice == null) {
            return Optional.empty();
        }
        WhatConditionsState conditions = WhatConditionsState.of(read);
        ElementsHeldFrom arrived = null;
        List<Proposition> taken = new ArrayList<>();
        for (int part = 0; part < choice.arms().size(); part++) {
            Choice.Arm arm = choice.arms().get(part);
            if (Core.withoutStanding(arm.answers()) instanceof Core.ListLit written
                    && written.elements().isEmpty()) {
                continue;
            }
            Optional<ElementsHeldFrom> inTheArm = of(new Denotation(arm.answers(),
                    whole.at().choosing(arm.decidedBy(), read.symbols(), newtypes)), read);
            if (inTheArm.isEmpty() || (arrived != null
                    && !(arrived.position().equals(inTheArm.get().position())
                            && arrived.elements().equals(inTheArm.get().elements())))) {
                return Optional.empty();
            }
            arrived = inTheArm.get();
            taken.add(WhereAnApplicationIsMade.past(
                    conditions.arm(fork, part, whole.at()).proposition(), inTheArm.get().where()));
        }
        return arrived == null ? Optional.empty()
                : Optional.of(new ElementsHeldFrom(arrived.position(), arrived.elements(),
                        WhereAnApplicationIsMade.alongOneOf(taken)));
    }
}
