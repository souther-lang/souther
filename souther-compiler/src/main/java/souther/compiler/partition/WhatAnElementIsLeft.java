package souther.compiler.partition;

import souther.compiler.inputs.SearchRegion;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * What the declarations leave an element of a container once what it is asked so far is taken in
 * — the one answer to whether some element meets a way of what a quantifier asks.
 *
 * <p>What the element is asked of itself is taken in together: it is one element, and a position
 * inside it says that element. What some element of a container inside it is asked
 * ({@link RowDemand.SomeElementWithin}) is not. That is asked of an element of its own, which meets
 * what holds of every element there and nothing another quantifier over the same container asks:
 * two of them are met by two elements, which may differ, and a position inside the container says
 * an element and not which. So each is asked by an answer of this kind over what is held so far,
 * one level further in, and never with another.
 *
 * <p>A proof and nothing weaker. Asked of what the declarations leave, which is what every element
 * holds, an answer that nothing is left says no element meets what was taken in; what is not
 * shown to leave nothing is no proof that some element does.
 *
 * <p>Held while one way is walked and kept by no answer: what it holds is how far a walk got.
 */
final class WhatAnElementIsLeft {

    /** What every element holds, with what the element is asked of itself taken in. */
    private final SearchRegion held;

    /** What some element of a container inside it is asked, each of its own. */
    private final List<RowDemand.SomeElementWithin> ofTheirOwn;

    private WhatAnElementIsLeft(SearchRegion held, List<RowDemand.SomeElementWithin> ofTheirOwn) {
        this.held = held;
        this.ofTheirOwn = List.copyOf(ofTheirOwn);
    }

    /** An element asked nothing yet, of a container whose elements all hold {@code declared}. */
    static WhatAnElementIsLeft of(SearchRegion declared) {
        return new WhatAnElementIsLeft(declared, List.of());
    }

    /**
     * This with {@code asked} taken in as well, or nothing where that is shown to leave no
     * element: what it asks of the element itself leaves nothing beside what was held, or what
     * some element of a container inside it is asked leaves none there.
     *
     * <p>What each such element is asked is asked again whenever the element itself is narrowed,
     * since what holds of every element there is what it is asked beside; otherwise only what
     * {@code asked} adds is asked.
     */
    Optional<WhatAnElementIsLeft> with(List<RowDemand.AskedOfAnElement> asked) {
        List<TakenConstraint> own = new ArrayList<>();
        List<RowDemand.SomeElementWithin> added = new ArrayList<>();
        for (RowDemand.AskedOfAnElement each : asked) {
            switch (each) {
                case RowDemand.Relational(TakenConstraint relation) -> own.add(relation);
                case RowDemand.SomeElementWithin some -> added.add(some);
                // A truth, a case or a value is written into the element and narrows no region.
                case RowDemand.ATruth _, RowDemand.InCases _, RowDemand.SameAs _,
                     RowDemand.DifferentFrom _, RowDemand.KeyedAs _, RowDemand.NotKeyedAs _,
                     RowDemand.WithinIt _ -> { }
            }
        }
        SearchRegion further = own.isEmpty() ? held : TakenConstraint.narrowedBy(own, held);
        if (!own.isEmpty() && TakenConstraint.nothingIsLeftFor(own, further)) {
            return Optional.empty();
        }
        List<RowDemand.SomeElementWithin> all = new ArrayList<>(ofTheirOwn);
        all.addAll(added);
        for (RowDemand.SomeElementWithin some : own.isEmpty() ? added : all) {
            if (of(further).with(some.asked()).isEmpty()) {
                return Optional.empty();
            }
        }
        return Optional.of(new WhatAnElementIsLeft(further, all));
    }
}
