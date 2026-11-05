package souther.compiler.partition;

import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;

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
 * <p>What every element of such a container meets one of ({@link RowDemand.EveryElementWithin})
 * holds of each element there, each whichever way it meets: of the element some quantifier finds,
 * which then meets what that quantifier asks beside one of the ways, and of some element where the
 * container cannot hold none. Each such statement is asked apart from any other over the same
 * container, which asks less than the two together do — so what is shown to leave nothing is a
 * proof, and what two of them leave together is not looked for.
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

    /** What every element of a container inside it meets one of. */
    private final List<RowDemand.EveryElementWithin> ofEach;

    private WhatAnElementIsLeft(SearchRegion held, List<RowDemand.SomeElementWithin> ofTheirOwn,
                                List<RowDemand.EveryElementWithin> ofEach) {
        this.held = held;
        this.ofTheirOwn = List.copyOf(ofTheirOwn);
        this.ofEach = List.copyOf(ofEach);
    }

    /** An element asked nothing yet, of a container whose elements all hold {@code declared}. */
    static WhatAnElementIsLeft of(SearchRegion declared) {
        return new WhatAnElementIsLeft(declared, List.of(), List.of());
    }

    /**
     * This with {@code asked} taken in as well, or nothing where that is shown to leave no
     * element: what it asks of the element itself leaves nothing beside what was held, or what
     * is asked of the elements of a container inside it leaves none there.
     *
     * <p>What is asked of those elements is asked again whenever what it is asked beside grows:
     * all of it where the element itself is narrowed, since what holds of every element there is
     * what each is asked beside, and what some element of a container is asked where what each
     * element of that container meets one of is added. Otherwise only what {@code asked} adds is
     * asked, so what comes back does not turn on the order things were asked in.
     */
    Optional<WhatAnElementIsLeft> with(List<RowDemand.AskedOfAnElement> asked) {
        List<TakenConstraint> own = new ArrayList<>();
        List<RowDemand.SomeElementWithin> addedSome = new ArrayList<>();
        List<RowDemand.EveryElementWithin> addedEach = new ArrayList<>();
        for (RowDemand.AskedOfAnElement each : asked) {
            switch (each) {
                case RowDemand.Relational(TakenConstraint relation) -> own.add(relation);
                case RowDemand.SomeElementWithin some -> addedSome.add(some);
                case RowDemand.EveryElementWithin every -> addedEach.add(every);
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
        List<RowDemand.SomeElementWithin> allSome = new ArrayList<>(ofTheirOwn);
        allSome.addAll(addedSome);
        List<RowDemand.EveryElementWithin> allEach = new ArrayList<>(ofEach);
        allEach.addAll(addedEach);
        List<RowDemand.SomeElementWithin> someAsked = new ArrayList<>(addedSome);
        List<RowDemand.EveryElementWithin> eachAsked = new ArrayList<>(addedEach);
        if (!own.isEmpty()) {
            someAsked = allSome;
            eachAsked = allEach;
        } else if (!addedEach.isEmpty()) {
            Set<TermPath> movedIn = new LinkedHashSet<>();
            addedEach.forEach(every -> movedIn.add(every.container()));
            ofTheirOwn.stream().filter(some -> movedIn.contains(some.container()))
                    .forEach(someAsked::add);
        }
        for (RowDemand.SomeElementWithin some : someAsked) {
            if (!someElementMeets(further, some.container(), some.asked(), allEach)) {
                return Optional.empty();
            }
        }
        for (RowDemand.EveryElementWithin every : eachAsked) {
            if (TakenConstraint.nothingMeetsAll(List.of(every.holdingNone().constraint()), further)
                    && !someElementMeets(further, every.container(), List.of(), allEach)) {
                return Optional.empty();
            }
        }
        return Optional.of(new WhatAnElementIsLeft(further, allSome, allEach));
    }

    /**
     * Whether some element of the container at {@code container} is not shown to meet nothing of
     * {@code asked} beside one way of each of {@code ofEach} over it, everything every element
     * holds being {@code held}: each of {@code ofEach} asked on its own.
     */
    private static boolean someElementMeets(SearchRegion held, TermPath container,
                                            List<RowDemand.AskedOfAnElement> asked,
                                            List<RowDemand.EveryElementWithin> ofEach) {
        Optional<WhatAnElementIsLeft> left = of(held).with(asked);
        if (left.isEmpty()) {
            return false;
        }
        for (RowDemand.EveryElementWithin every : ofEach) {
            if (every.container().equals(container) && every.ways().stream()
                    .noneMatch(way -> left.get().with(way).isPresent())) {
                return false;
            }
        }
        return true;
    }
}
