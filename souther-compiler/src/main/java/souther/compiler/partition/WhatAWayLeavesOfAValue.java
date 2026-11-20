package souther.compiler.partition;

import souther.compiler.inputs.InputNumber;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * What a way to a comparison leaves of the values a run works out there, and so whether it keeps
 * an operation over them within its type.
 *
 * <p>A place of the input holds what the region of the way leaves it. An element of a container
 * holds, beside that, what every element is stated to meet on the way ({@link RowDemand.ForAll}),
 * which the region does not take in: a container holding none meets it too, and a region narrowed
 * by it would say no such container is there. Here it narrows only the elements there are, which
 * is what a value read off one comes to. And a container the region leaves holding none holds no
 * element to come to, and what it holds adds up to nought: alike for a number of the input that
 * stands at an element and for a value a run works out off one.
 *
 * <p>This shows where no run stops, and never that one does: what a value may come to is an upper
 * bound on what a run makes it, so an operation the narrowed numbers take past its type is one a
 * run is not shown to stop in, and is left untold.
 */
final class WhatAWayLeavesOfAValue {

    private final InputReading read;
    private final SearchRegion region;
    private final List<OnTheWay> onTheWay;

    private WhatAWayLeavesOfAValue(InputReading read, SearchRegion region,
                                   List<OnTheWay> onTheWay) {
        this.read = read;
        this.region = region;
        this.onTheWay = List.copyOf(onTheWay);
    }

    /**
     * What the way {@code onTheWay} leaves of the values a run works out on it, or null where no
     * row takes it. The region it leaves the input's numbers and what every element of a
     * container is stated to meet are both read off the same conditions, so neither is of
     * another way than the other.
     */
    static WhatAWayLeavesOfAValue along(InputReading read, List<OnTheWay> onTheWay) {
        return Reachability.of(new WayToTheBorder(onTheWay), read.quantities().region())
                instanceof Reachability.Reaching reaching
                ? new WhatAWayLeavesOfAValue(read, reaching.region(), onTheWay) : null;
    }

    /**
     * Whether no run along the way stops in {@code operation}: every number it is over, as the
     * way leaves it, keeps it within its ends, or one it is over is worked out by no run on the
     * way. False where what one of them comes to is not known.
     */
    boolean keepsWithinItsType(UndividedByARelation.IntOperation operation) {
        Map<UndividedByARelation.IntOperand, FormRange> ranges = new HashMap<>();
        for (UndividedByARelation.IntOperand each : operation.form().coefs().keySet()) {
            Optional<FormRange> left;
            if (each instanceof UndividedByARelation.IntOperand.OfAValueWorkedOut(var _,
                    WhereAValueComesFrom origin)) {
                left = leftOf(origin);
            } else if (each instanceof UndividedByARelation.IntOperand.OfTheInput(
                    NumericTerm.FromOnePosition total) && FormRange.aTotal(total)
                    && holdsNoneAt(total.position().element())) {
                // What a container the way leaves holding none adds up to, whatever it is
                // made of on the way.
                left = Optional.of(new FormRange(ExactRatio.ZERO, ExactRatio.ZERO));
            } else if (each instanceof UndividedByARelation.IntOperand.OfTheInput(NumericTerm term)) {
                // As a run works it out, before any type holds it: a total is worked out exactly
                // past the ends of its place, and is not known.
                FormRange range = FormRange.asWorkedOut(term, read);
                if (range == null) {
                    return false;
                }
                left = term instanceof NumericTerm.ValueOf(TermPath place)
                        ? atAPlace(place, range) : narrowed(LinearForm.atom(term), range);
            } else {
                FormRange range = each.range(read);
                if (range == null) {
                    return false;
                }
                left = Optional.of(range);
            }
            if (left.isEmpty()) {
                return true;
            }
            ranges.put(each, left.get());
        }
        FormRange range = FormRange.of(operation.form(), ranges::get);
        return range != null && range.liesWithin(operation.least(), operation.greatest());
    }

    /**
     * Whether no row the way leaves takes {@code operation}, one over numbers of the input, past
     * its ends as forms of those numbers together ({@link UndividedByARelation#noRowTakesItPastItsEnds}):
     * what the numbers it is over hold one beside another, which {@link #keepsWithinItsType} asks of
     * each alone.
     */
    boolean noRowTakesItPastItsEnds(UndividedByARelation.IntOperation operation) {
        return UndividedByARelation.noRowTakesItPastItsEnds(operation, read, List.of(region));
    }

    /** What {@code origin} comes to along the way; none where no run along it works it out. */
    Optional<FormRange> leftOf(WhereAValueComesFrom origin) {
        return switch (origin) {
            case WhereAValueComesFrom.Fixed(FormRange range) -> Optional.of(range);
            case WhereAValueComesFrom.Derived(FormRange range) -> Optional.of(range);
            case WhereAValueComesFrom.AtAPlace(TermPath place, FormRange range) ->
                    atAPlace(place, range);
            case WhereAValueComesFrom.OneOf(List<WhereAValueComesFrom> candidates, var _) -> {
                FormRange hull = null;
                for (WhereAValueComesFrom each : candidates) {
                    Optional<FormRange> one = leftOf(each);
                    if (one.isPresent()) {
                        hull = hull == null ? one.get() : hull.hull(one.get());
                    }
                }
                yield Optional.ofNullable(hull);
            }
        };
    }

    /**
     * What {@code place}, read to hold {@code range}, holds along the way: none where the way
     * leaves no row, or it stands inside the elements of containers the way leaves holding none
     * of it. Inside the elements of a container, at any depth ({@link TermPath#containersHoldingIt}),
     * it holds what every element of each of those containers is stated to meet.
     */
    private Optional<FormRange> atAPlace(TermPath place, FormRange range) {
        LinearForm<NumericTerm> at = LinearForm.atom(new NumericTerm.ValueOf(place));
        List<TermPath> holding = place.containersHoldingIt();
        if (holding.isEmpty()) {
            return narrowed(at, range);
        }
        if (holdsNoneAt(place)) {
            return Optional.empty();
        }
        // Every element meets what the way states of each one, and the elements there are are
        // what a value read off one comes to.
        SearchRegion elements = region;
        for (OnTheWay each : onTheWay) {
            if (each instanceof OnTheWay.TakenIn(var _, RowDemand.ForAll every, var _, var _)
                    && holding.contains(every.container())) {
                for (RowDemand.Relational relation : every.heldOfEveryElement()) {
                    elements = relation.constraint().narrowing(elements);
                }
            }
        }
        return narrowedIn(elements, at, range);
    }

    /** Whether the way leaves no value standing at {@code place}, a place inside the elements of
     *  some container: how many stand there is shown below one. */
    private boolean holdsNoneAt(TermPath place) {
        NumericTerm howMany = InputNumber.howManyStandAt(place, read.domain(), read.rules());
        return howMany != null && narrowed(LinearForm.atom(howMany),
                new FormRange(ExactRatio.ZERO, null)).flatMap(counted ->
                Optional.ofNullable(counted.greatest()))
                .filter(most -> most.compareTo(ExactRatio.ONE) < 0).isPresent();
    }

    /** {@code range}, what {@code form} was read to come to, as the region of the way leaves it. */
    private Optional<FormRange> narrowed(LinearForm<NumericTerm> form, FormRange range) {
        return narrowedIn(region, form, range);
    }

    private static Optional<FormRange> narrowedIn(SearchRegion region, LinearForm<NumericTerm> form,
                                                  FormRange range) {
        return switch (region.projectionOf(form)) {
            case NumericDomain.FormProjection.NothingIsLeft _ -> Optional.empty();
            case NumericDomain.FormProjection.Within within -> {
                FormRange held = range.heldTo(within.bounds());
                yield held.least() != null && held.greatest() != null
                        && held.least().compareTo(held.greatest()) > 0
                        ? Optional.empty() : Optional.of(held);
            }
        };
    }
}
