package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.check.ClauseMeaning;
import souther.compiler.check.ClauseRead;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.Extreme;
import souther.compiler.check.PublishedRules;
import souther.compiler.check.Shape;
import souther.compiler.inputs.FilingCoordinate;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NameReach;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.PositionBounds;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.WhatARelationLeavesUndivided;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Quantity;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.values.AdmissibleSet;
import souther.compiler.values.StoppedReading;
import souther.compiler.values.UnreadReason;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

/**
 * A relation this stage read over the input, held as what is asked of it: which of its places it
 * is shown to leave undivided ({@link WhatARelationLeavesUndivided}).
 *
 * <p>Each term is asked two things of the reading of the input. Where it may lie is the run the
 * declarations, and the ways where some are asked of, leave it. What it is shown to take is asked
 * apart, and shown only three ways. The value at a position takes every value its type holds where
 * the declarations admit every value there with nothing of them unread and no end placed — the
 * position's own answer, which already holds the rules of its type. Where the rules place ends on
 * it and the ends are shown to be all they say ({@link Position#projection}), with no end on
 * another number of the position, it takes the run the region shows it fills between them: an
 * amount held at nought or more takes every amount from nought on. And a number taken of an
 * unrestricted value takes every number of its run where the operation declares that every number
 * it could answer is one some value answers ({@code EveryAnswerItCanGiveHasASourceValue}): a string
 * of any length is written by repeating a character, and every hour of the day is one some time
 * falls in. Anything else — what an operation answered of the input that declares no such thing, a
 * value no position holds, a position a rule holds to some of its values other than by ends on it —
 * takes what it takes, which nothing here works out.
 *
 * <p><b>Three things are shown of the term reaching, and none of them stands in for another.</b>
 * That it takes every value of a run, as above. That the run a way leaves it is every value between
 * the ends: a way placing an end on the term itself, or a relation the region took in over the term
 * and numbers of other places, narrows where it runs, and what the region then leaves it is taken
 * only as the region answers it whole ({@link SearchRegion#wholeRunOf}) — never put together from
 * where the values lie and a proof given beside it, since the one may be rounded past the rules and
 * the other is not about that. Under {@code a >= b} with {@code b} free, {@code a} still runs over
 * every value. And that nothing ties it to another place. A term that takes every value alone may
 * take only some of them beside a value of another term: under {@code x + y <= 1} over nought and
 * one, {@code x} at one is beside no {@code y} at one. Runs say nothing of that — the runs of each,
 * and of every sum and difference of the two, can be what they would be untied — so what is asked
 * is whether anything could tie the term to the others. A relation a way took in ties the term to
 * whatever a chain of statements reaches from the places it relates it to, and that is asked of
 * each pair of terms apart from what the term runs over: past {@code a >= b}, {@code a} is tied to
 * {@code b} and to nothing else. Which case a value around the term is and how many a value around
 * it holds say nothing of its values and tie it to nothing; nor, where no rule names the term, does
 * what other places of an element it is inside are asked to meet — which key a map's entry is under
 * says nothing of the value there. What a way states of the term otherwise leaves nothing shown of
 * it: a relation over
 * another number of the place it is taken of — a date on the twenty-ninth of February is in a leap
 * year — or anything the region did not take in. The declarations tie it to nothing where no rule
 * of a value it sits in reads a place at, under or around it, other than for how many a container
 * around it holds, which is where a rule over two of its positions is written. A rule that reads
 * the value at its place and nothing around it leaves it the run its bounds say, where those are
 * shown to be the whole of what the rules leave ({@link Position#projection}):
 * {@code expiresOn >= issuedOn} with {@code issuedOn} free leaves {@code expiresOn} every value. It
 * still holds the value beside the places it names, so such a value is tied to nothing only by a
 * term in another parameter, which no declaration relates to it, and a way stating anything of a
 * place of its parameter ties it.
 * A rule reading it any other way, or one not read, leaves nothing shown of it.
 *
 * <p>Held as the relation and not as the answer, because the answer is asked twice: once of what
 * the declarations leave, and again of the rows a way lets through, where {@code n == x} under
 * {@code x >= 0} is false at every {@code n} below nought.
 *
 * <p>Or the values at one position held against one another: how many different values a
 * container holds weighs each element against the others, which take the values it takes, so no
 * value of the element settles it.
 *
 * <p>Or what two numbers of the input come to multiplied, held against a number: the two sides
 * are then the factors, each weighed by one, and what is asked of each is what the other reaches
 * over every level the product over a value of it leaves
 * ({@link WhatARelationLeavesUndivided#leavesOfAProduct}).
 *
 * @param sides           the terms of the relation
 * @param constant        what the terms are held against, or null where that is no number
 * @param relation        how the terms are held against it
 * @param amongThemselves the places whose values it holds against other values of the same place,
 *                        and nothing else
 * @param kind            what the sides are: the terms of a form, the factors of a product held
 *                        against a number, or the dividend and the divisor of a remainder held
 *                        against nought
 */
record UndividedByARelation(List<Side> sides, ExactRatio constant, Rel relation,
                            List<FilingCoordinate> amongThemselves, Kind kind) {

    /** A relation that shows no place undivided: one nothing here takes apart. */
    static final UndividedByARelation SHOWING_NOTHING =
            new UndividedByARelation(List.of(), ExactRatio.ZERO, Rel.EQ, List.of(), Kind.AFFINE);

    UndividedByARelation {
        sides = List.copyOf(sides);
        amongThemselves = List.copyOf(amongThemselves);
        if (kind != Kind.AFFINE && (sides.size() != 2 || constant == null)) {
            throw new IllegalArgumentException("a product or a remainder is of two numbers, held"
                    + " against a number: " + sides);
        }
    }

    /** What the sides of a relation are. */
    enum Kind {
        /** Terms of a form, weighed and added. */
        AFFINE,
        /** The two factors of a product. */
        PRODUCT,
        /** The dividend then the divisor of a remainder, held equal or unequal to nought. */
        DIVISIBILITY
    }

    /** What {@code dividend} leaves divided by {@code divisor}, held equal or unequal to nought;
     *  against any other level or order it shows nothing. */
    static UndividedByARelation ofADivisibility(NumericTerm.FromOnePosition dividend,
                                                NumericTerm.FromOnePosition divisor,
                                                Rel relation) {
        return relation == Rel.EQ || relation == Rel.NE
                ? new UndividedByARelation(List.of(ofTheInput(dividend, ExactRatio.ONE),
                        ofTheInput(divisor, ExactRatio.ONE)), ExactRatio.ZERO, relation,
                        List.of(), Kind.DIVISIBILITY)
                : SHOWING_NOTHING;
    }

    /** The values at {@code at} held against other values at {@code at}. */
    static UndividedByARelation amongTheValuesAt(TermPath at) {
        return new UndividedByARelation(List.of(), ExactRatio.ZERO, Rel.EQ,
                List.of(FilingCoordinate.at(at)), Kind.AFFINE);
    }

    /** What {@code one} and {@code other} come to multiplied, held against {@code level} as
     *  {@code relation}. */
    static UndividedByARelation ofAProduct(NumericTerm.FromOnePosition one,
                                           NumericTerm.FromOnePosition other, ExactRatio level,
                                           Rel relation) {
        return new UndividedByARelation(List.of(ofTheInput(one, ExactRatio.ONE),
                ofTheInput(other, ExactRatio.ONE)), level.negated(), relation, List.of(), Kind.PRODUCT);
    }

    /**
     * What a relation leaves its places, over the rows some way lets through: the places it is
     * shown to leave undivided, and the terms some runs of whose values it is shown to settle,
     * every other value of each leaving it either way. A place in neither is one nothing is shown
     * of.
     *
     * @param undivided the places shown undivided
     * @param settled   each term shown to be settled by some of its values, and those values
     */
    record WhatItLeaves(Set<FilingCoordinate> undivided,
                        Map<NumericTerm.FromOnePosition,
                                WhatARelationLeavesUndivided.Leaves.Settled> settled) {

        WhatItLeaves {
            undivided = Set.copyOf(undivided);
            settled = Map.copyOf(settled);
        }

        /** What both this and {@code other} show, for rows that may come along either: a place
         *  shown one way along one and another way along the other is shown nothing of. */
        WhatItLeaves alongBoth(WhatItLeaves other) {
            Set<FilingCoordinate> both = new LinkedHashSet<>(undivided);
            both.retainAll(other.undivided);
            Map<NumericTerm.FromOnePosition, WhatARelationLeavesUndivided.Leaves.Settled> alike =
                    new LinkedHashMap<>();
            settled.forEach((term, runs) -> {
                if (runs.equals(other.settled.get(term))) {
                    alike.put(term, runs);
                }
            });
            return new WhatItLeaves(both, alike);
        }
    }

    /** The places this relation is about, which are the only ones it says anything of. */
    Set<FilingCoordinate> places() {
        Set<FilingCoordinate> out = new LinkedHashSet<>(amongThemselves);
        sides.forEach(each -> out.addAll(each.madeOf()));
        return out;
    }

    /**
     * One term.
     *
     * @param madeOf the places its value is made of, in the order the relation names them
     * @param weight what it is weighed by
     * @param term   the number of the input it is, or null where it is anything made of one or no
     *               position's
     * @param kept   where it is what a walk keeping an end carried into its step, the end kept so
     *               far, which says where it lies; null otherwise
     */
    record Side(List<FilingCoordinate> madeOf, ExactRatio weight,
                NumericTerm.FromOnePosition term, Quantity.KeptSoFar kept) {

        Side {
            madeOf = List.copyOf(madeOf);
            if (kept != null && (term != null || !madeOf.isEmpty())) {
                throw new IllegalArgumentException("what a walk carried is at no position: "
                        + kept);
            }
        }

        /** The number of the input what this side may be is read off — the order it stands on,
         *  what the declarations and a way say of it: its own, or the element's a walk kept an end
         *  of. */
        NumericTerm.FromOnePosition readOff() {
            return term != null ? term : kept != null ? kept.ofEach() : null;
        }
    }

    /** {@code form} held against nought as {@code relation}. */
    static UndividedByARelation ofAForm(LinearForm<Quantity> form, Rel relation) {
        List<Side> sides = new ArrayList<>();
        for (Map.Entry<Quantity, ExactRatio> each : form.coefs().entrySet()) {
            sides.add(switch (each.getKey()) {
                case DecisionAtom.OfTheInput(NumericTerm term) -> ofTheInput(term,
                        each.getValue());
                case Quantity.WhatAnOperationAnswers answers -> new Side(
                        answers.positionsItIsMadeOf().stream().map(FilingCoordinate::of).toList(),
                        each.getValue(), null, null);
                case Quantity.OfABinding bound -> new Side(List.of(), each.getValue(), null,
                        bound.kept().orElse(null));
                default -> new Side(List.of(), each.getValue(), null, null);
            });
        }
        return new UndividedByARelation(sides, form.constant(), relation, List.of(), Kind.AFFINE);
    }

    /**
     * A form over the input's numbers held against a constant as {@code relation}.
     *
     * @param constant the constant, or null where it is no number
     */
    static UndividedByARelation ofTheInputsNumbers(LinearForm<NumericTerm> form,
                                                  ExactRatio constant, Rel relation) {
        List<Side> sides = new ArrayList<>();
        form.coefs().forEach((term, weight) -> sides.add(ofTheInput(term, weight)));
        return new UndividedByARelation(sides, constant, relation, List.of(), Kind.AFFINE);
    }

    /** The values at two positions held as one value, or not. */
    static UndividedByARelation ofTwoPositions(TermPath one, TermPath other) {
        return new UndividedByARelation(List.of(
                new Side(List.of(FilingCoordinate.at(one)), ExactRatio.ONE,
                        new NumericTerm.ValueOf(one), null),
                new Side(List.of(FilingCoordinate.at(other)), ExactRatio.ONE.negated(),
                        new NumericTerm.ValueOf(other), null)), ExactRatio.ZERO, Rel.EQ,
                List.of(), Kind.AFFINE);
    }

    private static Side ofTheInput(NumericTerm term, ExactRatio weight) {
        return new Side(List.of(FilingCoordinate.of(term)), weight,
                term instanceof NumericTerm.FromOnePosition one ? one : null, null);
    }

    /** The places shown undivided over what the declarations leave. */
    Set<FilingCoordinate> undivided(InputReading read) {
        return undividedWhereRowsArrive(read, List.of());
    }

    /** The places shown undivided over the rows that arrive along {@code ways}
     *  ({@link #leftWhereRowsArrive}). */
    Set<FilingCoordinate> undividedWhereRowsArrive(InputReading read,
                                                   List<Reachability.Reaching> ways) {
        return leftWhereRowsArrive(read, ways).undivided();
    }

    /** What this leaves its places over what the declarations leave. */
    WhatItLeaves left(InputReading read) {
        return leftWhereRowsArrive(read, List.of());
    }

    /**
     * What this leaves its places over the rows that arrive at the relation along {@code ways} —
     * over what the declarations leave, where there are none.
     *
     * <p>Shown along each way apart, and a place is left undivided, or settled by some of its
     * values, where every way shows it so. Two ways put together run over more than either, and
     * what a term takes beside another along both is not what it takes along each: the runs of each
     * may join without a gap while a pair one way keeps out is one the other never reaches. Nothing
     * here shows what they come to together. A way split at a choice is each of its branches, so
     * each is a way here, and a way some of whose branches were not split out shows nothing.
     */
    WhatItLeaves leftWhereRowsArrive(InputReading read, List<Reachability.Reaching> ways) {
        WhatItLeaves nothingShown = new WhatItLeaves(new LinkedHashSet<>(amongThemselves),
                Map.of());
        // What the declarations leave each side, which no way changes: asked once for all of them.
        // A side a walk kept an end of is asked of the element's number, which is what the end
        // lies between.
        List<Source> sources = new ArrayList<>();
        for (Side each : sides) {
            sources.add(each.kept() == null ? sourceOf(each.term(), read)
                    : keptSource(each.kept(), read));
        }
        // And the order each side's values are counted on, which says where its type ends.
        List<Carrier> carriers = new ArrayList<>();
        for (Side each : sides) {
            TermOrders orders = each.readOff() == null ? null
                    : read.quantities().ordersOf(each.readOff());
            carriers.add(orders == null ? null : orders.answered());
        }
        // Where each side stands is compared with where the others do, which says something only
        // where they stand on one order: a case of one enumeration has no place on another's.
        // Nothing a side is shown to take is then a place on another's order, and two values of
        // two orders never take the same values, so nothing is shown of any of them.
        for (Carrier one : carriers) {
            for (Carrier other : carriers) {
                if (one != null && other != null && !Carrier.onOneOrder(one, other)) {
                    return nothingShown;
                }
            }
        }
        // Two sides each standing at the other's value are compared as one value against another,
        // so a side with no order of its own here — what an operation answered — stands on the
        // other's: a string is held equal to a string, and none is below the empty one.
        if (WhatARelationLeavesUndivided.eachStandsAtTheOthersValue(
                sides.stream().map(Side::weight).toList(), constant)) {
            Carrier known = carriers.get(0) != null ? carriers.get(0) : carriers.get(1);
            carriers = Arrays.asList(carriers.get(0) != null ? carriers.get(0) : known,
                    carriers.get(1) != null ? carriers.get(1) : known);
        }
        if (ways.isEmpty()) {
            return leftAlong(read, sources, carriers, read.quantities().region(), List.of(),
                    true);
        }
        List<Reachability.Reaching> branches = new ArrayList<>();
        for (Reachability.Reaching each : ways) {
            if (!branchesOf(each, branches)) {
                return nothingShown;
            }
        }
        WhatItLeaves out = null;
        for (Reachability.Reaching each : branches) {
            WhatItLeaves along = leftAlong(read, sources, carriers, each.region(),
                    conditionsOf(each), declinedOnlyAKeyFound(each));
            out = out == null ? along : out.alongBoth(along);
        }
        return out;
    }

    /**
     * Whether the way left nothing unread that bears on this relation: it declined no condition,
     * or only the arms that find the value a side was kept an end of ({@link
     * Quantity.KeptSoFar.Seed.OfTheKey}).
     *
     * <p>Such an arm is entered where an earlier element has the key, which is what the side
     * already stands for: the end is of the earlier elements of that key, and is shown to be taken
     * only where the container may hold two elements of one key. It says nothing of the input's
     * values beside that, so it is explained here and left declined for every other reader of the
     * way. An arm of any other match, or of another lookup, is not.
     *
     * <p>A condition on what a dependency answered alone is not declined for anything bearing on
     * the relation either. The answer is a value nothing relates to the input, so the condition
     * narrows which answer the row stands the dependency in with and no number of the input.
     */
    private boolean declinedOnlyAKeyFound(Reachability.Reaching way) {
        if (way.declined().isEmpty()) {
            return true;
        }
        return way.declined().stream().allMatch(declined -> declined.ofAnAnswerAlone()
                || sides.stream().anyMatch(side ->
                        side.kept() != null && findsTheEndOf(declined, side.kept().seed())));
    }

    /**
     * Whether {@code declined} is the entering of the arm that finds the end kept under a key,
     * {@code seed} being what that end starts from.
     *
     * <p>The arm itself, as the tree read has it, and not the arm the source wrote: a helper
     * expanded at two places has one source arm and a lookup in each, and a lookup that found a
     * value in one says nothing of the end the other found.
     */
    static boolean findsTheEndOf(OnTheWay.Declined declined, Quantity.KeptSoFar.Seed seed) {
        return seed instanceof Quantity.KeptSoFar.Seed.OfTheKey(var _, var arm)
                && arm.isPresent() && declined.arm().equals(arm);
    }

    /**
     * Adds to {@code into} each way {@code way} comes to where a condition on it came out one of
     * several ways, and the way itself where none did — false where some of it was not split.
     *
     * <p>A way split at a choice is the choices together, and what it states of the places is
     * stated by each branch and by none of them whole: under {@code x == 0 || x == 1}, a row
     * holds {@code x} at nought or at one, which the way whole says nothing of. A way looked along
     * whole past the figure is one whose branches past it were not split out, and nothing is shown
     * of those.
     */
    private static boolean branchesOf(Reachability.Reaching way,
                                      List<Reachability.Reaching> into) {
        return switch (way.ways()) {
            case Reachability.Ways.One _ -> into.add(way);
            case Reachability.Ways.Each each -> {
                for (Reachability.Reaching branch : each.along()) {
                    if (!branchesOf(branch, into)) {
                        yield false;
                    }
                }
                yield true;
            }
            case Reachability.Ways.Whole _ -> false;
        };
    }

    /**
     * What a way states, as what each statement turns on: what it took in, each as the demand it
     * is, and each case it requires.
     */
    private static List<OnAWay> conditionsOf(Reachability.Reaching way) {
        List<OnAWay> out = new ArrayList<>();
        way.boundedOnTheWay().forEach(taken -> {
            TakenConstraint relation = taken.demand() instanceof RowDemand.Relational(
                    TakenConstraint constraint) ? constraint : null;
            out.add(new OnAWay(taken.demand().positions(),
                    relation instanceof TakenConstraint.Affine(var form, var rel)
                            && rel != Rel.NE && form.coefs().size() == 1
                            && form.coefs().keySet().iterator().next()
                            instanceof NumericTerm.TakenOf count
                            && count.takenAs() instanceof TakenAs.HowManyItHolds,
                    relation, elementsAsked(taken.demand())));
        });
        way.requirements().refinements().keySet()
                .forEach(at -> out.add(new OnAWay(Set.of(at), true, null, null)));
        way.requirements().atANameTheCasesShare()
                .forEach(at -> out.add(new OnAWay(Set.of(at), true, null, null)));
        return out;
    }

    /** The container {@code demand} asks what some or every element of meets, or null where it
     *  asks nothing of the elements of one. */
    private static TermPath elementsAsked(RowDemand.OfACondition demand) {
        return switch (demand) {
            case RowDemand.Exists exists -> exists.container();
            case RowDemand.ForAll every -> every.container();
            case RowDemand.Relational _, RowDemand.ATruth _, RowDemand.OneValueAtBoth _,
                 RowDemand.SoMany _, RowDemand.ForTheRun _ -> null;
        };
    }

    /**
     * One statement of a way.
     *
     * @param positions  the positions it turns on
     * @param whatStands whether it says what stands at a value and nothing of the values that
     *                   stand there beside another: which case the value is, or ends on how many
     *                   it holds. Either of a value around a term says nothing of the term's
     *                   values — an element is reached only where the container holds one, and
     *                   holding one says nothing of what it is. Of the term's own value, a case,
     *                   as an enumeration's, is a value taken out of its order, which the region
     *                   holds, and an end on how many is an end on the term itself
     * @param relation   what it states as a relation the region took in, or null where it states
     *                   anything else
     * @param elementsOf the container it asks what some or every element of meets, or null where
     *                   it asks nothing of the elements of one
     * @param leavesAlone which parts of the dates it names it says nothing of: the years where it
     *                   states months and days and some month and day it lets through stands in
     *                   every year alike, the months and days where it states years and the dates
     *                   have years that hold it together with the rest of the way
     */
    private record OnAWay(Set<TermPath> positions, boolean whatStands, TakenConstraint relation,
                          TermPath elementsOf, PartsLeftAlone leavesAlone) {

        /** The parts of a date a statement of the other parts says nothing of. */
        enum PartsLeftAlone { NONE, YEARS, MONTHS_AND_DAYS }

        OnAWay(Set<TermPath> positions, boolean whatStands, TakenConstraint relation,
               TermPath elementsOf) {
            this(positions, whatStands, relation, elementsOf, PartsLeftAlone.NONE);
        }

        OnAWay leavingAlone(PartsLeftAlone parts) {
            return new OnAWay(positions, whatStands, relation, elementsOf, parts);
        }

        /** Whether this says nothing of {@code term} because it is a part of a date this leaves
         *  alone. */
        boolean leavesAlone(NumericTerm.FromOnePosition term) {
            return term instanceof NumericTerm.TakenOf taken
                    && taken.takenAs() instanceof TakenAs.PartOfDate(TakenAs.DatePart part)
                    && switch (leavesAlone) {
                        case NONE -> false;
                        case YEARS -> part == TakenAs.DatePart.YEAR;
                        case MONTHS_AND_DAYS -> part != TakenAs.DatePart.YEAR;
                    };
        }

        /** What it states as a form of the input's numbers held against nought, or null where it
         *  states anything else. */
        TakenConstraint.Affine affine() {
            return relation instanceof TakenConstraint.Affine affine ? affine : null;
        }

        /** Whether this says nothing of the values {@code term} takes by saying only what stands
         *  at a value around it — which case it is, or how many it holds — and nothing at or
         *  under the term. */
        boolean saysOnlyWhatStandsAround(NumericTerm.FromOnePosition term) {
            return whatStands && touches(term, positions) && onlyAround(term, positions);
        }

        /**
         * Whether this asks of the elements of a container the term is inside of nothing at, under
         * or around the term but the container. An element holds every value its other places
         * leave whatever is asked of those places — which key a map's entry is under, a field
         * beside the term — so this says nothing of the values the term takes, except where a rule
         * relates the term to those places, which the caller asks apart. That an element is a
         * value at another position is asked of the element whole, which is around the term, and
         * is not this.
         */
        boolean asksOnlyOtherPlacesOfTheElement(NumericTerm.FromOnePosition term) {
            if (elementsOf == null || !term.placesReadOff().stream()
                    .allMatch(place -> place.isAtOrUnder(elementsOf.element()))) {
                return false;
            }
            for (TermPath at : positions) {
                if (!at.equals(elementsOf) && term.placesReadOff().stream()
                        .anyMatch(place -> overlap(place, at))) {
                    return false;
                }
            }
            return true;
        }
    }

    /**
     * What this leaves its places over the rows in {@code region}, a way stating
     * {@code conditions} there.
     *
     * <p>A side whose values are whole numbers and that is not shown undivided is asked which of
     * its values settle the relation, and whether the rest of them leave it either way
     * ({@link WhatARelationLeavesUndivided#leavesOf}). A product's two factors are asked that of
     * the product alone, each against what the other reaches.
     *
     * @param sources  what the declarations leave the value each side is, or is taken of, in the
     *                 order of the sides
     * @param carriers the order each side is counted on, or null where it has none
     * @param read     the reading of the input, whose rules say which places they may name
     */
    private WhatItLeaves leftAlong(InputReading read, List<Source> sources,
                                   List<Carrier> carriers, SearchRegion region,
                                   List<OnAWay> stated, boolean heldWhole) {
        LeftToTheCalendar left = leavingPartsAlone(stated, read);
        List<OnAWay> conditions = left.conditions();
        List<List<OnAWay>> stating = stating(sources, conditions, heldWhole);
        List<WhatARelationLeavesUndivided.Term<FilingCoordinate>> terms =
                termsAlong(read, sources, carriers, region, conditions, stating, heldWhole);
        Set<FilingCoordinate> out = new LinkedHashSet<>(amongThemselves);
        Map<NumericTerm.FromOnePosition, WhatARelationLeavesUndivided.Leaves.Settled> settled =
                new LinkedHashMap<>();
        if (theWayLeavesNothingToDivide(conditions)) {
            out.addAll(places());
            return new WhatItLeaves(out, settled);
        }
        // A way that relates a term to other numbers leaves it the run the region answers, and
        // the pair is asked whether the way ties them as well as whether the declarations do.
        TiedOnTheWay tied = TiedOnTheWay.of(conditions, read);
        List<Set<Object>> tiedTo = new ArrayList<>();
        for (int i = 0; i < sides.size(); i++) {
            tiedTo.add(tiedTo(i, tied, conditions, sources, read));
        }
        WhatARelationLeavesUndivided.Independence independent =
                (one, other) -> apartByTheDeclarations(one, other, sources, read)
                        && Collections.disjoint(tiedTo.get(one), tiedTo.get(other));
        if (kind == Kind.PRODUCT) {
            for (int at = 0; at < 2; at++) {
                int other = 1 - at;
                boolean apart = !overlapping(sides.get(at), sides.get(other))
                        && independent.between(at, other);
                putDown(at, WhatARelationLeavesUndivided.leavesOfAProduct(terms.get(at),
                        terms.get(other), constant.negated(), relation, apart,
                        greatestOf(carriers.get(at))), out, settled);
            }
            return new WhatItLeaves(out, settled);
        }
        if (kind == Kind.DIVISIBILITY) {
            boolean apart = !overlapping(sides.get(0), sides.get(1))
                    && independent.between(0, 1);
            for (int at = 0; at < 2; at++) {
                putDown(at, WhatARelationLeavesUndivided.leavesOfADivisibility(terms.get(0),
                        terms.get(1), at == 0, relation, apart, endsOf(carriers.get(0)),
                        endsOf(carriers.get(1))), out, settled);
            }
            return new WhatItLeaves(out, settled);
        }
        // Each side asked once: whether another reaches it, and where it does not, which of its
        // values settle the relation.
        List<WhatARelationLeavesUndivided.Leaves> leaves = new ArrayList<>();
        List<WhatARelationLeavesUndivided.JointSupport> supports =
                datePartsTogether(sources, stating, heldWhole, left.years());
        for (int at = 0; at < sides.size(); at++) {
            WhatARelationLeavesUndivided.Leaves each = WhatARelationLeavesUndivided.leavesOf(
                    terms, at, constant, relation, UndividedByARelation::overlap, independent,
                    granularityOf(carriers.get(at)), greatestOf(carriers.get(at)), supports);
            leaves.add(each);
            if (each instanceof WhatARelationLeavesUndivided.Leaves.Undivided) {
                out.addAll(sides.get(at).madeOf());
            }
        }
        if (!out.containsAll(places())) {
            out.addAll(undividedByTheDifference(sources, carriers, stating, heldWhole, read));
        }
        for (int at = 0; at < sides.size(); at++) {
            if (leaves.get(at) instanceof WhatARelationLeavesUndivided.Leaves.Settled
                    && !out.containsAll(sides.get(at).madeOf())) {
                putDown(at, leaves.get(at), out, settled);
            }
        }
        return new WhatItLeaves(out, settled);
    }

    /**
     * {@code conditions}, with the statements of one kind of part of a date marked that leave the
     * other kind alone.
     *
     * <p>The way is asked whole ({@link WhatStatementsOfDatePartsLeaveAlone}): all its statements
     * of months and days together leave the years alone, or none of them does, and likewise those
     * of years. A statement is of one kind only where every term of it is a month or a day, or
     * every term is a year, of a date the declarations leave every date and no rule names, so that
     * no rule ties its parts to a number of another place. A statement of anything else is left
     * unmarked, and a part it touches is then tied by it as before.
     *
     * <p>Where the months and days are left, the dates are in the years the statements of years
     * were shown to hold at, and the combinations of months and days a date gives are those of
     * its year ({@link #datePartsTogether}).
     */
    private LeftToTheCalendar leavingPartsAlone(List<OnAWay> conditions, InputReading read) {
        List<TakenConstraint.Affine> ofMonthsAndDays = new ArrayList<>();
        List<TakenConstraint.Affine> ofYears = new ArrayList<>();
        for (OnAWay each : conditions) {
            if (statesOnlyParts(each, false, read)) {
                ofMonthsAndDays.add(each.affine());
            } else if (statesOnlyParts(each, true, read)) {
                ofYears.add(each.affine());
            }
        }
        boolean yearsAreLeft = !ofMonthsAndDays.isEmpty()
                && WhatStatementsOfDatePartsLeaveAlone.leavesTheYears(ofMonthsAndDays,
                        yearShiftsOfTheSides());
        WhatStatementsOfDatePartsLeaveAlone.YearsChosen years = ofYears.isEmpty() ? null
                : WhatStatementsOfDatePartsLeaveAlone.leavesTheMonthsAndDays(ofYears,
                        monthsAndDaysTheSidesTake());
        List<OnAWay> out = new ArrayList<>();
        for (OnAWay each : conditions) {
            out.add(yearsAreLeft && statesOnlyParts(each, false, read)
                    ? each.leavingAlone(OnAWay.PartsLeftAlone.YEARS)
                    : years != null && statesOnlyParts(each, true, read)
                    ? each.leavingAlone(OnAWay.PartsLeftAlone.MONTHS_AND_DAYS) : each);
        }
        return new LeftToTheCalendar(out, years);
    }

    /**
     * Whether the statements of {@code conditions} that weigh some terms alike leave no row along
     * the way, or come out one way for this relation at every row they leave
     * ({@link WhatStatementsOfOneFormDecide}). Either way no value of a place divides anything
     * along it.
     */
    private boolean theWayLeavesNothingToDivide(List<OnAWay> conditions) {
        WhatStatementsOfOneFormDecide.Verdict verdict = WhatStatementsOfOneFormDecide.of(
                conditions.stream().map(OnAWay::affine).toList(), askedAsAStatement());
        return verdict.noRowArrives() || verdict.relationIsDecided();
    }

    /** The relation as a statement is held, the sides weighed and added to the constant and held
     *  against nought, or null where it is not of terms of the input. */
    private TakenConstraint.Affine askedAsAStatement() {
        if (kind != Kind.AFFINE || constant == null || sides.isEmpty()) {
            return null;
        }
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        for (Side each : sides) {
            if (each.term() == null || each.kept() != null
                    || coefs.merge(each.term(), each.weight(),
                            (one, other) -> one.plus(other).orNull()) == null) {
                return null;
            }
        }
        return new TakenConstraint.Affine(new LinearForm<>(constant, coefs), relation);
    }

    /** The conditions of a way, marked, and the years its statements of years put the dates in,
     *  or null where they leave the months and days to no years. */
    private record LeftToTheCalendar(List<OnAWay> conditions,
                                     WhatStatementsOfDatePartsLeaveAlone.YearsChosen years) {}

    /** The months and the days the sides take of each date, after the move of each. */
    private Map<TermPath, List<DatesThatStandInEveryYear.Part>> monthsAndDaysTheSidesTake() {
        Map<TermPath, List<DatesThatStandInEveryYear.Part>> out = new LinkedHashMap<>();
        for (Side side : sides) {
            if (side.term() instanceof NumericTerm.TakenOf taken
                    && taken.takenAs() instanceof TakenAs.PartOfDate(TakenAs.DatePart part)
                    && part != TakenAs.DatePart.YEAR) {
                out.computeIfAbsent(taken.position(), _ -> new ArrayList<>()).add(
                        new DatesThatStandInEveryYear.Part(part,
                                taken.transformation().translation()));
            }
        }
        return out;
    }

    /** Whether {@code statement} is a form of years only, or of months and days only, of dates
     *  nothing in the declarations restricts or names. */
    private static boolean statesOnlyParts(OnAWay statement, boolean years, InputReading read) {
        TakenConstraint.Affine affine = statement.affine();
        if (affine == null || affine.form().coefs().isEmpty()) {
            return false;
        }
        for (NumericTerm each : affine.form().coefs().keySet()) {
            if (!(each instanceof NumericTerm.TakenOf taken)
                    || !(taken.takenAs() instanceof TakenAs.PartOfDate(TakenAs.DatePart part))
                    || (part == TakenAs.DatePart.YEAR) != years) {
                return false;
            }
            Source source = sourceOf(taken, read);
            if (source == null || !source.takes().every() || source.named()) {
                return false;
            }
        }
        return true;
    }

    /** The moves of each date whose year a side is, which a month and day must keep it in the
     *  year of. */
    private Map<TermPath, List<DateTranslation>> yearShiftsOfTheSides() {
        Map<TermPath, List<DateTranslation>> out = new LinkedHashMap<>();
        for (Side side : sides) {
            if (side.term() instanceof NumericTerm.TakenOf taken
                    && taken.takenAs() instanceof TakenAs.PartOfDate(TakenAs.DatePart part)
                    && part == TakenAs.DatePart.YEAR) {
                out.computeIfAbsent(taken.position(), _ -> new ArrayList<>())
                        .add(taken.transformation().translation());
            }
        }
        return out;
    }

    /**
     * The sides that are the month or the day of one date, as the combinations that date gives.
     *
     * <p>A date is asked only where the declarations leave it every date and the way says nothing
     * of any part taken of it, so the combinations are the calendar's whole and not those a rule
     * lets through. A date only one side is taken of has no combination to give.
     *
     * <p>A date the way fixes the year of gives the combinations of that year, which are all it
     * can be at; a support is made only where they give every number each side can be, so that no
     * value of a side goes unasked.
     *
     * @param years the years the way puts dates in, or null where it puts none
     */
    private List<WhatARelationLeavesUndivided.JointSupport> datePartsTogether(
            List<Source> sources, List<List<OnAWay>> stating, boolean heldWhole,
            WhatStatementsOfDatePartsLeaveAlone.YearsChosen years) {
        if (!heldWhole) {
            return List.of();
        }
        Map<TermPath, List<Integer>> ofOneDate = new LinkedHashMap<>();
        for (int i = 0; i < sides.size(); i++) {
            if (sides.get(i).term() instanceof NumericTerm.TakenOf taken
                    && taken.takenAs() instanceof TakenAs.PartOfDate(TakenAs.DatePart part)
                    && part != TakenAs.DatePart.YEAR
                    && sources.get(i) != null && sources.get(i).takes().every()
                    && wayOf(taken, stating.get(i)) == Way.UNTOUCHED) {
                ofOneDate.computeIfAbsent(taken.position(), _ -> new ArrayList<>()).add(i);
            }
        }
        List<WhatARelationLeavesUndivided.JointSupport> out = new ArrayList<>();
        for (Map.Entry<TermPath, List<Integer>> date : ofOneDate.entrySet()) {
            List<Integer> members = date.getValue();
            if (members.size() < 2) {
                continue;
            }
            List<DatesThatStandInEveryYear.Part> parts = new ArrayList<>();
            for (int i : members) {
                NumericTerm.TakenOf taken = (NumericTerm.TakenOf) sides.get(i).term();
                parts.add(new DatesThatStandInEveryYear.Part(
                        ((TakenAs.PartOfDate) taken.takenAs()).part(),
                        taken.transformation().translation()));
            }
            Integer year = years == null ? null : years.yearOf().get(date.getKey());
            List<List<ExactRatio>> together = year == null
                    ? MonthsAndDaysOfOneDate.ofAnyYear(parts)
                    : MonthsAndDaysOfOneDate.inYear(parts, year,
                            years.shiftsOf().get(date.getKey()));
            if (together != null && !together.isEmpty()
                    && MonthsAndDaysOfOneDate.coversEveryValue(together, parts)) {
                out.add(new WhatARelationLeavesUndivided.JointSupport(members, together));
            }
        }
        return out;
    }

    /** What {@code leaves} says of the side at {@code at}, put where it goes. */
    private void putDown(int at, WhatARelationLeavesUndivided.Leaves leaves,
                        Set<FilingCoordinate> undivided,
                        Map<NumericTerm.FromOnePosition, WhatARelationLeavesUndivided.Leaves.Settled>
                                settled) {
        switch (leaves) {
            case null -> { }
            case WhatARelationLeavesUndivided.Leaves.Undivided _ ->
                    undivided.addAll(sides.get(at).madeOf());
            case WhatARelationLeavesUndivided.Leaves.Settled runs -> {
                if (sides.get(at).term() != null) {
                    settled.put(sides.get(at).term(), runs);
                }
            }
        }
    }

    /** Whether a place of one side is a place of the other, or part of one. */
    private static boolean overlapping(Side one, Side other) {
        for (FilingCoordinate each : one.madeOf()) {
            for (FilingCoordinate that : other.madeOf()) {
                if (overlap(each, that)) {
                    return true;
                }
            }
        }
        return false;
    }

    /** How the values of {@code carrier} are spaced, or null where it has no order. */
    private static Granularity spacingOf(Carrier carrier) {
        return carrier == null ? null : carrier.spacingBetweenValues();
    }

    /** How the values of {@code carrier} are spaced, or null where they are no numbers a
     *  relation's settling values are worked out over. */
    private static Granularity granularityOf(Carrier carrier) {
        return switch (carrier) {
            case Carrier.Whole _ -> Granularity.DISCRETE;
            case Carrier.Dense _ -> Granularity.DENSE;
            case null, default -> null;
        };
    }

    /** The greatest whole number {@code carrier} holds, or null where it holds no greatest or none
     *  this reads as a number. */
    private static BigInteger greatestOf(Carrier carrier) {
        if (carrier == null || carrier.extent().high() == null
                || !(carrier.extent().high().at() instanceof Count greatest)) {
            return null;
        }
        return greatest.exactly().floor().orNull();
    }

    /** The least whole number {@code carrier} holds, or null where it holds no least or none this
     *  reads as a number. */
    private static BigInteger leastOf(Carrier carrier) {
        if (carrier == null || carrier.extent().low() == null
                || !(carrier.extent().low().at() instanceof Count least)) {
            return null;
        }
        return least.exactly().ceiling().orNull();
    }

    /** Where {@code carrier} stops at either end. */
    private static WhatARelationLeavesUndivided.Ends endsOf(Carrier carrier) {
        return new WhatARelationLeavesUndivided.Ends(leastOf(carrier), greatestOf(carrier));
    }

    /** What the way states of each side, asked once and read by both readings. */
    private List<List<OnAWay>> stating(List<Source> sources, List<OnAWay> conditions,
                                       boolean heldWhole) {
        List<List<OnAWay>> out = new ArrayList<>();
        for (int i = 0; i < sides.size(); i++) {
            Side each = sides.get(i);
            // A value a rule names moves with the places the rule names beside it, so what the
            // way states of any place of its parameter is stated of it.
            out.add(each.readOff() == null || !heldWhole ? List.of()
                    : sources.get(i) != null && sources.get(i).named()
                    ? statingAnythingOfItsParameter(each.readOff(), conditions)
                    : statingAnythingOf(each.readOff(), conditions));
        }
        return out;
    }

    /**
     * Each side as a term of the relation over the rows in {@code region}: where it may lie, what
     * it is shown to take there, and what it takes compared by equality.
     *
     * @param read       the reading of the input, whose declarations alone are what elements
     *                   other than the ones a way reads are left ({@link #keptAlong})
     * @param conditions what the way states
     */
    private List<WhatARelationLeavesUndivided.Term<FilingCoordinate>> termsAlong(
            InputReading read, List<Source> sources, List<Carrier> carriers, SearchRegion region,
            List<OnAWay> conditions, List<List<OnAWay>> stating, boolean heldWhole) {
        List<WhatARelationLeavesUndivided.Term<FilingCoordinate>> terms = new ArrayList<>();
        for (int i = 0; i < sides.size(); i++) {
            Side each = sides.get(i);
            if (each.kept() != null) {
                terms.add(keptAlong(each, sources.get(i), carriers.get(i), region, read,
                        conditions, stating.get(i), heldWhole));
                continue;
            }
            NumericDomain.Bounds holds = asARelationReadsIt(each.term() != null
                    && region.projectionOf(each.term())
                    instanceof NumericDomain.FormProjection.Within(NumericDomain.Bounds within)
                    ? within : NumericDomain.Bounds.OPEN, carriers.get(i));
            Way way = each.term() == null || !heldWhole ? Way.TIES
                    : wayOf(each.term(), stating.get(i));
            Source source = way == Way.TIES ? null : sources.get(i);
            // A statement shown to leave a part alone is taken into the region, which then does not
            // answer for that part: it is answered by what the declarations leave it.
            SearchRegion answering = way == Way.UNTOUCHED && conditions.stream()
                    .anyMatch(statement -> statement.leavesAlone(each.term()))
                    ? read.quantities().region() : region;
            NumericDomain.Bounds realizes = source == null ? null
                    : asARelationReadsIt(realized(each.term(), source, answering, way),
                            carriers.get(i));
            Takes takes = source != null && way == Way.UNTOUCHED
                    && each.term() instanceof NumericTerm.ValueOf ? source.takes() : null;
            terms.add(new WhatARelationLeavesUndivided.Term<>(each.madeOf(), each.weight(), holds,
                    realizes, takes, each.term() instanceof NumericTerm.ValueOf,
                    spacingOf(carriers.get(i))));
        }
        return terms;
    }

    /**
     * A side that is what a walk keeping an end carried into its step, as a term over the rows in
     * {@code region}.
     *
     * <p>On the first element it is the seed, and on a later one the end kept of the seed and the
     * element's number on every element before. So it lies between the seed and the furthest the
     * number may lie past it, and only at the seed where the container holds one element at most.
     * It takes the seed. Past the seed it takes every value the number is shown to take there,
     * where some row of the container holds two elements or more: an earlier element at the value
     * and none before it further out. Nothing is said of which values it takes by equality, which
     * are no values of the element's place.
     *
     * <p>The elements before are not the ones the way to the comparison reads. A condition on the
     * way about the element's number — the element the step is applied to, or one an enclosing
     * walk hands over, which the region holds as the same number — says nothing of the others,
     * which an end above it may have been kept of. So where the earlier elements lie is what the
     * declarations alone leave the number ({@code declared}), and they are shown to take its
     * values only where the way states nothing of it. How many the container holds is one value
     * of the run, and is read where the comparison is; so is a seed the input holds, which the
     * way leaves what it leaves it and which takes what it is shown to take there.
     *
     * @param ofEach     what the declarations leave the element's number
     * @param carrier    the order the element's number is counted on
     * @param region     the rows the way to the comparison lets through
     * @param read       the reading of the input, whose declarations alone are what the earlier
     *                   elements are left
     * @param conditions what the way states
     * @param stating    what the way states of the element's number
     */
    private static WhatARelationLeavesUndivided.Term<FilingCoordinate> keptAlong(
            Side side, Source ofEach, Carrier carrier, SearchRegion region, InputReading read,
            List<OnAWay> conditions, List<OnAWay> stating, boolean heldWhole) {
        Quantity.KeptSoFar kept = side.kept();
        boolean greatest = kept.extreme() instanceof Extreme.Greatest;
        SearchRegion declared = read.quantities().region();
        Start start = startOf(kept, region, read, conditions, heldWhole);
        if (start == null) {
            return new WhatARelationLeavesUndivided.Term<>(side.madeOf(), side.weight(),
                    NumericDomain.Bounds.OPEN, null, null, false, spacingOf(carrier));
        }
        NumericDomain.Bounds seed = start.lies();
        NumericDomain.Bounds seedTakes = start.takes();
        NumericDomain.Bounds twoOrMore =
                new NumericDomain.Bounds(Endpoint.inclusive(Count.of(2)), null);
        // Where the element's number lies past the least the seed may be, on any element before.
        NumericDomain.Bounds lies = (declared.projectionOf(kept.ofEach())
                instanceof NumericDomain.FormProjection.Within(NumericDomain.Bounds within)
                ? within : NumericDomain.Bounds.OPEN).meet(pastOf(seed, greatest));
        boolean atMostOne = kept.howMany() != null && region.projectionOf(kept.howMany())
                instanceof NumericDomain.FormProjection.Within(NumericDomain.Bounds count)
                && !count.meet(twoOrMore).holdsAValue();
        NumericDomain.Bounds holds = atMostOne || !lies.holdsAValue() ? seed
                : NumericDomain.Bounds.spanning(seed, lies);
        // What it is shown to take: the seed's values, on the first element; and past them what
        // the element's number is shown to take, on a row some earlier element is at.
        NumericDomain.Bounds realizes = seedTakes;
        NumericDomain.Bounds several = kept.howMany() == null ? null
                : region.wholeRunOf(kept.howMany());
        boolean untouched = heldWhole && wayOf(kept.ofEach(), stating) == Way.UNTOUCHED
                && !theWayStatesTheKey(kept.seed(), conditions);
        // A seed whose values are not shown leaves nothing for the elements after it to be
        // beside.
        NumericDomain.Bounds taken = (start.seeded() && seedTakes == null) || ofEach == null
                || !untouched || several == null || !several.meet(twoOrMore).holdsAValue() ? null
                : realized(kept.ofEach(), ofEach, declared, Way.UNTOUCHED);
        NumericDomain.Bounds above = taken == null ? null
                : start.seeded() ? taken.meet(pastOf(seedTakes, greatest)) : taken;
        if (above != null && above.holdsAValue()) {
            realizes = start.seeded() && joined(seedTakes, above, greatest, carrier)
                    ? NumericDomain.Bounds.spanning(seedTakes, above) : above;
        }
        return new WhatARelationLeavesUndivided.Term<>(side.madeOf(), side.weight(),
                asARelationReadsIt(holds, carrier), asARelationReadsIt(realizes, carrier), null,
                false, spacingOf(carrier));
    }

    /**
     * Where what a walk keeps an end of starts.
     *
     * @param lies   where the end may lie before any element past the first is counted: the seed,
     *               or, where there is none, wherever the element's number lies
     * @param takes  what the first element's end is shown to take, or null where nothing is shown
     * @param seeded whether the walk starts from a value, so that the end is that value on the
     *               first element; a walk filing under a key starts from none, since the first
     *               element of a key files its own value and is compared with nothing
     */
    private record Start(NumericDomain.Bounds lies, NumericDomain.Bounds takes, boolean seeded) {}

    /** Where the walk {@code kept} describes starts, or null where its seed is a number this
     *  reading does not count with. */
    private static Start startOf(Quantity.KeptSoFar kept, SearchRegion region, InputReading read,
                                 List<OnAWay> conditions, boolean heldWhole) {
        return switch (kept.seed()) {
            case Quantity.KeptSoFar.Seed.Written(ExactRatio number) -> {
                if (!(Count.written(number) instanceof ExactAnswer.Held<Optional<Count>>(
                        Optional<Count> written)) || written.isEmpty()) {
                    yield null;
                }
                Endpoint at = Endpoint.inclusive(written.get());
                NumericDomain.Bounds seed = new NumericDomain.Bounds(at, at);
                yield new Start(seed, seed, true);
            }
            case Quantity.KeptSoFar.Seed.OfTheInput(NumericTerm.FromOnePosition number) -> {
                NumericDomain.Bounds seed = region.projectionOf(number)
                        instanceof NumericDomain.FormProjection.Within(NumericDomain.Bounds within)
                        ? within : NumericDomain.Bounds.OPEN;
                Source source = sourceOf(number, read);
                Way way = !heldWhole || source == null ? Way.TIES
                        : wayOf(number, source.named()
                                ? statingAnythingOfItsParameter(number, conditions)
                                : statingAnythingOf(number, conditions));
                yield new Start(seed, way == Way.TIES ? null
                        : realized(number, source, region, way), true);
            }
            case Quantity.KeptSoFar.Seed.OfTheKey _ -> new Start(
                    read.quantities().region().projectionOf(kept.ofEach())
                            instanceof NumericDomain.FormProjection.Within(
                                    NumericDomain.Bounds within)
                            ? within : NumericDomain.Bounds.OPEN, null, false);
        };
    }

    /** Whether the way states anything of the key {@code seed} files under, which may keep the
     *  elements of one key apart or together. */
    private static boolean theWayStatesTheKey(Quantity.KeptSoFar.Seed seed,
                                              List<OnAWay> conditions) {
        return seed instanceof Quantity.KeptSoFar.Seed.OfTheKey(var key, var _)
                && !statingAnythingOf(new NumericTerm.ValueOf(key), conditions).isEmpty();
    }

    /** Every value at or past the least of {@code run} toward the end kept — at or above it for
     *  the greatest, at or below its greatest for the least. */
    private static NumericDomain.Bounds pastOf(NumericDomain.Bounds run, boolean greatest) {
        return greatest ? new NumericDomain.Bounds(run.min(), null)
                : new NumericDomain.Bounds(null, run.max());
    }

    /**
     * Whether {@code seed} and {@code above}, past it toward the end kept, are one run with
     * nothing between them: they share a value, or on whole numbers the one next to the seed's
     * last value is the first of the other.
     */
    private static boolean joined(NumericDomain.Bounds seed, NumericDomain.Bounds above,
                                  boolean greatest, Carrier carrier) {
        if (seed.meet(above).holdsAValue()) {
            return true;
        }
        Endpoint last = greatest ? seed.max() : seed.min();
        if (!(carrier instanceof Carrier.Whole) || last == null || !last.inclusive()
                || !(last.at() instanceof Count count)) {
            return false;
        }
        ExactAnswer<ExactRatio> next = greatest ? count.exactly().plus(ExactRatio.ONE)
                : count.exactly().minus(ExactRatio.ONE);
        return next instanceof ExactAnswer.Held<ExactRatio>(ExactRatio beside)
                && above.admits(beside);
    }

    /**
     * Whether nothing the declarations say ties where the side at {@code one} lies to where the
     * side at {@code other} does: one of them is a value no rule of a value it sits in names, or
     * the two are in different parameters, which no declaration relates. A side nothing is worked
     * out of may be named by anything.
     *
     * <p>A side a walk kept an end of is the element's number on other elements, which a rule of
     * the container may relate to any element: it is asked as that number, at its place.
     *
     * @param sources what the declarations leave each side, in the order of the sides
     */
    private boolean apartByTheDeclarations(int one, int other, List<Source> sources,
                                           InputReading read) {
        if (!mayBeNamed(one, sources) || !mayBeNamed(other, sources)) {
            return true;
        }
        List<FilingCoordinate> first = placesAsked(sides.get(one));
        List<FilingCoordinate> second = placesAsked(sides.get(other));
        if (first.isEmpty() || second.isEmpty()) {
            return false;
        }
        for (FilingCoordinate each : first) {
            for (FilingCoordinate that : second) {
                if (overlap(each, that) || !Collections.disjoint(
                        tiedByTheDeclarations(each.path(), read),
                        tiedByTheDeclarations(that.path(), read))) {
                    return false;
                }
            }
        }
        return true;
    }

    /** Whether a rule of a value the side at {@code at} sits in may name it. */
    private boolean mayBeNamed(int at, List<Source> sources) {
        Source source = sources.get(at);
        return sides.get(at).readOff() == null || source == null || source.named();
    }

    /** The places what the declarations and a way say of {@code side} are asked at: its own, or
     *  the place of the element's number a walk kept an end of and of a seed the input holds. */
    private static List<FilingCoordinate> placesAsked(Side side) {
        if (side.kept() == null) {
            return side.madeOf();
        }
        List<FilingCoordinate> out = new ArrayList<>();
        out.add(FilingCoordinate.of(side.kept().ofEach()));
        if (side.kept().seed() instanceof Quantity.KeptSoFar.Seed.OfTheInput(var from)) {
            out.add(FilingCoordinate.of(from));
        }
        return out;
    }

    /**
     * {@code run} as a relation reads it on {@code carrier}: ending where the order ends at a value
     * a model holds ({@link Carrier#asARelationReadsIt}) — an enumeration's last case, the empty
     * string — and left as it is where the order has no such end, or the side none at all. Null
     * stays null: nothing shown is still nothing shown.
     */
    private static NumericDomain.Bounds asARelationReadsIt(NumericDomain.Bounds run,
                                                           Carrier carrier) {
        return run == null || carrier == null ? run : run.meet(carrier.asARelationReadsIt());
    }

    /**
     * The places shown undivided because the relation, and everything a way states of its two
     * sides — {@code stating}, side by side — is about how far apart the two are
     * ({@link WhatARelationLeavesUndivided#ofTheirDifference}).
     *
     * <p>Each side is the value at a position the declarations leave every value of its type, so
     * nothing of them ties it and none is unread. What the way holds of either is taken only as a
     * form over the two weighed one way and the other. A statement about either that is anything
     * else — an end on one of them alone, a form with a third number in it — leaves nothing shown,
     * since it may keep a side from values of its own.
     */
    private Set<FilingCoordinate> undividedByTheDifference(List<Source> sources,
                                                         List<Carrier> carriers,
                                                         List<List<OnAWay>> stating,
                                                         boolean heldWhole, InputReading read) {
        if (!heldWhole || sides.size() != 2 || carriers.get(0) == null
                || !carriers.get(0).equals(carriers.get(1))
                || !apartByTheDeclarations(0, 1, sources, read)) {
            return Set.of();
        }
        Carrier on = carriers.get(0);
        List<WhatARelationLeavesUndivided.Term<FilingCoordinate>> terms = new ArrayList<>();
        for (int i = 0; i < sides.size(); i++) {
            Side each = sides.get(i);
            Source source = sources.get(i);
            if (!(each.term() instanceof NumericTerm.ValueOf) || source == null
                    || !source.takes().every()) {
                return Set.of();
            }
            terms.add(new WhatARelationLeavesUndivided.Term<>(each.madeOf(), each.weight(),
                    on.asARelationReadsIt(), on.asARelationReadsIt(), source.takes(), true,
                    on.spacingBetweenValues()));
        }
        // A statement about both sides is in each side's list; it is one statement.
        Set<OnAWay> aboutEither = new LinkedHashSet<>(stating.get(0));
        aboutEither.addAll(stating.get(1));
        List<WhatARelationLeavesUndivided.OnTheDifference> held = new ArrayList<>();
        for (OnAWay each : aboutEither) {
            WhatARelationLeavesUndivided.OnTheDifference statement = each.affine() == null ? null
                    : onTheDifference(each.affine().form(), each.affine().rel());
            if (statement == null) {
                return Set.of();
            }
            held.add(statement);
        }
        return WhatARelationLeavesUndivided.ofTheirDifference(terms, constant, relation, held,
                new NumericDomain.Bounds(on.extent().low(), on.extent().high()),
                UndividedByARelation::overlap);
    }

    /**
     * Those of {@code conditions} that state anything of the values {@code term} takes. What
     * stands at a value around the term, and what other places of an element the term is inside
     * are asked to meet, say nothing of the values the term takes, so a statement of only that is
     * left out.
     */
    private static List<OnAWay> statingAnythingOf(NumericTerm.FromOnePosition term,
                                                  List<OnAWay> conditions) {
        List<OnAWay> out = new ArrayList<>();
        for (OnAWay each : conditions) {
            if (touches(term, each.positions()) && !saysNothingOfTheValuesOf(term, each, false)) {
                out.add(each);
            }
        }
        return out;
    }

    /**
     * Those of {@code conditions} that state anything of a place in the parameter {@code term} is
     * read off, other than what stands at a value around the term. A rule naming the term holds it
     * beside the places it names, so an end on one of those moves where the term runs, and a
     * statement about one of those and another parameter ties the term to that parameter.
     */
    private static List<OnAWay> statingAnythingOfItsParameter(NumericTerm.FromOnePosition term,
                                                              List<OnAWay> conditions) {
        Set<String> heads = new LinkedHashSet<>();
        term.placesReadOff().forEach(place -> heads.add(place.head()));
        List<OnAWay> out = new ArrayList<>();
        for (OnAWay each : conditions) {
            boolean inIt = each.positions().stream().anyMatch(at -> heads.contains(at.head()));
            if (inIt && !saysNothingOfTheValuesOf(term, each, true)) {
                out.add(each);
            }
        }
        return out;
    }

    /**
     * Whether {@code statement} says nothing of the values {@code term} takes: it says only what
     * stands at a value around the term, or — where no rule may name the term — asks only other
     * places of an element the term is inside. A rule naming the term may relate it to those
     * places, so for such a term what is asked of them is said of it.
     *
     * @param named whether a rule of the declarations may name the term
     */
    private static boolean saysNothingOfTheValuesOf(NumericTerm.FromOnePosition term,
                                                    OnAWay statement, boolean named) {
        return statement.saysOnlyWhatStandsAround(term) || statement.leavesAlone(term)
                || (!named && statement.asksOnlyOtherPlacesOfTheElement(term));
    }

    /**
     * {@code form} held against nought as {@code rel}, as a statement about the difference of the
     * two sides — or null where it is over anything else, or weighs them other than one way and the
     * other.
     */
    private WhatARelationLeavesUndivided.OnTheDifference onTheDifference(
            LinearForm<NumericTerm> form, Rel rel) {
        ExactRatio first = form.coefs().get(sides.get(0).term());
        ExactRatio second = form.coefs().get(sides.get(1).term());
        if (form.coefs().size() != 2 || first == null || second == null
                || !(first.plus(second) instanceof ExactAnswer.Held<ExactRatio>(ExactRatio sum))
                || sum.signum() != 0) {
            return null;
        }
        return new WhatARelationLeavesUndivided.OnTheDifference(first, form.constant(), rel);
    }

    /** What a way does to a term: nothing, narrows where it runs over every value of the places it
     *  is related to, or more than this can read. */
    private enum Way {

        /** Nothing it states turns on any place the term is read off. */
        UNTOUCHED,

        /** What it states of those places is ends on the term itself, what stands at a value
         *  around it, or a relation the region took in over it and numbers of other places, and
         *  nothing else: that narrows where it runs, and what it ties the term to is asked
         *  apart ({@link TiedOnTheWay}). */
        NARROWED,

        /** Something it states of them is anything else: about a number of the same place other
         *  than the term, a value taken out, a statement the region did not take in. */
        TIES
    }

    /** What a way does to {@code term}, {@code stating} being what it states of the term
     *  ({@link #statingAnythingOf}). */
    private static Way wayOf(NumericTerm.FromOnePosition term, List<OnAWay> stating) {
        Way out = Way.UNTOUCHED;
        for (OnAWay each : stating) {
            // Which case the term's own value is takes values out of its order, which narrows it.
            if (!each.whatStands() && !inTheRegion(term, each)) {
                return Way.TIES;
            }
            out = Way.NARROWED;
        }
        return out;
    }

    /**
     * Whether {@code statement} is a relation the region took in over {@code term} alone, or over
     * it and numbers of other places, placing ends: what it leaves the term over every value of
     * those is the run the region answers whole ({@link SearchRegion#wholeRunOf}), and whatever
     * it ties the term to is asked apart ({@link TiedOnTheWay}). A form held against nought and an
     * end on one position's own order are both that. A relation over another number of a place
     * the term is read off — a string's length beside the string — is one the region holds as two
     * numbers it does not tie, so it is not this. Nor is a relation keeping the term off a value,
     * which leaves a hole where a run is answered by its ends.
     */
    private static boolean inTheRegion(NumericTerm.FromOnePosition term, OnAWay statement) {
        Set<NumericTerm> over = switch (statement.relation()) {
            case null -> Set.of();
            case TakenConstraint.Affine affine ->
                    affine.rel() == Rel.NE ? Set.of() : affine.form().coefs().keySet();
            case TakenConstraint.Ordered ordered -> Set.of(ordered.term());
            case TakenConstraint.AwayFrom _ -> Set.of();
        };
        if (!over.contains(term)) {
            return false;
        }
        for (NumericTerm each : over) {
            if (!each.equals(term) && touches(term, Set.of(each.subjectPath()))) {
                return false;
            }
        }
        return true;
    }

    /**
     * What the way ties the side at {@code at} to, as the classes of {@code tied} it is in: those
     * of every statement about a place the side is made of, save one saying nothing of the values
     * its term takes, and its parameter's where a rule of the declarations may name it. Two sides
     * in no class together are tied by nothing the way states.
     */
    private Set<Object> tiedTo(int at, TiedOnTheWay tied, List<OnAWay> conditions,
                               List<Source> sources, InputReading read) {
        Side side = sides.get(at);
        Set<Object> out = new HashSet<>();
        for (OnAWay each : conditions) {
            boolean about = side.readOff() == null
                    ? side.madeOf().stream().anyMatch(place -> each.positions().stream()
                            .anyMatch(that -> overlap(place.path(), that)))
                    : touches(side.readOff(), each.positions()) && !saysNothingOfTheValuesOf(
                            side.readOff(), each, mayBeNamed(at, sources));
            // What was kept of a seed the input holds is tied by what the way states of the seed.
            if (side.kept() != null
                    && side.kept().seed() instanceof Quantity.KeptSoFar.Seed.OfTheInput(var from)
                    && touches(from, each.positions())
                    && !saysNothingOfTheValuesOf(from, each, mayBeNamed(at, sources))) {
                about = true;
            }
            if (about) {
                out.add(tied.classOf(each.positions().iterator().next()));
            }
        }
        if (mayBeNamed(at, sources)) {
            for (FilingCoordinate place : placesAsked(side)) {
                for (Object node : tiedByTheDeclarations(place.path(), read)) {
                    out.add(tied.classOf(node));
                }
            }
        }
        return out;
    }

    /**
     * The places a way's statements tie together, in classes.
     *
     * <p>Two places are tied where a chain reaches from one to the other: a statement ties every
     * place it is about, the value one place sits in is tied to every place inside it, and a place
     * a rule of the declarations may name is tied to the parameter it is in, which the rule may
     * relate to anything else there. Generous where it is unsure — two places tied only through a
     * value the way leaves free are taken as tied — since a pair kept from one another by a third
     * place is not told from one that is not by anything the runs of each say. Worked out once for
     * a way and read by every pair of its sides.
     */
    private static final class TiedOnTheWay {

        /** The parameter a place is in, as one node every place under a value the rules leave
         *  nothing of is tied to. */
        private record Parameter(String head) {}

        /**
         * One rule of the value at {@code at}, as a node every place it may relate is tied to.
         *
         * @param worn   the name or declaration the rule is of
         * @param clause which of its clauses, or {@code -1} for a rule not read, which may relate
         *               anything under {@code at}
         */
        private record Rule(TermPath at, TypeSymbol worn, int clause) {}

        private final Map<Object, Object> parent = new HashMap<>();

        /**
         * The rules of the parameter {@code head}, in classes: the rules every place of it is read
         * by are joined, so that rules chaining from one place to another are in one class.
         */
        static TiedOnTheWay ofTheDeclarations(String head, InputReading read) {
            TiedOnTheWay out = new TiedOnTheWay();
            for (Position each : read.domain().positions()) {
                if (!each.path().head().equals(head)) {
                    continue;
                }
                Object first = null;
                for (Object node : reachedByTheDeclarations(each.path(), read).nodes().reads()) {
                    if (first == null) {
                        first = node;
                    } else {
                        out.join(first, node);
                    }
                }
            }
            return out;
        }

        static TiedOnTheWay of(List<OnAWay> conditions, InputReading read) {
            TiedOnTheWay out = new TiedOnTheWay();
            Set<TermPath> places = new LinkedHashSet<>();
            for (OnAWay each : conditions) {
                TermPath first = null;
                for (TermPath at : each.positions()) {
                    if (first == null) {
                        first = at;
                    } else {
                        out.join(first, at);
                    }
                    if (places.add(at)) {
                        for (Object node : tiedByTheDeclarations(at, read)) {
                            out.join(at, node);
                        }
                    }
                }
            }
            List<TermPath> all = List.copyOf(places);
            for (int i = 0; i < all.size(); i++) {
                for (int j = i + 1; j < all.size(); j++) {
                    if (overlap(all.get(i), all.get(j))) {
                        out.join(all.get(i), all.get(j));
                    }
                }
            }
            return out;
        }

        /** The class {@code node} is in, named by one node of it. */
        Object classOf(Object node) {
            Object at = node;
            for (Object up = parent.get(at); up != null; up = parent.get(at)) {
                at = up;
            }
            return at;
        }

        private void join(Object one, Object other) {
            Object first = classOf(one);
            Object second = classOf(other);
            if (!first.equals(second)) {
                parent.put(first, second);
            }
        }
    }

    /** Whether one of {@code positions} is a place {@code term} is read off, or one around it or
     *  under it. */
    private static boolean touches(NumericTerm.FromOnePosition term, Set<TermPath> positions) {
        for (TermPath place : term.placesReadOff()) {
            for (TermPath each : positions) {
                if (place.isAtOrUnder(each) || each.isAtOrUnder(place)) {
                    return true;
                }
            }
        }
        return false;
    }

    /** Whether every one of {@code positions} that a place {@code term} is read off touches is a
     *  value that place sits in, and not the place or one under it. */
    private static boolean onlyAround(NumericTerm.FromOnePosition term, Set<TermPath> positions) {
        for (TermPath place : term.placesReadOff()) {
            for (TermPath each : positions) {
                if (each.isAtOrUnder(place)) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * A run every value of which {@code term} is shown to take in {@code region}, or null where
     * none is shown.
     *
     * <p>A value no rule restricts, untouched on the way, takes every value of its type. Where a
     * way narrows it ({@link Way#NARROWED}), where the rules are ends on it and nothing else, or
     * where it is a number taken of a value no rule restricts, what it takes is the run the region
     * shows it fills ({@link SearchRegion#wholeRunOf}).
     *
     * @param source what the declarations leave the value {@code term} is, or is taken of
     */
    private static NumericDomain.Bounds realized(NumericTerm.FromOnePosition term, Source source,
                                                 SearchRegion region, Way way) {
        boolean every = source.takes().every();
        return switch (term) {
            case NumericTerm.ValueOf value -> every
                    ? way == Way.UNTOUCHED ? NumericDomain.Bounds.OPEN : region.wholeRunOf(value)
                    : source.onlyItsEnds() ? region.wholeRunOf(value) : null;
            case NumericTerm.TakenOf taken -> every && DefaultBoundOperationFacts.get()
                    .everyAnswerItCanGiveHasASourceValue(taken.operation())
                    ? region.wholeRunOf(taken) : null;
            case NumericTerm.CodePointClassCount _, NumericTerm.CodePointValueSum _ -> null;
        };
    }

    /**
     * What the declarations leave the value at a position, compared as one value with another's.
     *
     * <p>Every value of its type, or what the reading of the values there and the ends on it leave
     * it. Two claims and not one set, because the first is shown two ways: by that reading taking
     * in every rule there and finding nothing held back, or by a relation being the one rule it
     * did not take in and the bounds being shown to hold all the rules leave
     * ({@link Position#projection}). The second proves nothing about that reading, which still
     * did not take the relation in, so what it found is kept as it found it.
     */
    private sealed interface Takes {

        /** Every value {@code type} holds. */
        record Every(Type type) implements Takes {}

        /**
         * What {@code admitted} and {@code ends} leave of {@code type}.
         *
         * @param ends the ends the rules place on it ({@link #endsOf}), or null where none does
         */
        record Some(Type type, AdmissibleSet admitted, NumericDomain.Bounds ends)
                implements Takes {}

        default boolean every() {
            return this instanceof Every;
        }
    }

    /**
     * What the declarations leave the value at a position, with whether that is shown to be the
     * values between its ends.
     *
     * <p>Two answers and not one record, because only the first is what two values are compared
     * by. Whether the ends are shown to be all the rules say is a question about everything the
     * value sits in, and two positions of one declared type take the same values however much the
     * rules beside each were read.
     *
     * <p>And a third, whether a rule of a value it sits in names it. Such a rule leaves it the run
     * its bounds say, which are shown to be the whole of what the rules leave it, and may still
     * hold it beside the other places it names: under {@code x <= y}, each takes every value and
     * {@code x} above {@code y} is in no row. So a value a rule names is tied to nothing only
     * where what it is held beside is in another parameter, which no declaration relates it to.
     *
     * @param takes       what the declarations leave it
     * @param onlyItsEnds whether, where that is not every value, it is the values between the ends
     *                    and nothing else
     *                    ({@link #onlyItsEnds(Position, NumericTerm.ValueOf, boolean)})
     * @param named       whether a rule of a value it sits in names it
     */
    private record Source(Takes takes, boolean onlyItsEnds, boolean named) {}

    /**
     * What the declarations leave each position of one reading, kept with the reading.
     *
     * <p>A function of the position and the reading alone, asked again by every relation over the
     * position and by each way a row arrives at one along, and each asking walks the rules of every
     * value around the position. Empty where nothing is shown, since the map holds no null.
     */
    private static final class Left {

        private final Map<TermPath, Optional<Source>> byPosition = new ConcurrentHashMap<>();
    }

    /** What the declarations leave the value {@code term} is, or is taken of — or null where it is
     *  no such number, or nothing is shown ({@link #takes}). */
    private static Source sourceOf(NumericTerm.FromOnePosition term, InputReading read) {
        return switch (term) {
            case null -> null;
            case NumericTerm.ValueOf value -> takes(value, read);
            case NumericTerm.TakenOf taken ->
                    takes(new NumericTerm.ValueOf(taken.position()), read);
            case NumericTerm.CodePointClassCount _, NumericTerm.CodePointValueSum _ -> null;
        };
    }

    /**
     * What the declarations leave the element's number a walk kept an end of, as what the end
     * lies between: named only where a rule of the container, or of a value it sits in, reads a
     * place inside its elements. That is where a rule relating one element to another is written.
     * A rule of the element is about that one element, and what was kept is the number on the
     * others. And named where a seed the input holds is: what was kept is that seed too.
     */
    private static Source keptSource(Quantity.KeptSoFar kept, InputReading read) {
        Source each = sourceOf(kept.ofEach(), read);
        if (each == null) {
            return null;
        }
        boolean seedNamed = kept.seed() instanceof Quantity.KeptSoFar.Seed.OfTheInput(var from)
                && (sourceOf(from, read) == null || sourceOf(from, read).named());
        // A rule keeping elements apart by some field relates them to one another whichever field
        // the number is, so it is asked at the elements and not at the number.
        int deepest = kept.container().steps().size();
        return new Source(each.takes(), each.onlyItsEnds(), seedNamed
                || namedDownTo(kept.ofEach().subjectPath(), deepest, read, null) != Named.NOT
                || namedDownTo(kept.container().element(), deepest, read, null) == Named.UNSEEN);
    }

    /**
     * What the declarations leave {@code value}, or null where it is at no position read or a rule
     * of a value it sits in reads it and nothing shows what that leaves it.
     */
    private static Source takes(NumericTerm.ValueOf value, InputReading read) {
        Left left = read.derived(Left.class, _ -> new Left());
        // Not computeIfAbsent: a name the cases of a sum share is worked out by asking this of the
        // position under each case, which would update the map from inside its own update.
        Optional<Source> kept = left.byPosition.get(value.position());
        if (kept == null) {
            kept = Optional.ofNullable(worksOut(value, read));
            left.byPosition.put(value.position(), kept);
        }
        return kept.orElse(null);
    }

    /**
     * {@link #takes}, worked out.
     *
     * <p>A name the cases of a sum share stands at no position of its own but at one under each
     * case ({@link NameReach#standingOf}), and a row holds one case. So it is left what every case
     * leaves it where they leave it the same, and nothing is shown where they differ or where the
     * reading of some case stopped before putting the name anywhere: what one case leaves it is
     * not what it takes in a row of another. Its values are the values between its ends only where
     * every case shows that of it.
     */
    private static Source worksOut(NumericTerm.ValueOf value, InputReading read) {
        Position at = read.domain().at(value.position().position());
        if (at == null) {
            return read.domain().reach().standingOf(value.position())
                    instanceof NameReach.Standing.UnderTheCases(var standings)
                    ? takesUnderEvery(standings, read) : null;
        }
        // A rule naming the place relates it to the places beside it, which leaves it whatever its
        // bounds say only where they are shown to be the whole of what the rules leave it, and
        // where no end of its order cuts them.
        Named named = namedByTheDeclarations(value.position(), read);
        if (named == Named.UNSEEN || (named == Named.BY_A_RULE
                && (!at.projection().isCertified() || !wholeOnItsOrder(value, read)))) {
            return null;
        }
        boolean byARule = named == Named.BY_A_RULE;
        NumericDomain.Bounds ends = endsOf(at.boundsFor(value), byARule);
        AdmissibleSet admitted = at.admitted();
        // Every value where nothing holds any back: the reading of the values here took every rule
        // in, or the relation is the one rule it did not and the bounds, shown to hold all the
        // rules leave, place no end on any number of it. An end on how long a string is keeps it
        // from the longer ones.
        boolean every = ends == null && admitted.approximation().isAny()
                && (admitted.completeness() instanceof AdmissibleSet.Completeness.Complete
                        || (byARule && onlyARelationWentUnread(admitted)
                                && at.bounds().stream()
                                        .allMatch(each -> endsOf(each, true) == null)));
        Takes takes = every ? new Takes.Every(at.type())
                : new Takes.Some(at.type(), admitted, ends);        return new Source(takes, !every && onlyItsEnds(at, value, byARule), byARule);
    }

    /** Whether the order {@code value} is counted on leaves a run the arithmetic gives it whole
     *  ({@link Carrier#leavesARelatedRunWhole}) — not where it is counted on none. */
    private static boolean wholeOnItsOrder(NumericTerm.ValueOf value, InputReading read) {
        TermOrders orders = read.quantities().ordersOf(value);
        return orders != null && orders.answered() != null
                && orders.answered().leavesARelatedRunWhole();
    }

    /**
     * The ends the rules place on a number, or null where none does or the position has no such
     * number. A rule naming the place holds it beside the places it names, so what it leaves the
     * number is where it stops once every rule reaching the value is taken in: under
     * {@code issuedOn >= 0 && expiresOn >= issuedOn} no rule places an end on {@code expiresOn},
     * and it stops at nought. A range with neither end is no end.
     */
    private static NumericDomain.Bounds endsOf(PositionBounds bounds, boolean byARule) {
        if (bounds == null) {
            return null;
        }
        NumericDomain.Bounds ends = byARule ? bounds.rangeLeft() : bounds.admissible();
        return ends == null || ends.saysNothing() ? null : ends;
    }

    /** Whether all that kept {@code admitted} from being the values the rules leave is a rule
     *  relating the place to another, which the reading of one place's values does not read. */
    private static boolean onlyARelationWentUnread(AdmissibleSet admitted) {
        return admitted.completeness() instanceof AdmissibleSet.Completeness.Wider(
                Set<AdmissibleSet.Widening> why)
                && why.stream().allMatch(each -> each
                        instanceof AdmissibleSet.Widening.RuleUnread(StoppedReading stopped)
                        && stopped.why() == UnreadReason.RELATES_TWO_POSITIONS);
    }

    /**
     * Whether the ends the declarations place on {@code value} are all they say of the position:
     * the bounds are shown to be the whole of what the rules of the value it sits in leave
     * ({@link Position#projection}), and no other number of the position is bounded. A bound on
     * another number — how long a string is — keeps the value from some of its own values, which
     * the ends on it do not say.
     *
     * @param byARule whether a rule of a value it sits in names it, so that what bounds each number
     *                is where it stops once every rule is taken in ({@link #endsOf})
     */
    private static boolean onlyItsEnds(Position at, NumericTerm.ValueOf value, boolean byARule) {
        if (!at.projection().isCertified()) {
            return false;
        }
        for (PositionBounds each : at.bounds()) {
            if (!each.term().equals(value) && endsOf(each, byARule) != null) {
                return false;
            }
        }
        return true;
    }

    /** What every one of {@code standings} leaves the value there, where that is one answer, or
     *  null. */
    private static Source takesUnderEvery(List<NameReach.CaseStanding> standings,
                                          InputReading read) {
        Source out = null;
        for (NameReach.CaseStanding each : standings) {
            Source here = takes(new NumericTerm.ValueOf(each.position()), read);
            if (here == null || (out != null && !out.takes().equals(here.takes()))) {
                return null;
            }
            out = out == null ? here
                    : new Source(here.takes(), out.onlyItsEnds() && here.onlyItsEnds(),
                            out.named() || here.named());
        }
        return out;
    }

    /**
     * The rules of each name {@link #namedByTheDeclarations} read, and what it answered of each
     * place, kept with the reading: what a position is left is kept per position ({@link Left}),
     * many positions sit in one value, and every way a relation is asked along asks again of the
     * places its statements are about.
     */
    private record RulesRead(Map<TypeSymbol.AtModule, PublishedRules> byName,
                             Map<TermPath, Reached> byPlace,
                             Map<String, TiedOnTheWay> declared,
                             Map<Written, List<TermPath>> placed) {

        static RulesRead of(InputReading read) {
            return read.derived(RulesRead.class, _ -> new RulesRead(
                    new ConcurrentHashMap<>(), new ConcurrentHashMap<>(),
                    new ConcurrentHashMap<>(), new ConcurrentHashMap<>()));
        }
    }

    /**
     * What the rules around a place say of it, and the rules they say it of.
     *
     * @param named what they say ({@link #namedByTheDeclarations})
     * @param nodes the rules that say it
     */
    private record Reached(Named named, Nodes nodes) {}

    /**
     * The rules around a place, one node per clause of a value around it.
     *
     * @param ties  the clauses that read something at, under, past or around the place. Two places
     *              are tied by the declarations where their classes of these meet, and only then: a
     *              rule of a value relates places in that value, so places the rules of no value
     *              around both read are in no way related by them. Empty where the place is
     *              {@link Named#NOT} named.
     * @param reads the clauses that read the place itself, or a value it is a part of whole. Where
     *              a place is read by two clauses, what each relates to it is related to what the
     *              other does; a clause that reads only parts of the place is no such meeting
     *              point, since two parts of a value are not one value.
     */
    private record Nodes(Set<Object> ties, Set<Object> reads) {

        Nodes() {
            this(new LinkedHashSet<>(), new LinkedHashSet<>());
        }

        /** A rule nothing says what it reads: it may relate anything under {@code node}'s place. */
        void unread(Object node) {
            ties.add(node);
            reads.add(node);
        }
    }

    /**
     * What the rules around {@code path} say of it, with the places a name the cases of a sum share
     * stands at asked as {@link NameReach#standingOf} puts them. Not {@code computeIfAbsent}: the
     * place a name stands at can itself be a name that crosses, which asks this again of the same
     * map.
     */
    private static Reached reachedByTheDeclarations(TermPath path, InputReading read) {
        Map<TermPath, Reached> known = RulesRead.of(read).byPlace();
        Reached reached = known.get(path);
        if (reached == null) {
            reached = reachedWorkedOut(path, read);
            known.put(path, reached);
        }
        return reached;
    }

    private static Reached reachedWorkedOut(TermPath path, InputReading read) {
        if (read.domain().at(path.position()) == null) {
            NameReach.Standing standing = read.domain().reach().standingOf(path);
            boolean incomplete = standing instanceof NameReach.Standing.CasesIncomplete;
            List<NameReach.CaseStanding> standings = switch (standing) {
                case NameReach.Standing.UnderTheCases(var each) -> each;
                case NameReach.Standing.CasesIncomplete(var each, var _) -> each;
                default -> null;
            };
            if (standings != null) {
                // A row holds one case, so the rules of every case the name stands under are the
                // rules around it; a case the reading stopped in may hold any rule at all.
                Named named = incomplete ? Named.UNSEEN : Named.NOT;
                Nodes nodes = new Nodes();
                if (incomplete) {
                    nodes.unread(new TiedOnTheWay.Parameter(path.head()));
                }
                for (NameReach.CaseStanding each : standings) {
                    Reached under = reachedByTheDeclarations(each.position(), read);
                    named = named.and(under.named());
                    nodes.ties().addAll(under.nodes().ties());
                    nodes.reads().addAll(under.nodes().reads());
                }
                return new Reached(named, nodes);
            }
        }
        Nodes nodes = new Nodes();
        return new Reached(namedDownTo(path, path.steps().size() - 1, read, nodes), nodes);
    }

    /**
     * The classes the rules around {@code path} are in ({@link Nodes#ties}), where two rules are in
     * one class if some place of the parameter is read by both ({@link Nodes#reads}).
     */
    private static Set<Object> tiedByTheDeclarations(TermPath path, InputReading read) {
        TiedOnTheWay declared = RulesRead.of(read).declared().computeIfAbsent(path.head(),
                head -> TiedOnTheWay.ofTheDeclarations(head, read));
        Set<Object> out = new LinkedHashSet<>();
        for (Object node : reachedByTheDeclarations(path, read).nodes().ties()) {
            out.add(declared.classOf(node));
        }
        return out;
    }

    /**
     * What the rules of the values a position sits in say of it: nothing, that one names it, or
     * nothing anyone can tell.
     *
     * <p>In the order they hold more back, which is the order two of them are put together in.
     */
    private enum Named {

        /** No rule of a value around it reads it, so none ties it to anything. */
        NOT,

        /**
         * A rule reads the value at the place itself, by the chain of fields down to it. What it
         * leaves the place is in the place's bounds, and is all of it where those are shown to be
         * the whole of what the rules leave ({@link Position#projection}).
         */
        BY_A_RULE,

        /** A rule reads it some way its bounds do not say what that leaves it — a value around
         *  it, or past an element or a case — or a rule was not read at all, or no value around
         *  it is there to be read. */
        UNSEEN;

        Named and(Named other) {
            return compareTo(other) >= 0 ? this : other;
        }
    }

    /**
     * What the rules of every value {@code path} sits in say of it: some value around it — the
     * parameter itself, and every value between — wears a name, or is a declaration, with a rule
     * that reads a place at, under or around what stands at {@code path}.
     *
     * <p>A rule on the position's own type is about it alone and ties it to nothing; one on a
     * value around it is where a rule over two of its positions is written. A rule there that reads
     * only places beside the path leaves every value of the path standing beside some value of the
     * rest — what it holds back is which of the rest stand together — and one reading a container
     * around the path for nothing but how many it holds leaves its elements every value, wherever
     * it may hold one. Both rest on some value of the rest being there, so a value around it the
     * rules leave none of is unseen. And so is a value around it the reading holds no position for,
     * which nothing can be said of.
     *
     * <p>A name the value wears and the declaration it is are asked alike: the rules of each call
     * a place by the fields read down from the value, a newtype's own {@code value} being the value
     * itself ({@link ClauseRead}).
     */
    private static Named namedByTheDeclarations(TermPath path, InputReading read) {
        return reachedByTheDeclarations(path, read).named();
    }

    /**
     * What the rules of the values {@code path} sits in say of it, of those {@code deepest} steps
     * down from the parameter or fewer ({@link #namedByTheDeclarations}).
     *
     * <p>Where {@code nodes} is given, every rule is asked and those that read something of the
     * path are added to it; without it the answer stops at the first unseen.
     */
    private static Named namedDownTo(TermPath path, int deepest, InputReading read,
                                     Nodes nodes) {
        List<TermPath.Step> steps = path.steps();
        Named out = Named.NOT;
        for (int length = 0; length <= deepest && length < steps.size(); length++) {
            TermPath here = new TermPath(path.head(), steps.subList(0, length));
            Position around = read.domain().at(here.position());
            // Where the rules leave no value of it, nothing stands beside the rest of it either.
            if (around == null || around.nothingExists()) {
                if (nodes != null) {
                    nodes.unread(new TiedOnTheWay.Parameter(path.head()));
                }
                return Named.UNSEEN;
            }
            List<TypeSymbol> worn = new ArrayList<>(around.view().wrappers());
            switch (around.view().shape()) {
                case Shape.Product product -> worn.add(product.name());
                case Shape.Sum sum -> worn.add(sum.name());
                default -> { }
            }
            List<TermPath.Step> rest = steps.subList(length, steps.size());
            for (TypeSymbol each : worn) {
                out = out.and(namedBy(each, here, path, rest, read, nodes));
                if (out == Named.UNSEEN && nodes == null) {
                    return out;
                }
            }
        }
        return out;
    }

    /**
     * What a rule of {@code worn} says of what stands at {@code rest} below {@code here}: unseen
     * where one was not reached or has no form to say what it reads.
     */
    private static Named namedBy(TypeSymbol worn, TermPath here, TermPath place,
                                 List<TermPath.Step> rest, InputReading read, Nodes nodes) {
        if (!(worn instanceof TypeSymbol.AtModule name)) {
            return Named.NOT;
        }
        PublishedRules rules = RulesRead.of(read).byName().computeIfAbsent(name,
                each -> PublishedRules.governing(each, read.rules().published()));
        if (!rules.everyRuleReached()) {
            if (nodes != null) {
                nodes.unread(new TiedOnTheWay.Rule(here, worn, -1));
            }
            return Named.UNSEEN;
        }
        Named out = Named.NOT;
        List<ClauseMeaning> reached = rules.reached();
        for (int clause = 0; clause < reached.size(); clause++) {
            if (!(reached.get(clause) instanceof ClauseMeaning.Stated stated)) {
                if (nodes == null) {
                    return Named.UNSEEN;
                }
                nodes.unread(new TiedOnTheWay.Rule(here, worn, -1));
                out = Named.UNSEEN;
                continue;
            }
            for (ClauseRead reading : stated.reads()) {
                Named says = namedBy(reading, here, place, rest, read);
                out = out.and(says);
                if (says != Named.NOT && nodes != null) {
                    TiedOnTheWay.Rule rule = new TiedOnTheWay.Rule(here, worn, clause);
                    nodes.ties().add(rule);
                    if (readsThePlace(reading, here, place, read)) {
                        nodes.reads().add(rule);
                    }
                }
                if (out == Named.UNSEEN && nodes == null) {
                    return out;
                }
            }
        }
        return out;
    }

    /**
     * Whether {@code reading}, written in the rules of the value at {@code here}, reads
     * {@code place} or a value it is a part of whole; and not only parts of it, nor the places
     * beside it.
     *
     * <p>Asked of the positions the name stands at ({@link InputDomain#positionsNamed}), which is
     * where a name a sum's cases share stands under each of them. Where none is found the reading
     * is placed nowhere, and a rule that cannot be placed may read anything under {@code here}.
     */
    private static boolean readsThePlace(ClauseRead reading, TermPath here, TermPath place,
                                         InputReading read) {
        List<TermPath> reached = placesRead(reading, here, read);
        if (reached.isEmpty()) {
            return true;
        }
        for (TermPath each : reached) {
            boolean reads = reading.kind() == ClauseRead.Kind.HOW_MANY_IT_HOLDS
                    ? place.equals(each) : place.isAtOrUnder(each);
            if (reads) {
                return true;
            }
        }
        return false;
    }

    /**
     * The positions {@code reading}, written in the rules of the value at {@code here}, reads: where
     * its name stands, and for the fields of each element, where those stand in each element. The
     * one place a reading is put at positions, so that what a rule leaves a place and what a rule
     * relates it to are asked of the same positions.
     *
     * <p>Empty where some name stands nowhere this reading put a position at.
     */
    private static List<TermPath> placesRead(ClauseRead reading, TermPath here, InputReading read) {
        return RulesRead.of(read).placed().computeIfAbsent(new Written(here, reading), each -> {
            List<TermPath> named = read.domain().positionsNamed(here, reading.at());
            if (reading.kind() != ClauseRead.Kind.EACH_ELEMENTS_RUN) {
                return named;
            }
            List<TermPath> out = new ArrayList<>();
            for (TermPath container : named) {
                List<TermPath> run = read.domain().positionsNamed(container.element(),
                        reading.run());
                if (run.isEmpty()) {
                    return List.of();
                }
                out.addAll(run);
            }
            return out;
        });
    }

    /** A reading written in the rules of the value at {@code root}. */
    private record Written(TermPath root, ClauseRead reading) {}

    /**
     * What a clause reading {@code reading} says of what stands at {@code rest} below
     * {@code here}.
     *
     * <p>A rule names a place by fields alone ({@code RuleKey}), and a path
     * goes on past its fields into an element or a case. So the two are held against each other
     * along the fields the path starts with. They part where a field differs, and then the rule
     * reads beside the path. Where the rule's place is the path, by fields all the way, it reads
     * the value there. Where it goes on below those fields it is under the path, or past a step no
     * chain of fields names. Where it stops above them it reads what the path stands in —
     * everything there, unless what it reads is how many a container holds and the path goes on
     * into the elements.
     */
    private static Named namedBy(ClauseRead reading, TermPath here, TermPath place,
                                 List<TermPath.Step> rest, InputReading read) {
        int fields = 0;
        while (fields < rest.size() && rest.get(fields) instanceof TermPath.Step.Field) {
            fields++;
        }
        List<String> at = reading.at().steps();
        for (int i = 0; i < at.size() && i < fields; i++) {
            if (!at.get(i).equals(((TermPath.Step.Field) rest.get(i)).name())) {
                return Named.NOT;
            }
        }
        if (at.size() == fields && fields == rest.size()
                && reading.kind() == ClauseRead.Kind.ITS_VALUES) {
            return Named.BY_A_RULE;
        }
        if (reading.kind() == ClauseRead.Kind.EACH_ELEMENTS_RUN) {
            return namedByARunOfEachElement(reading, here, place, read);
        }
        if (at.size() > fields || reading.kind() != ClauseRead.Kind.HOW_MANY_IT_HOLDS) {
            return Named.UNSEEN;
        }
        // How many a container holds, read at or above where the path stops going by fields. Only
        // where the container is exactly there and the path goes on into it is that apart from
        // what stands at the path.
        if (at.size() != fields || fields == rest.size()) {
            return Named.UNSEEN;
        }
        List<TermPath.Step> container = new ArrayList<>(here.steps());
        container.addAll(rest.subList(0, fields));
        return mayHoldOne(new TermPath(here.head(), container), read) ? Named.NOT : Named.UNSEEN;
    }

    /**
     * What a rule reading a run of each element says of {@code place}: nothing where the positions
     * it reads are neither the place, nor under it, nor a value it is a part of — the rule then
     * reads other fields of the elements — and unseen where they are, or where they are placed
     * nowhere.
     */
    private static Named namedByARunOfEachElement(ClauseRead reading, TermPath here,
                                                  TermPath place, InputReading read) {
        List<TermPath> reached = placesRead(reading, here, read);
        if (reached.isEmpty()) {
            return Named.UNSEEN;
        }
        for (TermPath each : reached) {
            if (place.isAtOrUnder(each) || each.isAtOrUnder(place)) {
                return Named.UNSEEN;
            }
        }
        return Named.NOT;
    }

    /**
     * Whether the container at {@code at} is shown to hold one element beside some value of
     * everything else: some value of it exists, and one is in a run of how many it holds that the
     * rules are shown to leave whole ({@link SearchRegion#wholeRunOf}) — so some value holds
     * exactly one.
     *
     * <p>One and not one or more. A container holding one element holds it whatever value it is —
     * no second element is there to be apart from — so one taken is every value of the elements
     * standing in some value. More than one asks the element's type for that many values apart,
     * which a type holding fewer does not have.
     *
     * <p>Shown of the count, not of the value whole. Whether the rules of everything the
     * container sits in project exactly is a question about all of them, and a pattern a field
     * beside it is held to says nothing of how many it holds.
     */
    private static boolean mayHoldOne(TermPath at, InputReading read) {
        Position container = read.domain().at(at.position());
        if (container == null || container.nothingExists()) {
            return false;
        }
        for (PositionBounds each : container.bounds()) {
            if (each.term() instanceof NumericTerm.TakenOf taken
                    && taken.takenAs() instanceof TakenAs.HowManyItHolds) {
                NumericDomain.Bounds whole = read.quantities().region().wholeRunOf(taken);
                return whole != null && whole.admits(ExactRatio.ONE);
            }
        }
        return false;
    }

    private static boolean overlap(FilingCoordinate one, FilingCoordinate other) {
        return overlap(one.path(), other.path());
    }

    /** Whether two places are one, or one is inside the other. */
    private static boolean overlap(TermPath one, TermPath other) {
        return one.isAtOrUnder(other) || other.isAtOrUnder(one);
    }
}
