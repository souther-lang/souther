package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.check.ClauseMeaning;
import souther.compiler.check.ClauseRead;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.PublishedRules;
import souther.compiler.check.Shape;
import souther.compiler.inputs.FilingCoordinate;
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
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.values.AdmissibleSet;
import souther.compiler.values.StoppedReading;
import souther.compiler.values.UnreadReason;

import java.util.ArrayList;
import java.util.Arrays;
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
 * the ends: a way placing an end on the term itself narrows where it runs, and what the region then
 * leaves it is taken only as the region answers it whole ({@link SearchRegion#wholeRunOf}) — never
 * put together from where the values lie and a proof given beside it, since the one may be rounded
 * past the rules and the other is not about that. And that nothing ties it to another place. A term
 * that takes every value alone may take only some of them beside a value of another term: under
 * {@code x + y <= 1} over nought and one, {@code x} at one is beside no {@code y} at one. Runs say
 * nothing of that — the runs of each, and of every sum and difference of the two, can be what they
 * would be untied — so what is asked is whether anything could tie the term to the others. Nothing
 * a way states ties it where it states nothing of the term but ends on itself, which case a value
 * around it is and how many a value around it holds: nothing a way took in turns on another number
 * with it, or on another number of the place it is taken of — a date on the twenty-ninth of
 * February is in a leap year; and nothing a way stated and none of this took in. Where one does,
 * nothing is shown of the term. The declarations tie it to nothing where no rule of a value it sits
 * in reads a place at, under or around it, other than for how many a container around it holds,
 * which is where a rule over two of its positions is written. A rule that reads the value at its
 * place and nothing around it leaves it the run its bounds say, where those are shown to be the
 * whole of what the rules leave ({@link Position#projection}): {@code expiresOn >= issuedOn} with
 * {@code issuedOn} free leaves {@code expiresOn} every value. It still holds the value beside the
 * places it names, so such a value is tied to nothing only by a term in another parameter, which
 * no declaration relates to it, and a way stating anything of a place of its parameter ties it.
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
 * @param sides           the terms of the relation
 * @param constant        what the terms are held against, or null where that is no number
 * @param relation        how the terms are held against it
 * @param amongThemselves the places whose values it holds against other values of the same place,
 *                        and nothing else
 */
record UndividedByARelation(List<Side> sides, ExactRatio constant, Rel relation,
                            List<FilingCoordinate> amongThemselves) {

    /** A relation that shows no place undivided: one nothing here takes apart. */
    static final UndividedByARelation SHOWING_NOTHING =
            new UndividedByARelation(List.of(), ExactRatio.ZERO, Rel.EQ, List.of());

    UndividedByARelation {
        sides = List.copyOf(sides);
        amongThemselves = List.copyOf(amongThemselves);
    }

    /** The values at {@code at} held against other values at {@code at}. */
    static UndividedByARelation amongTheValuesAt(TermPath at) {
        return new UndividedByARelation(List.of(), ExactRatio.ZERO, Rel.EQ,
                List.of(FilingCoordinate.at(at)));
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
     */
    record Side(List<FilingCoordinate> madeOf, ExactRatio weight,
                NumericTerm.FromOnePosition term) {

        Side {
            madeOf = List.copyOf(madeOf);
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
                        each.getValue(), null);
                default -> new Side(List.of(), each.getValue(), null);
            });
        }
        return new UndividedByARelation(sides, form.constant(), relation, List.of());
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
        return new UndividedByARelation(sides, constant, relation, List.of());
    }

    /** The values at two positions held as one value, or not. */
    static UndividedByARelation ofTwoPositions(TermPath one, TermPath other) {
        return new UndividedByARelation(List.of(
                new Side(List.of(FilingCoordinate.at(one)), ExactRatio.ONE,
                        new NumericTerm.ValueOf(one)),
                new Side(List.of(FilingCoordinate.at(other)), ExactRatio.ONE.negated(),
                        new NumericTerm.ValueOf(other))), ExactRatio.ZERO, Rel.EQ, List.of());
    }

    private static Side ofTheInput(NumericTerm term, ExactRatio weight) {
        return new Side(List.of(FilingCoordinate.of(term)), weight,
                term instanceof NumericTerm.FromOnePosition one ? one : null);
    }

    /** The places shown undivided over what the declarations leave. */
    Set<FilingCoordinate> undivided(InputReading read) {
        return undividedWhereRowsArrive(read, List.of());
    }

    /**
     * The places shown undivided over the rows that arrive at the relation along {@code ways} —
     * over what the declarations leave, where there are none.
     *
     * <p>Shown along each way apart, and a place is left undivided where every way shows it. Two
     * ways put together run over more than either, and what a term takes beside another along both
     * is not what it takes along each: the runs of each may join without a gap while a pair one way
     * keeps out is one the other never reaches. Nothing here shows what they come to together. A
     * way split at a choice is each of its branches, so each is a way here, and a way some of whose
     * branches were not split out shows nothing.
     */
    Set<FilingCoordinate> undividedWhereRowsArrive(InputReading read,
                                                   List<Reachability.Reaching> ways) {
        // What the declarations leave each side, which no way changes: asked once for all of them.
        List<Source> sources = new ArrayList<>();
        for (Side each : sides) {
            sources.add(switch (each.term()) {
                case null -> null;
                case NumericTerm.ValueOf value -> takes(value, read);
                case NumericTerm.TakenOf taken ->
                        takes(new NumericTerm.ValueOf(taken.position()), read);
                case NumericTerm.CodePointClassCount _ -> null;
            });
        }
        // And the order each side's values are counted on, which says where its type ends.
        List<Carrier> carriers = new ArrayList<>();
        for (Side each : sides) {
            TermOrders orders = each.term() == null ? null
                    : read.quantities().ordersOf(each.term());
            carriers.add(orders == null ? null : orders.answered());
        }
        // Where each side stands is compared with where the others do, which says something only
        // where they stand on one order: a case of one enumeration has no place on another's.
        // Nothing a side is shown to take is then a place on another's order, and two values of
        // two orders never take the same values, so nothing is shown of any of them.
        for (Carrier one : carriers) {
            for (Carrier other : carriers) {
                if (one != null && other != null && !Carrier.onOneOrder(one, other)) {
                    return new LinkedHashSet<>(amongThemselves);
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
            return undividedAlong(sources, carriers, read.quantities().region(), List.of(), true);
        }
        List<Reachability.Reaching> branches = new ArrayList<>();
        for (Reachability.Reaching each : ways) {
            if (!branchesOf(each, branches)) {
                return new LinkedHashSet<>(amongThemselves);
            }
        }
        Set<FilingCoordinate> out = null;
        for (Reachability.Reaching each : branches) {
            Set<FilingCoordinate> along = undividedAlong(sources, carriers, each.region(),
                    conditionsOf(each), each.declined().isEmpty());
            if (out == null) {
                out = along;
            } else {
                out.retainAll(along);
            }
        }
        return out;
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
            NumericTerm runOf = taken.demand() instanceof RowDemand.Relational(
                    TakenConstraint.Affine(LinearForm<NumericTerm> form, Rel rel))
                    && rel != Rel.NE && form.coefs().size() == 1
                    ? form.coefs().keySet().iterator().next() : null;
            out.add(new OnAWay(taken.demand().positions(), runOf,
                    runOf instanceof NumericTerm.TakenOf count
                            && count.takenAs() instanceof TakenAs.HowManyItHolds,
                    taken.demand() instanceof RowDemand.Relational(
                            TakenConstraint.Affine affine) ? affine : null));
        });
        way.requirements().refinements().keySet()
                .forEach(at -> out.add(new OnAWay(Set.of(at), null, true, null)));
        way.requirements().atANameTheCasesShare()
                .forEach(at -> out.add(new OnAWay(Set.of(at), null, true, null)));
        return out;
    }

    /**
     * One statement of a way.
     *
     * @param positions the positions it turns on
     * @param runOf      the one number it places an end on, where it is an end on one number and
     *                   nothing else; null where it is anything else
     * @param whatStands whether it says what stands at a value and nothing of the values that
     *                   stand there beside another: which case the value is, or ends on how many
     *                   it holds. Either of a value around a term says nothing of the term's
     *                   values — an element is reached only where the container holds one, and
     *                   holding one says nothing of what it is. Of the term's own value, a case,
     *                   as an enumeration's, is a value taken out of its order, which the region
     *                   holds, and an end on how many is an end on the term itself
     * @param affine     what it states as a form of the input's numbers held against nought, or
     *                   null where it states anything else
     */
    private record OnAWay(Set<TermPath> positions, NumericTerm runOf, boolean whatStands,
                          TakenConstraint.Affine affine) {}

    /**
     * The places shown undivided over the rows in {@code region}, a way stating
     * {@code conditions} there.
     *
     * @param sources  what the declarations leave the value each side is, or is taken of, in the
     *                 order of the sides
     * @param carriers the order each side is counted on, or null where it has none
     */
    private Set<FilingCoordinate> undividedAlong(List<Source> sources, List<Carrier> carriers,
                                                 SearchRegion region, List<OnAWay> conditions,
                                                 boolean heldWhole) {
        List<WhatARelationLeavesUndivided.Term<FilingCoordinate>> terms = new ArrayList<>();
        // What the way states of each side, asked once and read by both readings.
        List<List<OnAWay>> stating = new ArrayList<>();
        for (int i = 0; i < sides.size(); i++) {
            Side each = sides.get(i);
            // A value a rule names moves with the places the rule names beside it, so what the
            // way states of any place of its parameter is stated of it.
            stating.add(each.term() == null || !heldWhole ? List.of()
                    : sources.get(i) != null && sources.get(i).named()
                    ? statingAnythingOfItsParameter(each.term(), conditions)
                    : statingAnythingOf(each.term(), conditions));
            NumericDomain.Bounds holds = asARelationReadsIt(each.term() != null
                    && region.projectionOf(each.term())
                    instanceof NumericDomain.FormProjection.Within(NumericDomain.Bounds within)
                    ? within : NumericDomain.Bounds.OPEN, carriers.get(i));
            Way way = each.term() == null || !heldWhole ? Way.TIES
                    : wayOf(each.term(), stating.get(i));
            Source source = way == Way.TIES ? null : sources.get(i);
            NumericDomain.Bounds realizes = source == null ? null
                    : asARelationReadsIt(realized(each.term(), source, region, way),
                            carriers.get(i));
            Takes takes = source != null && way == Way.UNTOUCHED
                    && each.term() instanceof NumericTerm.ValueOf ? source.takes() : null;
            terms.add(new WhatARelationLeavesUndivided.Term<>(each.madeOf(), each.weight(), holds,
                    realizes, takes, each.term() instanceof NumericTerm.ValueOf));
        }
        Set<FilingCoordinate> out = new LinkedHashSet<>(amongThemselves);
        // A way that states of a term anything past an end on it leaves the term nothing it is
        // shown to take (wayOf), so what is asked of a pair is what the declarations tie.
        out.addAll(WhatARelationLeavesUndivided.of(terms, constant, relation,
                UndividedByARelation::overlap,
                (one, other) -> apartByTheDeclarations(one, other, sources)));
        if (!out.containsAll(places())) {
            out.addAll(undividedByTheDifference(sources, carriers, stating, heldWhole));
        }
        return out;
    }

    /**
     * Whether nothing the declarations say ties where the side at {@code one} lies to where the
     * side at {@code other} does: one of them is a value no rule of a value it sits in names, or
     * the two are in different parameters, which no declaration relates. A side nothing is worked
     * out of may be named by anything.
     *
     * @param sources what the declarations leave each side, in the order of the sides
     */
    private boolean apartByTheDeclarations(int one, int other, List<Source> sources) {
        if (!mayBeNamed(one, sources) || !mayBeNamed(other, sources)) {
            return true;
        }
        List<FilingCoordinate> first = sides.get(one).madeOf();
        List<FilingCoordinate> second = sides.get(other).madeOf();
        if (first.isEmpty() || second.isEmpty()) {
            return false;
        }
        for (FilingCoordinate each : first) {
            for (FilingCoordinate that : second) {
                if (each.path().head().equals(that.path().head())) {
                    return false;
                }
            }
        }
        return true;
    }

    /** Whether a rule of a value the side at {@code at} sits in may name it. */
    private boolean mayBeNamed(int at, List<Source> sources) {
        Source source = sources.get(at);
        return sides.get(at).term() == null || source == null || source.named();
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
                                                         boolean heldWhole) {
        if (!heldWhole || sides.size() != 2 || carriers.get(0) == null
                || !carriers.get(0).equals(carriers.get(1))
                || !apartByTheDeclarations(0, 1, sources)) {
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
                    on.asARelationReadsIt(), on.asARelationReadsIt(), source.takes(), true));
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
     * stands at a value around the term says nothing of the values the term takes, so a statement
     * of only that is left out.
     */
    private static List<OnAWay> statingAnythingOf(NumericTerm.FromOnePosition term,
                                                  List<OnAWay> conditions) {
        List<OnAWay> out = new ArrayList<>();
        for (OnAWay each : conditions) {
            if (touches(term, each.positions())
                    && !(each.whatStands() && onlyAround(term, each.positions()))) {
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
            if (inIt && !(each.whatStands() && touches(term, each.positions())
                    && onlyAround(term, each.positions()))) {
                out.add(each);
            }
        }
        return out;
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

    /** What a way does to a term: nothing, an end on it alone, or more than this can read. */
    private enum Way {

        /** Nothing it states turns on any place the term is read off. */
        UNTOUCHED,

        /** What it states of those places is ends on the term itself, or what stands at a value
         *  around it, and nothing else: that narrows where it runs and ties it to nothing. */
        NARROWED,

        /** Something it states of them is anything else: about another number with it, about a
         *  number of the same place other than the term, a value taken out. */
        TIES
    }

    /** What a way does to {@code term}, {@code stating} being what it states of the term
     *  ({@link #statingAnythingOf}). */
    private static Way wayOf(NumericTerm.FromOnePosition term, List<OnAWay> stating) {
        Way out = Way.UNTOUCHED;
        for (OnAWay each : stating) {
            // Which case the term's own value is takes values out of its order, which narrows it.
            if (!each.whatStands() && !term.equals(each.runOf())) {
                return Way.TIES;
            }
            out = Way.NARROWED;
        }
        return out;
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
     * way places ends on it, where the rules are ends on it and nothing else, or where it is a number
     * taken of a value no rule restricts, what it takes is the run the region shows it fills
     * ({@link SearchRegion#wholeRunOf}).
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
            case NumericTerm.CodePointClassCount _ -> null;
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
     * The rules of each name {@link #namedByTheDeclarations} read, kept with the reading: what a
     * position is left is kept per position ({@link Left}), and many positions sit in one value.
     */
    private record RulesRead(Map<TypeSymbol.AtModule, PublishedRules> byName) {

        static RulesRead of(InputReading read) {
            return read.derived(RulesRead.class, _ -> new RulesRead(new ConcurrentHashMap<>()));
        }
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
        List<TermPath.Step> steps = path.steps();
        Named out = Named.NOT;
        for (int length = 0; length < steps.size(); length++) {
            TermPath here = new TermPath(path.head(), steps.subList(0, length));
            Position around = read.domain().at(here.position());
            // Where the rules leave no value of it, nothing stands beside the rest of it either.
            if (around == null || around.nothingExists()) {
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
                out = out.and(namedBy(each, here, rest, read));
                if (out == Named.UNSEEN) {
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
    private static Named namedBy(TypeSymbol worn, TermPath here, List<TermPath.Step> rest,
                                 InputReading read) {
        if (!(worn instanceof TypeSymbol.AtModule name)) {
            return Named.NOT;
        }
        PublishedRules rules = RulesRead.of(read).byName().computeIfAbsent(name,
                each -> PublishedRules.governing(each, read.rules().published()));
        if (!rules.everyRuleReached()) {
            return Named.UNSEEN;
        }
        Named out = Named.NOT;
        for (ClauseMeaning each : rules.reached()) {
            if (!(each instanceof ClauseMeaning.Stated stated)) {
                return Named.UNSEEN;
            }
            for (ClauseRead reading : stated.reads()) {
                out = out.and(namedBy(reading, here, rest, read));
                if (out == Named.UNSEEN) {
                    return out;
                }
            }
        }
        return out;
    }

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
    private static Named namedBy(ClauseRead reading, TermPath here, List<TermPath.Step> rest,
                                 InputReading read) {
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
        if (at.size() > fields || reading.kind() == ClauseRead.Kind.ITS_VALUES) {
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
        return one.path().isAtOrUnder(other.path()) || other.path().isAtOrUnder(one.path());
    }
}
