package souther.compiler.partition;

import souther.compiler.check.DeclaredClauses;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.Shape;
import souther.compiler.inputs.FilingCoordinate;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.PositionBounds;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.WhatARelationLeavesUndivided;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Quantity;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.values.AdmissibleSet;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * A relation this stage read over the input, held as what is asked of it: which of its places it
 * is shown to leave undivided ({@link WhatARelationLeavesUndivided}).
 *
 * <p>Each term is asked two things of the reading of the input. Where it may lie is the run the
 * declarations, and the ways where some are asked of, leave it. What it is shown to take is asked
 * apart, and shown only twice over. The value at a position takes every value its type holds where
 * the declarations admit every value there with nothing of them unread and no end placed — the
 * position's own answer, which already holds the rules of its type. And a number taken of such a
 * value takes every number of its run where the operation declares that every number it could
 * answer is one some value answers ({@code EveryAnswerItCanGiveHasASourceValue}): a string of any
 * length is written by repeating a character, and every hour of the day is one some time falls in.
 * Anything else — what an operation answered of the input that declares no such thing, a value no
 * position holds, a position a rule holds to some of its values — takes what it takes, which
 * nothing here works out.
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
 * would be untied — so what is asked is whether anything could tie the term at all. Nothing ties it
 * where nothing names it but ends on itself and which case a value around it is: no rule of a value
 * it sits in, which is where a rule over two of its positions is written; nothing a way took in
 * that turns on another number with it, or on another number of the place it is taken of — a date
 * on the twenty-ninth of February is in a leap year; and nothing a way stated and none of this took
 * in. Where one does, nothing is shown of the term, whether or not the rule ties it.
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
        List<Takes> sources = new ArrayList<>();
        for (Side each : sides) {
            sources.add(switch (each.term()) {
                case null -> null;
                case NumericTerm.ValueOf value -> takes(value, read);
                case NumericTerm.TakenOf taken ->
                        takes(new NumericTerm.ValueOf(taken.position()), read);
                case NumericTerm.CodePointClassCount _ -> null;
            });
        }
        if (ways.isEmpty()) {
            return undividedAlong(sources, read.quantities().region(), List.of(), true);
        }
        List<Reachability.Reaching> branches = new ArrayList<>();
        for (Reachability.Reaching each : ways) {
            if (!branchesOf(each, branches)) {
                return new LinkedHashSet<>(amongThemselves);
            }
        }
        Set<FilingCoordinate> out = null;
        for (Reachability.Reaching each : branches) {
            Set<FilingCoordinate> along = undividedAlong(sources, each.region(),
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
        way.boundedOnTheWay().forEach(taken -> out.add(new OnAWay(taken.demand().positions(),
                taken.demand() instanceof RowDemand.Relational(TakenConstraint.Affine(
                        LinearForm<NumericTerm> form, Rel rel)) && rel != Rel.NE
                        && form.coefs().size() == 1 ? form.coefs().keySet().iterator().next()
                        : null, false)));
        way.requirements().refinements().keySet()
                .forEach(at -> out.add(new OnAWay(Set.of(at), null, true)));
        way.requirements().atANameTheCasesShare()
                .forEach(at -> out.add(new OnAWay(Set.of(at), null, true)));
        return out;
    }

    /**
     * One statement of a way.
     *
     * @param positions the positions it turns on
     * @param runOf     the one number it places an end on, where it is an end on one number and
     *                  nothing else; null where it is anything else
     * @param aCase     whether it is which case a value is, which says what is there and nothing
     *                  of the values that stand there beside another — a case of a value around a
     *                  term says nothing of the term's values, and a case of the term's own value,
     *                  as an enumeration's, is a value taken out of its order, which the region
     *                  holds
     */
    private record OnAWay(Set<TermPath> positions, NumericTerm runOf, boolean aCase) {}

    /**
     * The places shown undivided over the rows in {@code region}, a way stating
     * {@code conditions} there.
     *
     * @param sources what the declarations leave the value each side is, or is taken of, in the
     *                order of the sides
     */
    private Set<FilingCoordinate> undividedAlong(List<Takes> sources, SearchRegion region,
                                                 List<OnAWay> conditions, boolean heldWhole) {
        List<WhatARelationLeavesUndivided.Term<FilingCoordinate>> terms = new ArrayList<>();
        for (int i = 0; i < sides.size(); i++) {
            Side each = sides.get(i);
            NumericDomain.Bounds holds = each.term() != null
                    && region.projectionOf(each.term())
                    instanceof NumericDomain.FormProjection.Within(NumericDomain.Bounds within)
                    ? within : NumericDomain.Bounds.OPEN;
            Way way = each.term() == null || !heldWhole ? Way.TIES
                    : wayOf(each.term(), conditions);
            Takes source = way == Way.TIES ? null : sources.get(i);
            NumericDomain.Bounds realizes = source == null ? null
                    : realized(each.term(), source, region, way);
            Takes takes = way == Way.UNTOUCHED && each.term() instanceof NumericTerm.ValueOf
                    ? source : null;
            terms.add(new WhatARelationLeavesUndivided.Term<>(each.madeOf(), each.weight(), holds,
                    realizes, takes, each.term() instanceof NumericTerm.ValueOf));
        }
        Set<FilingCoordinate> out = new LinkedHashSet<>(amongThemselves);
        // A term only reaches where nothing ties it, which is what it is asked of before it is
        // taken to reach at all; nothing else needs saying of a pair.
        out.addAll(WhatARelationLeavesUndivided.of(terms, constant, relation,
                UndividedByARelation::overlap, (one, other) -> true));
        return out;
    }

    /** What a way does to a term: nothing, an end on it alone, or more than this can read. */
    private enum Way {

        /** Nothing it states turns on any place the term is read off. */
        UNTOUCHED,

        /** What it states of those places is ends on the term itself, or which case a value
         *  around it is, and nothing else: that narrows where it runs and ties it to nothing. */
        NARROWED,

        /** Something it states of them is anything else: about another number with it, about a
         *  number of the same place other than the term, a value taken out. */
        TIES
    }

    private static Way wayOf(NumericTerm.FromOnePosition term, List<OnAWay> conditions) {
        Way out = Way.UNTOUCHED;
        for (OnAWay each : conditions) {
            // Which case a value around the term is says what stands there and nothing of the
            // values the term takes; which case the term's own value is takes values out of its
            // order, which narrows it.
            if (!touches(term, each.positions())
                    || (each.aCase() && onlyAround(term, each.positions()))) {
                continue;
            }
            if (!each.aCase() && !term.equals(each.runOf())) {
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
     * way places ends on it, or it is a number taken of such a value, what it takes is the run the
     * region shows it fills ({@link SearchRegion#wholeRunOf}).
     *
     * @param source what the declarations leave the value {@code term} is, or is taken of
     */
    private static NumericDomain.Bounds realized(NumericTerm.FromOnePosition term, Takes source,
                                                 SearchRegion region, Way way) {
        if (!source.every()) {
            return null;
        }
        return switch (term) {
            case NumericTerm.ValueOf value -> way == Way.UNTOUCHED ? NumericDomain.Bounds.OPEN
                    : region.wholeRunOf(value);
            case NumericTerm.TakenOf taken -> DefaultBoundOperationFacts.get()
                    .everyAnswerItCanGiveHasASourceValue(taken.operation())
                    ? region.wholeRunOf(taken) : null;
            case NumericTerm.CodePointClassCount _ -> null;
        };
    }

    /**
     * What the declarations leave the value at a position, compared as one value with another's.
     *
     * @param every whether that is every value its type holds: the declarations admit every value
     *              there, nothing of them went unread, and no rule places an end on it
     */
    private record Takes(Type type, AdmissibleSet admitted, NumericDomain.Bounds ends,
                         boolean every) {}

    /** What the declarations leave {@code value}, or null where it is at no position read or a
     *  rule of a value it sits in may tie it to another. */
    private static Takes takes(NumericTerm.ValueOf value, InputReading read) {
        Position at = read.domain().at(value.position().position());
        if (at == null || mayBeTiedByTheDeclarations(value.position(), read)) {
            return null;
        }
        PositionBounds bounds = at.boundsFor(value);
        NumericDomain.Bounds ends = bounds == null ? null : bounds.admissible();
        boolean every = at.admitted().approximation().isAny()
                && at.admitted().completeness() instanceof AdmissibleSet.Completeness.Complete
                && ends == null;
        return new Takes(at.type(), at.admitted(), ends, every);
    }

    /**
     * Whether a rule of some value {@code path} sits in may name it beside another position: some
     * value around it — the parameter itself, and every value between — wears a name, or is a
     * declaration, that writes a rule.
     *
     * <p>A rule on the position's own type is about it alone and ties it to nothing; one on a
     * value around it is where a rule over two of its positions is written. A value around it the
     * reading holds no position for is one nothing can be said of, and may.
     */
    private static boolean mayBeTiedByTheDeclarations(TermPath path, InputReading read) {
        for (int length = 0; length < path.steps().size(); length++) {
            Position around = read.domain().at(
                    new TermPath(path.head(), path.steps().subList(0, length)).position());
            if (around == null) {
                return true;
            }
            List<TypeSymbol> worn = new ArrayList<>(around.view().wrappers());
            switch (around.view().shape()) {
                case Shape.Product product -> worn.add(product.name());
                case Shape.Sum sum -> worn.add(sum.name());
                default -> { }
            }
            for (DeclaredClauses.OnAName each : DeclaredClauses.of(worn, read.rules())) {
                if (!each.conjuncts().isEmpty()) {
                    return true;
                }
            }
        }
        return false;
    }

    private static boolean overlap(FilingCoordinate one, FilingCoordinate other) {
        return one.path().isAtOrUnder(other.path()) || other.path().isAtOrUnder(one.path());
    }
}
