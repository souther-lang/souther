package souther.compiler.partition;

import souther.compiler.check.ClauseMeaning;
import souther.compiler.check.ClauseRead;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.PublishedRules;
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
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.values.AdmissibleSet;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

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
 * it sits in reading a place at, under or around it, other than for how many a container around it
 * holds, which is where a rule over two of its positions is written; nothing a way took in
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
        if (at == null || TiedByTheDeclarations.of(read).answered().computeIfAbsent(
                value.position(), path -> mayBeTiedByTheDeclarations(path, read))) {
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
     * What {@link #mayBeTiedByTheDeclarations} answered of each path of one reading, and the rules
     * of each name it read, kept with the reading: every relation over the input asks it of the
     * places it relates, many relations relate one place, and many places sit in one value.
     */
    private record TiedByTheDeclarations(Map<TermPath, Boolean> answered,
                                         Map<TypeSymbol.AtModule, PublishedRules> rules) {

        static TiedByTheDeclarations of(InputReading read) {
            return read.derived(TiedByTheDeclarations.class,
                    _ -> new TiedByTheDeclarations(new ConcurrentHashMap<>(),
                            new ConcurrentHashMap<>()));
        }
    }

    /**
     * Whether a rule of some value {@code path} sits in may hold it back: some value around it —
     * the parameter itself, and every value between — wears a name, or is a declaration, with a
     * rule that reads a place at, under or around what stands at {@code path}.
     *
     * <p>A rule on the position's own type is about it alone and ties it to nothing; one on a
     * value around it is where a rule over two of its positions is written. A rule there that reads
     * only places beside the path leaves every value of the path standing beside some value of the
     * rest — what it holds back is which of the rest stand together — and one reading a container
     * around the path for nothing but how many it holds leaves its elements every value, wherever
     * it may hold one. Both rest on some value of the rest being there, so a value around it the
     * rules leave none of may. And a value around it the reading holds no position for is one
     * nothing can be said of, and may.
     *
     * <p>A name the value wears and the declaration it is are asked alike: the rules of each call
     * a place by the fields read down from the value, a newtype's own {@code value} being the value
     * itself ({@link ClauseRead}).
     */
    private static boolean mayBeTiedByTheDeclarations(TermPath path, InputReading read) {
        List<TermPath.Step> steps = path.steps();
        for (int length = 0; length < steps.size(); length++) {
            TermPath here = new TermPath(path.head(), steps.subList(0, length));
            Position around = read.domain().at(here.position());
            // Where the rules leave no value of it, nothing stands beside the rest of it either.
            if (around == null || around.nothingExists()) {
                return true;
            }
            List<TypeSymbol> worn = new ArrayList<>(around.view().wrappers());
            switch (around.view().shape()) {
                case Shape.Product product -> worn.add(product.name());
                case Shape.Sum sum -> worn.add(sum.name());
                default -> { }
            }
            List<TermPath.Step> rest = steps.subList(length, steps.size());
            for (TypeSymbol each : worn) {
                if (mayHoldBack(each, here, rest, read)) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Whether a rule of {@code worn} may hold back what stands at {@code rest} below {@code here}:
     * one reads a place there, or one was not reached or has no form to say what it reads.
     */
    private static boolean mayHoldBack(TypeSymbol worn, TermPath here, List<TermPath.Step> rest,
                                       InputReading read) {
        if (!(worn instanceof TypeSymbol.AtModule named)) {
            return false;
        }
        PublishedRules rules = TiedByTheDeclarations.of(read).rules().computeIfAbsent(named,
                name -> PublishedRules.governing(name, read.rules().published()));
        if (!rules.everyRuleReached()) {
            return true;
        }
        for (ClauseMeaning each : rules.reached()) {
            if (!(each instanceof ClauseMeaning.Stated stated)) {
                return true;
            }
            for (ClauseRead reading : stated.reads()) {
                if (holdsBack(reading, here, rest, read)) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Whether a clause reading {@code reading} may hold back what stands at {@code rest} below
     * {@code here}.
     *
     * <p>A rule names a place by fields alone ({@code RuleKey}), and a path
     * goes on past its fields into an element or a case. So the two are held against each other
     * along the fields the path starts with. They part where a field differs, and then the rule
     * reads beside the path. Where the rule's place goes on below those fields it is under the
     * path, or past a step no chain of fields names, and may hold it back. Where it stops at or
     * above them it reads what the path stands in — everything there, unless what it reads is how
     * many a container holds and the path goes on into the elements.
     */
    private static boolean holdsBack(ClauseRead reading, TermPath here, List<TermPath.Step> rest,
                                     InputReading read) {
        int fields = 0;
        while (fields < rest.size() && rest.get(fields) instanceof TermPath.Step.Field) {
            fields++;
        }
        List<String> at = reading.at().steps();
        for (int i = 0; i < at.size() && i < fields; i++) {
            if (!at.get(i).equals(((TermPath.Step.Field) rest.get(i)).name())) {
                return false;
            }
        }
        if (at.size() > fields || reading.kind() == ClauseRead.Kind.ITS_VALUES) {
            return true;
        }
        // How many a container holds, read at or above where the path stops going by fields. Only
        // where the container is exactly there and the path goes on into it is that apart from
        // what stands at the path.
        if (at.size() != fields || fields == rest.size()) {
            return true;
        }
        List<TermPath.Step> container = new ArrayList<>(here.steps());
        container.addAll(rest.subList(0, fields));
        return !mayHoldOne(new TermPath(here.head(), container), read);
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
