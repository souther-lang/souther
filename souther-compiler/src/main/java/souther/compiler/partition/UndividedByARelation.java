package souther.compiler.partition;

import souther.compiler.abort.GetsPast;
import souther.compiler.check.AnOperationApplied;
import souther.compiler.check.Carrier;
import souther.compiler.check.ClauseAffineMeaning;
import souther.compiler.check.ClauseMeaning;
import souther.compiler.check.ClauseRead;
import souther.compiler.check.ContainerSizesUnderAWitness;
import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.ElementsApart;
import souther.compiler.check.Extreme;
import souther.compiler.check.FieldDomains;
import souther.compiler.check.NumericMeasures;
import souther.compiler.check.PartId;
import souther.compiler.check.ProjectionEvidence;
import souther.compiler.check.PublishedRules;
import souther.compiler.check.RuleKey;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleRef;
import souther.compiler.check.Shape;
import souther.compiler.check.SumCases;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.check.TypeView;
import souther.compiler.core.Core;
import souther.compiler.inputs.Admits;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.DecimalOperation;
import souther.compiler.inputs.ElementProjection;
import souther.compiler.inputs.ElementValue;
import souther.compiler.inputs.EveryRunStops;
import souther.compiler.inputs.FilingCoordinate;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NameReach;
import souther.compiler.inputs.ReadMeaning;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.PathResolution;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.PositionBounds;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.WhatARelationLeavesUndivided;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.PositionsAStatementReads;
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
import souther.compiler.numeric.ValueTransformation;
import souther.compiler.numeric.WholeNumberRuns;
import souther.compiler.observe.Figure;
import souther.compiler.regex.CodeMap;
import souther.compiler.regex.Language;
import souther.compiler.regex.PatternPlan;
import souther.compiler.regex.StringsHeldAsWritten;
import souther.compiler.regex.StringsInsideStrings;
import souther.compiler.regex.StringsOfAPiece;
import souther.compiler.semantics.Accumulation;
import souther.compiler.semantics.CaseMapping;
import souther.compiler.semantics.CodePointClass;
import souther.compiler.semantics.StringContainment;
import souther.compiler.semantics.TakenArguments;
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;
import souther.compiler.values.AdmissibleSet;
import souther.compiler.values.StoppedReading;
import souther.compiler.values.TextExtents;
import souther.compiler.values.UnreadReason;
import souther.compiler.values.ValueSet;

import net.unit8.notation199x.pattern.CodePoints;
import net.unit8.notation199x.pattern.Meter;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collection;
import java.util.Comparator;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.BiPredicate;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

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
 * @param remainder       where the first side is what a division by a written number leaves of a
 *                        form of the input's numbers, the form and the divisor; null otherwise
 * @param working         what the comparison this relation was read from works out, which a
 *                        row has to get past to be a row of it
 */
record UndividedByARelation(List<Side> sides, ExactRatio constant, Rel relation,
                            List<FilingCoordinate> amongThemselves, Kind kind,
                            RemainderSide remainder, Working working) {

    /** A relation that shows no place undivided: one nothing here takes apart. */
    static final UndividedByARelation SHOWING_NOTHING =
            new UndividedByARelation(List.of(), ExactRatio.ZERO, Rel.EQ, List.of(), Kind.AFFINE,
                    null);

    /**
     * An operation of whole numbers a comparison works out: the numbers it is over, weighed, and a
     * constant come to a number from {@code least} to {@code greatest} in every row that is
     * computed. What it is over is the comparison's own reading of it, and not the form the
     * comparison is cut as: {@code a + b - 100 >= 0} works out {@code a + b} and then the
     * difference, and {@code a + b >= 100} the sum alone.
     *
     * @param after the operations, by where they are among those the comparison works out, whose
     *              value this one is worked out of, and theirs: each is worked out before it on
     *              every run. Two operations neither of which is worked out of the other may come
     *              in either order, and an operation worked out of one through a name is not
     *              among these, which says less of the order and nothing false
     */
    record IntOperation(LinearForm<NumericTerm> form, BigInteger least, BigInteger greatest,
                        List<Integer> after) {

        IntOperation {
            after = List.copyOf(new TreeSet<>(after));
        }
    }

    /**
     * The operations of whole numbers and of decimals a comparison works out, and how much of what
     * can stop a run in working it out they are.
     *
     * @param told whether the reading of the comparison told of every operation that can stop a
     *             run, only some, or was not made
     * @param onEveryRun whether every run that gets to the comparison works the operations out,
     *                   and works out nothing that can stop it before them: not where they are
     *                   those of one arm of a choice, or those beside an expression another
     *                   analysis answers for
     * @param decimals the operations of decimals, which a row is asked by working them out
     */
    record Working(List<IntOperation> operations, WhatARelationLeavesUndivided.Told told,
                   boolean onEveryRun, List<DecimalOperation> decimals) {

        Working(List<IntOperation> operations, WhatARelationLeavesUndivided.Told told) {
            this(operations, told, true);
        }

        Working(List<IntOperation> operations, WhatARelationLeavesUndivided.Told told,
                boolean onEveryRun) {
            this(operations, told, onEveryRun, List.of());
        }

        /** No reading of the comparison was made, and the program is taken to add the form up.
         *  That holds for the relations read from the cut of a comparison (a product, a whole and
         *  its part, a difference, a remainder or quotient, and the lines drawn from them), whose
         *  form is the program's own expression and not a sum the walk composed. A relation read
         *  by the affine walk carries what that walk told instead. */
        static final Working NOTHING =
                new Working(List.of(), WhatARelationLeavesUndivided.Told.NOTHING_SAID);

        /** A comparison was read and nothing it told is known to belong to this relation: no row
         *  is shown computed. */
        static final Working UNREAD =
                new Working(List.of(), WhatARelationLeavesUndivided.Told.SOME);

        /**
         * What several readings of one relation tell together: the same where they agree, and
         * otherwise nothing that holds of the rows of every one of them. A row arrives along one
         * reading, and an operation told by another is not one it is asked to get past.
         */
        static Working together(List<Working> readings) {
            Working first = readings.getFirst();
            return readings.stream().allMatch(first::equals) ? first : UNREAD;
        }

        Working {
            operations = List.copyOf(operations);
            decimals = List.copyOf(decimals);
            Objects.requireNonNull(told, "what the reading told, or that there was none");
        }

        /**
         * What a row gets past in working this out after {@code earlier}: both their operations,
         * and every one told only where both tell every one. A row of an arm of a choice has
         * worked out what decided the arm before it works out the arm.
         */
        Working after(Working earlier) {
            if (earlier.equals(NOTHING)) {
                return this;
            }
            if (equals(NOTHING)) {
                return earlier;
            }
            List<IntOperation> both = new ArrayList<>(earlier.operations);
            for (IntOperation each : operations) {
                // What an operation is worked out of is told by where it stands among them.
                both.add(new IntOperation(each.form(), each.least(), each.greatest(),
                        each.after().stream().map(at -> at + earlier.operations.size())
                                .toList()));
            }
            List<DecimalOperation> bothDecimals = new ArrayList<>(earlier.decimals);
            for (DecimalOperation each : decimals) {
                bothDecimals.add(each.shifted(earlier.decimals.size()));
            }
            return new Working(both, earlier.exact() && exact()
                    ? WhatARelationLeavesUndivided.Told.EVERY
                    : WhatARelationLeavesUndivided.Told.SOME,
                    earlier.onEveryRun && onEveryRun, bothDecimals);
        }

        /** The same operations, for a relation not every run that gets to the comparison reaches. */
        Working notOnEveryRun() {
            return new Working(operations, told, false, decimals);
        }

        /** Whether every operation that can stop a run is told. */
        boolean exact() {
            return told == WhatARelationLeavesUndivided.Told.EVERY;
        }
    }

    UndividedByARelation(List<Side> sides, ExactRatio constant, Rel relation,
                         List<FilingCoordinate> amongThemselves, Kind kind,
                         RemainderSide remainder) {
        this(sides, constant, relation, amongThemselves, kind, remainder, Working.NOTHING);
    }

    /** The same relation, read from a comparison that works out {@code working}. */
    UndividedByARelation workingOut(Working working) {
        return new UndividedByARelation(sides, constant, relation, amongThemselves, kind,
                remainder, working);
    }

    UndividedByARelation {
        sides = List.copyOf(sides);
        amongThemselves = List.copyOf(amongThemselves);
        Objects.requireNonNull(working, "a relation says what its comparison works out");
        if (kind != Kind.AFFINE && (sides.size() != 2 || constant == null)) {
            throw new IllegalArgumentException("a product or a remainder is of two numbers, held"
                    + " against a number: " + sides);
        }
        if (remainder != null && (kind != Kind.AFFINE || sides.isEmpty()
                || sides.getFirst().number() != null || sides.getFirst().along() != null)) {
            throw new IllegalArgumentException("a remainder of a form is the first side of a form"
                    + " of terms, and is no number of one place: " + sides);
        }
    }

    /** What the sides of a relation are. */
    enum Kind {
        /** Terms of a form, weighed and added. */
        AFFINE,
        /** The two factors of a product. */
        PRODUCT,
        /** The dividend then the divisor of a remainder, held equal or unequal to nought. */
        DIVISIBILITY,
        /** The string looked for then the string looked in, the first standing somewhere in the
         *  second. */
        INSIDE_ANYWHERE,
        /** The string looked for then the string looked in, the first the start of the second. */
        INSIDE_AT_THE_START,
        /** The string looked for then the string looked in, the first the end of the second. */
        INSIDE_AT_THE_END;

        /** Where the first string stands in the second, where this is a string standing inside
         *  another; null otherwise. */
        StringsInsideStrings.Where inside() {
            return switch (this) {
                case INSIDE_ANYWHERE -> StringsInsideStrings.Where.ANYWHERE;
                case INSIDE_AT_THE_START -> StringsInsideStrings.Where.AT_THE_START;
                case INSIDE_AT_THE_END -> StringsInsideStrings.Where.AT_THE_END;
                case AFFINE, PRODUCT, DIVISIBILITY -> null;
            };
        }
    }

    /** What {@code dividend} leaves divided by {@code divisor}, held equal or unequal to nought;
     *  against any other level or order it shows nothing. */
    static UndividedByARelation ofADivisibility(NumericTerm.FromOnePosition dividend,
                                                NumericTerm.FromOnePosition divisor,
                                                Rel relation) {
        return relation == Rel.EQ || relation == Rel.NE
                ? new UndividedByARelation(List.of(ofTheInput(dividend, ExactRatio.ONE),
                        ofTheInput(divisor, ExactRatio.ONE)), ExactRatio.ZERO, relation,
                        List.of(), Kind.DIVISIBILITY, null)
                : SHOWING_NOTHING;
    }

    /** The values at {@code at} held against other values at {@code at}. */
    static UndividedByARelation amongTheValuesAt(TermPath at) {
        return amongTheValuesAt(List.of(at));
    }

    /**
     * The values at each of {@code places} held against other values, only for whether they are
     * the same: no order is asked of them, so no line is drawn on any of them.
     */
    static UndividedByARelation amongTheValuesAt(List<TermPath> places) {
        return new UndividedByARelation(List.of(), ExactRatio.ZERO, Rel.EQ,
                places.stream().map(FilingCoordinate::at).toList(), Kind.AFFINE, null);
    }

    /** What {@code one} and {@code other} come to multiplied, held against {@code level} as
     *  {@code relation}. */
    static UndividedByARelation ofAProduct(NumericTerm.FromOnePosition one,
                                           NumericTerm.FromOnePosition other, ExactRatio level,
                                           Rel relation) {
        return new UndividedByARelation(List.of(ofTheInput(one, ExactRatio.ONE),
                ofTheInput(other, ExactRatio.ONE)), level.negated(), relation, List.of(),
                Kind.PRODUCT, null);
    }

    /**
     * What a relation leaves its places, over the rows some way lets through: the places it is
     * shown to leave undivided, and the terms some runs of whose values it is shown to settle,
     * every other value of each leaving it either way. A place in neither is one nothing is shown
     * of.
     *
     * @param undivided  the places shown undivided
     * @param settled    each term shown to be settled by some of its values, and those values —
     *                   kept whether or not the term is the number at one position, and whether
     *                   or not the lines parting them are the model's. The places of a term none
     *                   of whose lines parts a place — the orders' ends alone draw them, or they
     *                   are lines on a total of a run — are also among the places shown
     *                   undivided, as the model draws no line on them
     * @param rowsArrive whether any row comes along the way this is of; where none does it says
     *                   nothing of any row, and a way put beside it is what the two come to
     * @param stoppedAt  the figures a search for what would have shown more stopped at: a place
     *                   nothing is shown of here may be one a run allowed more shows undivided
     * @param mayStopBefore those of {@code undivided} some way to which a run may stop on before
     *                   the relation, on what nothing here says: what the relation leaves them is
     *                   shown, and that every value there gets to it is not, which a reader
     *                   claiming the place undivided over every value needs as well
     * @param partnered  each string position the relation is shown to part by the strings its
     *                   partner can hold, and those strings: the values there some value of the
     *                   partner equals, and the rest, which no value of it does. In the order of
     *                   the relation's sides
     */
    record WhatItLeaves(Set<FilingCoordinate> undivided,
                        Map<NumericTerm, WhatARelationLeavesUndivided.Leaves.Settled> settled,
                        boolean rowsArrive, Set<Figure> stoppedAt,
                        Set<FilingCoordinate> mayStopBefore,
                        Map<NumericTerm.FromOnePosition, StringsAPartnerCanHold> partnered) {

        WhatItLeaves {
            undivided = Set.copyOf(undivided);
            settled = Map.copyOf(settled);
            stoppedAt = Set.copyOf(stoppedAt);
            mayStopBefore = Set.copyOf(mayStopBefore);
            // In the order the sides were said in: whoever files a reading for each numbers them
            // as it goes, and an order the keys' hashes decide numbers them differently each run.
            partnered = Collections.unmodifiableMap(new LinkedHashMap<>(partnered));
            if (!undivided.containsAll(mayStopBefore)) {
                throw new IllegalArgumentException("a run stopping before the relation is said of"
                        + " a place the relation is shown to leave undivided");
            }
        }

        WhatItLeaves(Set<FilingCoordinate> undivided,
                     Map<NumericTerm, WhatARelationLeavesUndivided.Leaves.Settled> settled,
                     boolean rowsArrive, Set<Figure> stoppedAt,
                     Set<FilingCoordinate> mayStopBefore) {
            this(undivided, settled, rowsArrive, stoppedAt, mayStopBefore, Map.of());
        }

        WhatItLeaves(Set<FilingCoordinate> undivided,
                     Map<NumericTerm, WhatARelationLeavesUndivided.Leaves.Settled> settled) {
            this(undivided, settled, true, Set.of(), Set.of());
        }

        WhatItLeaves(Set<FilingCoordinate> undivided,
                     Map<NumericTerm, WhatARelationLeavesUndivided.Leaves.Settled> settled,
                     boolean rowsArrive, Set<Figure> stoppedAt) {
            this(undivided, settled, rowsArrive, stoppedAt, Set.of());
        }

        /**
         * This, with the strings each position's partner can hold. A position so parted is no
         * longer shown undivided: its strings are what the relation shows of it, over the region
         * the run gets to the relation at.
         */
        WhatItLeaves partnered(
                Map<NumericTerm.FromOnePosition, StringsAPartnerCanHold> strings) {
            Set<FilingCoordinate> parted = new LinkedHashSet<>();
            strings.keySet().forEach(term -> parted.add(FilingCoordinate.of(term)));
            Set<FilingCoordinate> stillUndivided = new LinkedHashSet<>(undivided);
            stillUndivided.removeAll(parted);
            Set<FilingCoordinate> stops = new LinkedHashSet<>(mayStopBefore);
            stops.removeAll(parted);
            return new WhatItLeaves(stillUndivided, settled, rowsArrive, stoppedAt, stops,
                    strings);
        }

        /** What a way that no row comes along shows of {@code places}: every one of them, of the
         *  rows there are none of. */
        static WhatItLeaves ofAWayNoRowComesAlong(Set<FilingCoordinate> places) {
            return new WhatItLeaves(places, Map.of(), false, Set.of());
        }

        /**
         * This, along a way whose run may stop before the relation on {@code places}: those of
         * them shown undivided are still, and are said not to be shown getting there at every
         * value. A place not shown undivided keeps what it was not shown for, which is no claim
         * about every value getting there. What the relation settles stays as it is, since a value
         * settling it settles it wherever a row gets there.
         */
        WhatItLeaves mayStopBefore(Set<FilingCoordinate> places) {
            Set<FilingCoordinate> stops = new LinkedHashSet<>(mayStopBefore);
            places.stream().filter(undivided::contains).forEach(stops::add);
            return new WhatItLeaves(undivided, settled, rowsArrive, stoppedAt, stops, partnered);
        }

        /** What both this and {@code other} show, for rows that may come along either: a place
         *  shown one way along one and another way along the other is shown nothing of. A way no
         *  row comes along adds no row, so it adds nothing to what the other shows. */
        WhatItLeaves alongBoth(WhatItLeaves other) {
            if (!rowsArrive) {
                return other;
            }
            if (!other.rowsArrive) {
                return this;
            }
            Set<FilingCoordinate> both = new LinkedHashSet<>(undivided);
            both.retainAll(other.undivided);
            Map<NumericTerm, WhatARelationLeavesUndivided.Leaves.Settled> alike =
                    new LinkedHashMap<>();
            settled.forEach((term, runs) -> {
                if (runs.equals(other.settled.get(term))) {
                    alike.put(term, runs);
                }
            });
            Set<Figure> stopped = new LinkedHashSet<>(stoppedAt);
            stopped.addAll(other.stoppedAt);
            Set<FilingCoordinate> stops = new LinkedHashSet<>(mayStopBefore);
            stops.addAll(other.mayStopBefore);
            stops.retainAll(both);
            // Strings a partner can hold are the classes of the position, and a position parted
            // one way along one way and another along the other is parted by neither.
            Map<NumericTerm.FromOnePosition, StringsAPartnerCanHold> alikeStrings =
                    new LinkedHashMap<>();
            partnered.forEach((term, strings) -> {
                StringsAPartnerCanHold theirs = other.partnered.get(term);
                if (strings.showsTheStringsOf(theirs)) {
                    alikeStrings.put(term, strings.orAnother(theirs));
                }
            });
            return new WhatItLeaves(both, alike, true, stopped, stops, alikeStrings);
        }
    }

    /**
     * The strings the other side of an equality can hold, which are the only ones of this side that
     * some row can have the equality come out true at, as far as each is shown.
     *
     * <p>Three regions of this side's strings, and none stands for another. A string of
     * {@code canBe} no longer than {@code upTo} is shown to be some value of the partner, so a row
     * has the equality true there. A string outside {@code mayBe} is shown to be none, so the
     * equality is false there whatever the partner holds. Every other string — of {@code mayBe}
     * and not of {@code canBe}, or of {@code canBe} and longer — is shown neither, and no class of
     * this side is drawn over it.
     *
     * @param canBe   the strings shown to be some value of the partner, as far as {@code upTo}
     *                goes; empty where none is
     * @param mayBe   the strings outside which no value of the partner is, which hold
     *                {@code canBe}
     * @param upTo    the most code points a string of {@code canBe} is shown to be a value of the
     *                partner at, or null where every one of them is
     * @param reached the lengths at which a run is shown to get to the equality with a string of
     *                this side, or null where it is at every length; a string of any other length
     *                is shown neither way, whichever side of the equality it would be on
     * @param partnerHeldTo the lengths at which a run is shown to get to the equality with a
     *                string of the partner, or null where it is at every length: the partner is
     *                the other side's only at these, so a string of this side is shown to be none
     *                of its values at any other
     * @param partner what the model calls the partner
     * @param imagesNotShown the operations of the library whose image over the strings of a side is
     *                shown only where it is exact, which are why strings of {@code mayBe} and not
     *                of {@code canBe} are open at any length
     */
    record StringsAPartnerCanHold(ValueSet canBe, ValueSet mayBe, Long upTo,
                                  StringsPastTheWay reached,
                                  StringsPastTheWay partnerHeldTo, String partner,
                                  List<String> imagesNotShown) {

        StringsAPartnerCanHold {
            if (canBe == null || mayBe == null || partner == null || imagesNotShown == null) {
                throw new IllegalArgumentException("strings a partner can hold are some strings");
            }
            imagesNotShown = List.copyOf(imagesNotShown);
        }

        /**
         * Strings shown at every length a run gets to the equality at, and open for no
         * operation's image: a value that has been given no reach yet. Named so that a value
         * built again from one that has one does not read as a plain construction; that is
         * {@link #showing}, and the constructor above that names every component.
         */
        static StringsAPartnerCanHold unreached(ValueSet canBe, ValueSet mayBe, Long upTo,
                                                String partner) {
            return new StringsAPartnerCanHold(canBe, mayBe, upTo, null, null, partner, List.of());
        }

        /** Strings shown to be the partner's values exactly where {@code canBe} holds them, and
         *  given no reach yet. */
        static StringsAPartnerCanHold unreached(ValueSet canBe, String partner) {
            return unreached(canBe, canBe, null, partner);
        }

        /** The same strings, with the operations whose image is not shown beyond them. */
        StringsAPartnerCanHold withTheImagesNotShownOf(List<String> operations) {
            List<String> all = new ArrayList<>(imagesNotShown);
            all.addAll(operations);
            return new StringsAPartnerCanHold(canBe, mayBe, upTo, reached, partnerHeldTo, partner,
                    all.stream().distinct().sorted().toList());
        }

        /**
         * The same partner and the same reach, with other strings shown. The one way to change
         * what is shown of a value that has been given its reach: a value built again from its
         * strings alone is shown at every length, and the reach it was given is gone.
         */
        StringsAPartnerCanHold showing(ValueSet canBe, ValueSet mayBe, Long upTo) {
            return new StringsAPartnerCanHold(canBe, mayBe, upTo, reached, partnerHeldTo, partner,
                    imagesNotShown);
        }

        /** These, shown only at the lengths {@code lengths}, which every other length is left
         *  open at. */
        StringsAPartnerCanHold reachedAt(StringsPastTheWay lengths) {
            return new StringsAPartnerCanHold(canBe, mayBe, upTo, lengths, partnerHeldTo, partner,
                    imagesNotShown);
        }

        /** These, where the partner is the other side's only at the lengths {@code lengths}. */
        StringsAPartnerCanHold partnerHeldTo(StringsPastTheWay lengths) {
            return new StringsAPartnerCanHold(canBe, mayBe, upTo, reached, lengths, partner,
                    imagesNotShown);
        }

        /** Whether every string is shown on one side or the other, so that none is open. */
        boolean leavesNoneOpen() {
            return upTo == null && reached == null && partnerHeldTo == null
                    && canBe.equals(mayBe);
        }

        /** Whether the same strings are shown on each side, whatever the partner is called. */
        boolean showsTheStringsOf(StringsAPartnerCanHold other) {
            return other != null && canBe.equals(other.canBe) && mayBe.equals(other.mayBe)
                    && Objects.equals(upTo, other.upTo)
                    && Objects.equals(reached, other.reached)
                    && Objects.equals(partnerHeldTo, other.partnerHeldTo);
        }

        /** The same strings, said of this partner or the other: a value is shown to be one of two
         *  partners' where it is shown to be either's. */
        StringsAPartnerCanHold orAnother(StringsAPartnerCanHold other) {
            StringsAPartnerCanHold named = partner.equals(other.partner) ? this
                    : new StringsAPartnerCanHold(canBe, mayBe, upTo, reached, partnerHeldTo,
                            partner + " or " + other.partner, imagesNotShown);
            return named.withTheImagesNotShownOf(other.imagesNotShown);
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
     * @param number the number of the input it is, or null where it is anything made of one or no
     *               position's
     * @param along  where it is read off a container's elements one by one, what that is — the end
     *               a walk kept so far of what it carried, where the element it hands its step
     *               stands, or how many of the elements meet a statement — which says where it
     *               lies; null otherwise
     * @param piece  the piece of a string of the input at some indexes that it is, which is made of
     *               that string's position and is at none of its own; null otherwise
     * @param text   the string made of the string at a position by case conversions, which is
     *               made of that position and is at none of its own; null otherwise
     */
    record Side(List<FilingCoordinate> madeOf, ExactRatio weight,
                NumericTerm number, Quantity.ReadAlongAContainer along,
                PiecesOfAString piece, ConvertedText text) {

        Side {
            madeOf = List.copyOf(madeOf);
            if (along != null && (number != null || !madeOf.isEmpty())) {
                throw new IllegalArgumentException("what is read along a container is at no"
                        + " position: " + along);
            }
            if (piece != null && number != null) {
                throw new IllegalArgumentException("a piece of a string is no number of one"
                        + " position: " + piece);
            }
            if (text != null && (number != null || piece != null)) {
                throw new IllegalArgumentException("a converted string is no number of one"
                        + " position and no piece: " + text);
            }
        }

        /** A side that is neither a text nor a piece of one. */
        Side(List<FilingCoordinate> madeOf, ExactRatio weight, NumericTerm number,
             Quantity.ReadAlongAContainer along, PiecesOfAString piece) {
            this(madeOf, weight, number, along, piece, null);
        }

        /** The end a walk keeping one carried into its step, where this is that; null
         *  otherwise. */
        Quantity.KeptSoFar kept() {
            return along instanceof Quantity.KeptSoFar kept ? kept : null;
        }

        /** How many elements of a container meet a statement, where this is that; null
         *  otherwise. */
        Quantity.HowManyMeet counted() {
            return along instanceof Quantity.HowManyMeet counted ? counted : null;
        }

        /** Where the element a walk hands its step stands, where this is that; null otherwise. */
        Quantity.PositionInTheWalk position() {
            return along instanceof Quantity.PositionInTheWalk position ? position : null;
        }

        /**
         * The number as one position's, or null where it is no number of one position.
         *
         * <p>Apart from {@link #number}, which says which number of the input the side is. A
         * number taken over a run has no position and nothing a way states of a position is
         * stated of it, so what it is shown to take is nothing; where its values lie is still what
         * the region reads of it, and that is asked of the number.
         */
        NumericTerm.FromOnePosition atOnePosition() {
            return number == null ? null : number.atOnePosition();
        }

        /** The number of the input what this side may be is read off — the order it stands on,
         *  what the declarations and a way say of it: its own, or the element's a walk kept an end
         *  of. */
        NumericTerm.FromOnePosition readOff() {
            return atOnePosition() != null ? atOnePosition()
                    : kept() != null ? kept().ofEach() : null;
        }

        /**
         * The number a statement of the way can be about, as the statement names it: the number
         * of one position, or the end of a key's numbers. The term the sides are weighed in is the
         * term a statement is weighed in, so it is looked up by the number itself and not by the
         * position it is read off, which an end has none of. Null for any other number.
         */
        NumericTerm statedTerm() {
            return atOnePosition() != null || !placesOfItsEnd().isEmpty() ? number : null;
        }

        /**
         * The places the end of a key's numbers is taken of, where this is such an end: a
         * container of one element has that element's number for its end, at whichever place its
         * case puts it, so what the declarations leave the places is what they leave the end.
         * Empty where it is no end, or the end of anything but places.
         */
        List<NumericTerm.ValueOf> placesOfItsEnd() {
            return number == null ? List.of()
                    : placesOfOneElement(number).stream().map(PlaceOfAnEnd::value).toList();
        }

        /**
         * The numbers the places of this end are measured by, for what the declarations leave them
         * and the order they stand on: the value at each place, or the steps its values fall in
         * where the end is of those. Empty where this is no end, and null where steps are not of
         * the value at a place.
         */
        List<NumericTerm.FromOnePosition> measuresOfItsEnd(InputReading read) {
            List<NumericTerm.FromOnePosition> out = new ArrayList<>();
            for (PlaceOfAnEnd each : number == null ? List.<PlaceOfAnEnd>of()
                    : placesOfOneElement(number)) {
                NumericTerm.FromOnePosition measured = each.measure(read);
                if (measured == null) {
                    return null;
                }
                out.add(measured);
            }
            return out;
        }

    }

    /**
     * One place an end is taken of, and the operation whose steps of the values there the end is
     * of — none where it is the end of the values themselves.
     *
     * <p>The steps are a term made against the type of what stands at the place, so a place and an
     * operation of another type never make one: {@code made} is the term where the end already
     * carries it, and otherwise it is made here, where the reading of the input is at hand.
     */
    private record PlaceOfAnEnd(TermPath place, ValueName.Stdlib steps,
                                NumericTerm.WholeUnitsOf made) {

        NumericTerm.ValueOf value() {
            return new NumericTerm.ValueOf(place);
        }

        /** The number the end is measured by at this place; null where the steps are not of the
         *  value there. */
        NumericTerm.FromOnePosition measure(InputReading read) {
            if (steps == null) {
                return value();
            }
            return made != null ? made : NumericTerm.WholeUnitsOf.of(steps, place,
                    read.domain().typeAt(place, read.rules()), read.rules().inners(),
                    read.rules().declarations());
        }
    }

    /**
     * What the declarations leave the value {@code each} is, or is taken of — and where it is the
     * end of a key's numbers, what they leave every place it is taken of, or null where they leave
     * them differently. No one place stands for the others.
     */
    private static Source sourceOfSide(Side each, InputReading read) {
        List<NumericTerm.FromOnePosition> places = each.measuresOfItsEnd(read);
        if (places == null) {
            return null;
        }
        if (places.isEmpty()) {
            return sourceOf(each.atOnePosition(), read);
        }
        Source first = sourceOf(places.getFirst(), read);
        for (NumericTerm.FromOnePosition place : places) {
            if (!Objects.equals(first, sourceOf(place, read))) {
                return null;
            }
        }
        return first;
    }

    /**
     * The order the numbers of {@code each} are counted on — and where it is the end of a key's
     * numbers, the order every place it is taken of stands on, or null where they stand on
     * different ones.
     */
    private static Carrier carrierOfSide(Side each, InputReading read) {
        if (each.text() != null) {
            TermOrders orders = read.quantities().ordersOf(each.text().place());
            return orders == null ? null : orders.answered();
        }
        List<NumericTerm.FromOnePosition> places = each.measuresOfItsEnd(read);
        if (places == null) {
            return null;
        }
        if (places.isEmpty()) {
            NumericTerm.FromOnePosition countedAs = each.readOff() != null ? each.readOff()
                    : summedAs(each.number());
            TermOrders orders = countedAs == null ? null : read.quantities().ordersOf(countedAs);
            return orders == null ? null : orders.answered();
        }
        Carrier first = null;
        for (NumericTerm.FromOnePosition place : places) {
            TermOrders orders = read.quantities().ordersOf(place);
            if (orders == null || (first != null && !first.equals(orders.answered()))) {
                return null;
            }
            first = orders.answered();
        }
        return first;
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
                        each.getValue(), null, null, null);
                case Quantity.APieceOf piece -> new Side(
                        piece.positionsItIsMadeOf().stream().map(FilingCoordinate::of).toList(),
                        each.getValue(), null, null, PiecesOfAString.of(piece));
                case Quantity.ThePieceAt piece -> new Side(
                        piece.positionsItIsMadeOf().stream().map(FilingCoordinate::of).toList(),
                        each.getValue(), null, null, PiecesOfAString.of(piece));
                case Quantity.IsAmongThePieces among -> new Side(
                        among.positionsItIsMadeOf().stream().map(FilingCoordinate::of).toList(),
                        each.getValue(), null, null, null);
                case Quantity.OfABinding bound -> new Side(List.of(), each.getValue(), null,
                        bound.handed().orElse(null), null);
                case Quantity.HowManyMeet counted -> new Side(List.of(), each.getValue(), null,
                        counted, null);
                default -> new Side(List.of(), each.getValue(), null, null, null);
            });
        }
        return new UndividedByARelation(sides, form.constant(), relation, List.of(), Kind.AFFINE,
                null);
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
        return new UndividedByARelation(sides, constant, relation, List.of(), Kind.AFFINE, null);
    }

    /** The values at two positions held as one value, or not. */
    static UndividedByARelation ofTwoPositions(TermPath one, TermPath other) {
        return new UndividedByARelation(List.of(
                new Side(List.of(FilingCoordinate.at(one)), ExactRatio.ONE,
                        new NumericTerm.ValueOf(one), null, null),
                new Side(List.of(FilingCoordinate.at(other)), ExactRatio.ONE.negated(),
                        new NumericTerm.ValueOf(other), null, null)), ExactRatio.ZERO, Rel.EQ,
                List.of(), Kind.AFFINE, null);
    }

    /**
     * The string {@code inner} standing where {@code where} says in the string {@code outer}, each
     * a string of the input or one made of it by case conversions; or nothing shown, where either
     * is anything else, or they are made of one position.
     */
    static UndividedByARelation ofAStringInside(Quantity inner, Quantity outer,
                                                StringContainment where) {
        ConvertedText looked = ConvertedText.of(inner);
        ConvertedText in = ConvertedText.of(outer);
        if (looked == null || in == null || overlap(FilingCoordinate.of(looked.place()),
                FilingCoordinate.of(in.place()))) {
            return SHOWING_NOTHING;
        }
        Kind kind = switch (where) {
            case ANYWHERE -> Kind.INSIDE_ANYWHERE;
            case AT_THE_START -> Kind.INSIDE_AT_THE_START;
            case AT_THE_END -> Kind.INSIDE_AT_THE_END;
        };
        return new UndividedByARelation(List.of(
                new Side(List.of(FilingCoordinate.of(looked.place())), ExactRatio.ONE, null, null,
                        null, looked),
                new Side(List.of(FilingCoordinate.of(in.place())), ExactRatio.ONE, null, null,
                        null, in)), ExactRatio.ZERO, Rel.EQ, List.of(), kind, null);
    }

    /**
     * What a division by a written number leaves of a form of the input's numbers, with a form of
     * other numbers added to it, held against {@code level} as {@code relation}.
     *
     * <p>The remainder is the first side, weighed by one and made of the places of the form, and
     * the numbers added follow it. It is a side that is no number of one place, as what an
     * operation answers is not, and it runs from nought to one below the divisor
     * ({@link RemainderSide}).
     */
    static UndividedByARelation ofARemainderOfAForm(LinearForm<NumericTerm> dividend,
                                                    BigInteger shift, BigInteger divisor,
                                                    LinearForm<NumericTerm> added,
                                                    ExactRatio level, Rel relation) {
        // Which numbers are apart is read off the places each side is made of, so a number read
        // off more than the place it is filed under — the times a value occurs in a run is read
        // off the run and the value — has places no side names. Nothing is shown of it.
        if (Stream.concat(dividend.coefs().keySet().stream(), added.coefs().keySet().stream())
                .anyMatch(term -> !term.placesReadOff().equals(List.of(term.subjectPath())))) {
            return SHOWING_NOTHING;
        }
        List<Side> sides = new ArrayList<>();
        sides.add(new Side(dividend.coefs().keySet().stream().map(FilingCoordinate::of).toList(),
                ExactRatio.ONE, null, null, null));
        added.coefs().forEach((term, weight) -> sides.add(ofTheInput(term, weight)));
        return new UndividedByARelation(sides, level.negated(), relation, List.of(), Kind.AFFINE,
                new RemainderSide(dividend, shift, divisor));
    }

    /**
     * The first side of a relation, where it is what a division by a written number leaves of a
     * form of the input's numbers.
     *
     * @param dividend the form the division is of, with no constant: its numbers and what each is
     *                 weighed by
     * @param shift    the whole number the form is moved by before it is divided
     * @param divisor  the number it is divided by, above nought
     */
    record RemainderSide(LinearForm<NumericTerm> dividend, BigInteger shift, BigInteger divisor) {

        RemainderSide {
            if (dividend == null || shift == null || divisor == null || divisor.signum() <= 0
                    || dividend.coefs().isEmpty()) {
                throw new IllegalArgumentException("a remainder is of a form of numbers, by a"
                        + " divisor above nought: " + dividend + " + " + shift + " by " + divisor);
            }
        }

        /** Whether {@code on} is a condition on this remainder: of the same form, moved by the
         *  same number and divided by the same divisor. */
        boolean isAskedBy(RowDemand.OnARemainder on) {
            Quantity.RemainderOfADividend asked = on.remainder();
            return asked.divisor().equals(divisor)
                    && asked.dividend().coefs().equals(dividend.coefs())
                    && asked.dividend().constant().equals(ExactRatio.of(shift));
        }
    }

    private static Side ofTheInput(NumericTerm term, ExactRatio weight) {
        return new Side(List.of(FilingCoordinate.of(term)), weight, term, null, null);
    }

    /**
     * The operations the comparison works out, each weighing the numbers it is over by name. An
     * operation over a number that is no side of this relation, or is two sides, is left out,
     * which cuts less and says nothing false — and is an operation a row is not asked to get past
     * here, so the operations are then not every one, unless no row of the places it is over
     * could stop at it.
     */
    private WhatARelationLeavesUndivided.Operations operationsOverTheSides(InputReading read) {
        if (working.operations().isEmpty() && working.decimals().isEmpty()) {
            return new WhatARelationLeavesUndivided.Operations(List.of(), working.told());
        }
        Map<NumericTerm, Integer> named = new LinkedHashMap<>();
        for (Side each : sides) {
            if (each.number() != null) {
                named.merge(each.number(), 1, Integer::sum);
            }
        }
        List<WhatARelationLeavesUndivided.IntSum> sums = new ArrayList<>();
        boolean leftOut = false;
        for (IntOperation each : working.operations()) {
            boolean overTheSides = each.form().coefs().keySet().stream()
                    .allMatch(atom -> Integer.valueOf(1).equals(named.get(atom)));
            if (!overTheSides) {
                leftOut |= !stopsNoRow(each, read);
                continue;
            }
            sums.add(new WhatARelationLeavesUndivided.IntSum(
                    new LinkedHashMap<Object, ExactRatio>(each.form().coefs()),
                    each.form().constant(), each.least(), each.greatest()));
        }
        // A decimal operation reads the results of those worked out before it by where they stand
        // among them, so none is left out alone: one over a number that is no side of this
        // relation, or is two sides, leaves them all out.
        boolean decimalsOverTheSides = working.decimals().stream()
                .allMatch(each -> overTheSides(each, named));
        List<DecimalOperation> decimals = decimalsOverTheSides ? working.decimals() : List.of();
        leftOut |= !decimalsOverTheSides;
        // An operation left out is one a row is not asked to get past here: not every one told.
        return new WhatARelationLeavesUndivided.Operations(sums, decimals,
                leftOut && working.exact() ? WhatARelationLeavesUndivided.Told.SOME
                        : working.told());
    }

    /** Whether every number {@code operation} reads from a row is a side of this relation, once. */
    private static boolean overTheSides(DecimalOperation operation,
                                        Map<NumericTerm, Integer> named) {
        return operation.operands().stream().allMatch(operand -> !(operand
                instanceof DecimalOperation.Formed formed)
                || formed.coefs().keySet().stream()
                        .allMatch(atom -> Integer.valueOf(1).equals(named.get(atom))));
    }

    /**
     * Whether no row stops at {@code operation}: the number it comes to lies from {@code least} to
     * {@code greatest} whatever its places hold, each between the ends of the order its values are
     * counted on. False where a place has no end to give.
     */
    private static boolean stopsNoRow(IntOperation operation, InputReading read) {
        FormRange range = FormRange.of(operation.form(), read);
        return range != null && range.liesWithin(operation.least(), operation.greatest());
    }

    /** The places shown undivided over what the declarations leave. */
    Set<FilingCoordinate> undivided(InputReading read, CountWitnesses.Lookup witnesses) {
        return undividedWhereRowsArrive(read, List.of(), witnesses);
    }

    /** The places shown undivided over the rows that arrive along {@code ways}
     *  ({@link #leftWhereRowsArrive}). */
    Set<FilingCoordinate> undividedWhereRowsArrive(InputReading read,
                                                   List<Reachability.Reaching> ways,
                                                   CountWitnesses.Lookup witnesses) {
        return leftWhereRowsArrive(read, ways, witnesses).undivided();
    }

    /** What this leaves its places over what the declarations leave. */
    WhatItLeaves left(InputReading read, CountWitnesses.Lookup witnesses) {
        return leftWhereRowsArrive(read, List.of(), witnesses);
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
     * each is a way here, and a way some of whose branches were not split out is read again with
     * its choices as they come to for this, or shows nothing ({@link #branchesOf}).
     *
     * @param witnesses where a count of elements meeting a statement is shown to take every value
     *                  beside how many the container holds ({@link #countWithinItsContainer})
     */
    WhatItLeaves leftWhereRowsArrive(InputReading read, List<Reachability.Reaching> ways,
                                     CountWitnesses.Lookup witnesses) {
        WhatItLeaves nothingShown = new WhatItLeaves(new LinkedHashSet<>(amongThemselves),
                Map.of());
        // What the declarations leave each side, which no way changes: asked once for all of them.
        // A side a walk kept an end of is asked of the element's number, which is what the end
        // lies between.
        List<Source> sources = new ArrayList<>();
        for (Side each : sides) {
            sources.add(each.kept() == null ? sourceOfSide(each, read)
                    : keptSource(each.kept(), read));
        }
        // And the order each side's values are counted on, which says where its type ends.
        List<Carrier> carriers = new ArrayList<>();
        for (Side each : sides) {
            carriers.add(carrierOfSide(each, read));
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
                    null, true, Optional.of(Set.of()), DemandReading.Answered.NOTHING, witnesses);
        }
        List<Reachability.Reaching> branches = new ArrayList<>();
        Set<CompositionBudget> stopped = new LinkedHashSet<>();
        for (Reachability.Reaching each : ways) {
            if (!branchesOf(each, branches, read, stopped)) {
                return new WhatItLeaves(nothingShown.undivided(), Map.of(), true,
                        stopped.stream().map(CompositionBudget::figure)
                                .collect(Collectors.toCollection(LinkedHashSet::new)));
            }
        }
        if (branches.isEmpty()) {
            return WhatItLeaves.ofAWayNoRowComesAlong(places());
        }
        // Ways read alike are read once: a choice the body works out after reading its input splits
        // the way into as many ways as it has arms, and each states the same. What a way is read by
        // is its region, what it states and whether it is held whole, and two ways of one reading
        // narrowed by the same are over one region ({@link Reachability.Reaching#narrowedBy}).
        Map<Along, WhatItLeaves> alike = new HashMap<>();
        List<Carrier> carried = carriers;
        WhatItLeaves out = null;
        for (Reachability.Reaching each : branches) {
            WholeNumberRuns remainders = remaindersLeftAlong(each);
            if (remainders != null && remainders.isNone()) {
                WhatItLeaves none = WhatItLeaves.ofAWayNoRowComesAlong(places());
                out = out == null ? none : out.alongBoth(none);
                continue;
            }
            List<OnAWay> conditions = conditionsOf(each, remainder);
            boolean heldWhole = nothingUnreadBearsOnIt(each);
            Optional<Set<String>> declined = parametersDeclined(each);
            DemandReading.Answered past = new DemandReading.Answered(each.gotPast(), each.tied(),
                    each.unsaid(), each.owed(), each.before());
            WhatItLeaves along = each.narrowedBy().isPresent()
                    ? alike.computeIfAbsent(new Along(each.narrowedBy().get(), conditions,
                            remainders, heldWhole, declined, past), _ -> leftAlong(read, sources,
                                    carried, each.region(), conditions, remainders, heldWhole,
                                    declined, past, witnesses))
                    : leftAlong(read, sources, carried, each.region(), conditions, remainders,
                            heldWhole, declined, past, witnesses);
            out = out == null ? along : out.alongBoth(along);
        }
        return out;
    }

    /**
     * Where every run getting to this relation stops in one of the operations the reading of the
     * comparison told of, said only where every operation that can stop a run was told.
     *
     * <p>A run stops in the first operation it works out that is past its type. So the rows it
     * stops in one are those at which that one is past its type and every operation it may work
     * out before it is within its own: all the others but those worked out of its value, which
     * come after it on every run. The rows are said as the forms of the operations between their
     * ends, over as many numbers as each is over, and a form over one number as that number's
     * run. Rows at which two operations either of which may come first are both past their types
     * stop in one of them, and are said of neither.
     *
     * <p>Said where some region leaves such a row: none of what the ways to the comparison leave
     * holds one, and every row there gets past.
     *
     * @param regions what the ways to the comparison leave, before what the rows that get past
     *                its operations are narrowed to: a region a row got past them in holds none
     *                of the rows a run stops at
     */
    List<EveryRunStops> everyRunStopsIn(InputReading read, List<SearchRegion> regions) {
        if (!working.exact() || !working.onEveryRun() || !working.decimals().isEmpty()) {
            return List.of();
        }
        List<IntOperation> operations = working.operations();
        Set<EveryRunStops> out = new LinkedHashSet<>();
        for (int at = 0; at < operations.size(); at++) {
            IntOperation it = operations.get(at);
            List<Bounded> before = new ArrayList<>();
            for (int other = 0; other < operations.size(); other++) {
                IntOperation one = operations.get(other);
                if (other != at && !one.after().contains(at)) {
                    before.add(new Bounded(one.form(), one.least(), one.greatest()));
                }
            }
            for (Bounded past : List.of(
                    new Bounded(it.form(), it.greatest().add(BigInteger.ONE), null),
                    new Bounded(it.form(), null, it.least().subtract(BigInteger.ONE)))) {
                List<Bounded> rows = new ArrayList<>(before);
                rows.add(past);
                List<EveryRunStops.Within> where = rowsWhere(rows, read, regions);
                if (where != null) {
                    out.add(new EveryRunStops(written(it.form()), where));
                }
            }
        }
        return List.copyOf(out);
    }

    /** A form over numbers of the input, constant and all, from {@code least} to
     *  {@code greatest}, either of which may be null where nothing bounds it there. */
    private record Bounded(LinearForm<NumericTerm> form, BigInteger least, BigInteger greatest) { }

    /**
     * The rows meeting every one of {@code bounds}, as each form of numbers they hold between two
     * ends: the forms alike but for the constant met into one, a form of one number said as that
     * number's run within its type, and an end that is the type's own left unsaid. Null where no
     * row meets them, or no region leaves one that does.
     */
    private static List<EveryRunStops.Within> rowsWhere(List<Bounded> bounds, InputReading read,
                                                        List<SearchRegion> regions) {
        Map<Map<NumericTerm, ExactRatio>, BigInteger[]> met = new LinkedHashMap<>();
        Set<NumericTerm.FromOnePosition> numbers = new LinkedHashSet<>();
        for (Bounded each : bounds) {
            Map<NumericTerm, ExactRatio> coefs = each.form().coefs();
            BigInteger weight = coefs.size() == 1 ? wholeOf(coefs.values().iterator().next())
                    : BigInteger.ONE;
            BigInteger shift = wholeOf(each.form().constant());
            if (coefs.isEmpty() || weight == null || shift == null
                    || !coefs.keySet().stream().allMatch(term ->
                            term instanceof NumericTerm.FromOnePosition)) {
                return null;
            }
            coefs.keySet().forEach(term -> numbers.add((NumericTerm.FromOnePosition) term));
            BigInteger least = each.least() == null ? null : each.least().subtract(shift);
            BigInteger greatest = each.greatest() == null ? null
                    : each.greatest().subtract(shift);
            Map<NumericTerm, ExactRatio> shape = coefs;
            if (coefs.size() == 1) {
                // One number weighed: its own run, the ends divided by the weight.
                shape = Map.of(coefs.keySet().iterator().next(), ExactRatio.ONE);
                BigInteger low = least == null ? null : weight.signum() > 0
                        ? ceilingOf(least, weight) : floorOf(least, weight);
                BigInteger high = greatest == null ? null : weight.signum() > 0
                        ? floorOf(greatest, weight) : ceilingOf(greatest, weight);
                least = weight.signum() > 0 ? low : high;
                greatest = weight.signum() > 0 ? high : low;
            }
            BigInteger[] ends = met.computeIfAbsent(shape, _ -> new BigInteger[2]);
            if (least != null) {
                ends[0] = ends[0] == null ? least : ends[0].max(least);
            }
            if (greatest != null) {
                ends[1] = ends[1] == null ? greatest : ends[1].min(greatest);
            }
        }
        List<EveryRunStops.Within> out = new ArrayList<>();
        List<Bounded> asked = new ArrayList<>();
        for (Map.Entry<Map<NumericTerm, ExactRatio>, BigInteger[]> each : met.entrySet()) {
            LinearForm<NumericTerm> form = new LinearForm<>(ExactRatio.ZERO, each.getKey());
            BigInteger least = each.getValue()[0];
            BigInteger greatest = each.getValue()[1];
            BigInteger typeLeast = typeEndOf(form, true, read);
            BigInteger typeGreatest = typeEndOf(form, false, read);
            if (form.coefs().size() == 1) {
                least = least == null ? typeLeast : typeLeast == null ? least : least.max(typeLeast);
                greatest = greatest == null ? typeGreatest
                        : typeGreatest == null ? greatest : greatest.min(typeGreatest);
            }
            if (least != null && greatest != null && least.compareTo(greatest) > 0) {
                return null;
            }
            asked.add(new Bounded(form, least, greatest));
            BigInteger shownLeast = least != null && least.equals(typeLeast) ? null : least;
            BigInteger shownGreatest = greatest != null && greatest.equals(typeGreatest) ? null
                    : greatest;
            if (shownLeast != null || shownGreatest != null) {
                out.add(new EveryRunStops.Within(written(form), shownLeast, shownGreatest));
            }
        }
        // And every number of them within its type, which every row is, for the regions: a
        // region need not say where a type stops.
        for (NumericTerm.FromOnePosition number : numbers) {
            LinearForm<NumericTerm> alone = LinearForm.atom(number);
            asked.add(new Bounded(alone, typeEndOf(alone, true, read),
                    typeEndOf(alone, false, read)));
        }
        // In the order of what they are written as, which is what a report is compared by.
        out.sort(Comparator.comparing(EveryRunStops.Within::form));
        return out.isEmpty() || regions.stream().noneMatch(region -> holdsARow(region, asked))
                ? null : out;
    }

    /** Whether {@code region}, narrowed to {@code bounds}, is not shown to hold no row. A bound
     *  it cannot carry narrows nothing, which leaves a row where there may be none. */
    private static boolean holdsARow(SearchRegion region, List<Bounded> bounds) {
        SearchRegion narrowed = region;
        for (Bounded each : bounds) {
            if (each.least() != null) {
                narrowed = narrowedBy(narrowed, each.form(), each.least(), Rel.GE);
            }
            if (each.greatest() != null) {
                narrowed = narrowedBy(narrowed, each.form(), each.greatest(), Rel.LE);
            }
        }
        LinearForm<NumericTerm> any = bounds.getFirst().form();
        return !(narrowed.projectionOf(any)
                instanceof NumericDomain.FormProjection.NothingIsLeft);
    }

    /** {@code region} with {@code form rel end} taken in, or as it was where it cannot be. */
    private static SearchRegion narrowedBy(SearchRegion region, LinearForm<NumericTerm> form,
                                           BigInteger end, Rel rel) {
        LinearForm<NumericTerm> moved = new LinearForm<>(
                form.constant().minus(ExactRatio.of(end)).orNull(), form.coefs());
        return moved.constant() != null
                && region.assuming(moved, rel) instanceof SearchRegion.Assumption.Taken(
                        SearchRegion taken) ? taken : region;
    }

    /** {@code ratio} where it is a whole number, or null. */
    static BigInteger wholeOf(ExactRatio ratio) {
        return ratio.isWhole() && ratio.floor() instanceof ExactAnswer.Held<BigInteger>(
                BigInteger whole) ? whole : null;
    }

    /**
     * The least {@code form} comes to where each number in it is at an end of its type — or the
     * most, where {@code least} is false — or null where a number of it has no such end or is no
     * whole number.
     */
    private static BigInteger typeEndOf(LinearForm<NumericTerm> form, boolean least,
                                        InputReading read) {
        if (!(form.constant().floor() instanceof ExactAnswer.Held<BigInteger>(BigInteger sum))
                || !form.constant().isWhole()) {
            return null;
        }
        for (Map.Entry<NumericTerm, ExactRatio> each : form.coefs().entrySet()) {
            if (!(each.getKey() instanceof NumericTerm.FromOnePosition place)
                    || !each.getValue().isWhole()
                    || !(each.getValue().floor() instanceof ExactAnswer.Held<BigInteger>(
                            BigInteger weight))) {
                return null;
            }
            Carrier carrier = read.quantities().ordersOf(place).answered();
            boolean atItsLeast = least == (weight.signum() > 0);
            BigInteger end = withinWhatItCanBe(
                    atItsLeast ? leastOf(carrier) : greatestOf(carrier), place, atItsLeast);
            if (end == null) {
                return null;
            }
            sum = sum.add(weight.multiply(end));
        }
        return sum;
    }

    /**
     * {@code end}, the end its carrier gives {@code number}, brought in to the end of what the
     * number can be besides ({@link NumericTerm#reachBounds}): a length is never negative and no
     * longer than a string can be, however many an {@code Int} holds.
     */
    private static BigInteger withinWhatItCanBe(BigInteger end, NumericTerm number,
                                                boolean least) {
        NumericDomain.Bounds reach = number.reachBounds();
        BigInteger narrower = wholeEnd(least ? reach.min() : reach.max(), least);
        if (narrower == null) {
            return end;
        }
        return end == null ? narrower : least ? end.max(narrower) : end.min(narrower);
    }

    static BigInteger floorOf(BigInteger numerator, BigInteger denominator) {
        BigInteger[] parts = numerator.divideAndRemainder(denominator);
        return parts[1].signum() != 0 && parts[1].signum() != denominator.signum()
                ? parts[0].subtract(BigInteger.ONE) : parts[0];
    }

    static BigInteger ceilingOf(BigInteger numerator, BigInteger denominator) {
        return floorOf(numerator.negate(), denominator).negate();
    }

    /** {@code form} as an author would write it: each number weighed, in the order of their
     *  names, and the constant last. */
    private static String written(LinearForm<NumericTerm> form) {
        Map<String, ExactRatio> named = new TreeMap<>();
        form.coefs().forEach((term, weight) -> named.put(term.toString(), weight));
        StringBuilder out = new StringBuilder();
        named.forEach((name, weight) -> {
            boolean below = weight.signum() < 0;
            ExactRatio size = below ? weight.negated() : weight;
            out.append(out.isEmpty() ? (below ? "-" : "") : below ? " - " : " + ")
                    .append(size.equals(ExactRatio.ONE) ? "" : size.spelled() + " * ")
                    .append(name);
        });
        if (!form.constant().isZero() || out.isEmpty()) {
            boolean below = form.constant().signum() < 0;
            ExactRatio size = below ? form.constant().negated() : form.constant();
            out.append(out.isEmpty() ? (below ? "-" : "") : below ? " - " : " + ")
                    .append(size.spelled());
        }
        return out.toString();
    }

    /**
     * The remainders the conditions of {@code way} on this relation's remainder leave it, all of
     * them met; null where the relation is over no remainder or the way states nothing of it.
     *
     * <p>A condition on the remainder says which remainders the form leaves along the way and
     * nothing else of the form's numbers: whatever one of them stands at, the others still bring
     * the form to each remainder it leaves. So it narrows where the remainder lies and is not a
     * condition tying the numbers ({@link #conditionsOf}).
     */
    private WholeNumberRuns remaindersLeftAlong(Reachability.Reaching way) {
        if (remainder == null) {
            return null;
        }
        WholeNumberRuns out = null;
        for (OnTheWay.TakenIn taken : way.boundedOnTheWay()) {
            if (taken.demand() instanceof RowDemand.OnARemainder on && remainder.isAskedBy(on)) {
                out = out == null ? on.leaves() : out.and(on.leaves());
            }
        }
        return out;
    }

    /** What a way is read by: what narrowed its region, what it states, the remainders it leaves
     *  this relation's remainder, whether nothing unread bears on the relation, which parameters
     *  what it declined may name and what the run works out asks of a row. */
    private record Along(List<TakenConstraint> region, List<OnAWay> conditions,
                         WholeNumberRuns remainders, boolean heldWhole,
                         Optional<Set<String>> declined, DemandReading.Answered past) {}

    /**
     * The parameters what {@code way} declined may name a position under — or empty where some of
     * it may name any: a condition on no answer of a dependency, or one whose parts were not all
     * read.
     */
    private static Optional<Set<String>> parametersDeclined(Reachability.Reaching way) {
        Set<String> out = new HashSet<>();
        for (OnTheWay.Declined each : way.declined()) {
            Optional<Set<String>> named = each.parametersNamed();
            if (named.isEmpty()) {
                return Optional.empty();
            }
            out.addAll(named.get());
        }
        return Optional.of(out);
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
     * <p>A condition on what a dependency answered is not declined for anything bearing on the
     * relation either, where every position of the input it names beside the answer is under a
     * parameter none of this relation's places is under. The answer is a value nothing relates to
     * the input, and no declaration relates one parameter to another, so the condition narrows
     * which answer the row stands the dependency in with and nothing this relation reads. Where
     * some side is read off places this cannot name, the condition has to name none at all.
     */
    private boolean nothingUnreadBearsOnIt(Reachability.Reaching way) {
        if (way.declined().isEmpty()) {
            return true;
        }
        Optional<Set<String>> parameters = parametersRead();
        return way.declined().stream().allMatch(declined -> (parameters.isPresent()
                        ? declined.namesNoneOf(parameters.get())
                        : declined.namesNothingOfTheInput())
                || sides.stream().anyMatch(side ->
                        side.kept() != null && findsTheEndOf(declined, side.kept().seed())));
    }

    /**
     * The parameters this relation reads a place under: those of its places, and those of what a
     * walk handing a side its value walks or starts from — or empty where some side is read off
     * no place this names, as what an operation answered of something unnamed is, since that side
     * may be read off any of them.
     */
    private Optional<Set<String>> parametersRead() {
        Set<String> out = new HashSet<>();
        amongThemselves.forEach(place -> out.add(place.path().head()));
        for (Side each : sides) {
            Optional<List<TermPath>> read = placesRead(each);
            if (read.isEmpty()) {
                return Optional.empty();
            }
            read.get().forEach(place -> out.add(place.head()));
        }
        return Optional.of(out);
    }

    /**
     * The places of the input what {@code side} comes to is worked out from — its own, and those
     * of what a walk handing it its value walks or starts from — or empty where some of them are no
     * place this names: what an operation answered of something unnamed, or how many elements meet
     * a statement that reads what was not read.
     *
     * <p>Not where the relation is reported: a count of the elements meeting a statement is at no
     * position, and is worked out from the container and from what the statement reads of each
     * element.
     */
    private static Optional<List<TermPath>> placesRead(Side side) {
        List<TermPath> out = new ArrayList<>();
        side.madeOf().forEach(place -> out.add(place.path()));
        switch (side.along()) {
            case null -> {
                if (side.madeOf().isEmpty() && side.number() == null) {
                    return Optional.empty();
                }
            }
            case Quantity.KeptSoFar kept -> {
                out.add(kept.container());
                out.addAll(kept.ofEach().placesReadOff());
                if (kept.seed() instanceof Quantity.KeptSoFar.Seed.OfTheInput(var from)) {
                    out.add(from.subjectPath());
                }
            }
            case Quantity.PositionInTheWalk position -> out.add(position.container());
            case Quantity.HowManyMeet counted -> {
                Optional<List<TermPath>> read = PositionsAStatementReads.of(counted.ofTheElement());
                if (read.isEmpty() || !(counted.container() instanceof DecisionSubject.AnInput(
                        TermPath container))) {
                    return Optional.empty();
                }
                out.add(container);
                out.addAll(read.get());
            }
        }
        return Optional.of(out);
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
     * holds {@code x} at nought or at one, which the way whole says nothing of.
     *
     * <p>A way looked along whole past the figure is one whose branches past it were not split
     * out. It is read again with each choice on it as it is shown to come to for this relation
     * ({@link #readAgainForThis}), and its branches are those of what that comes to; where
     * no choice is shown to come to less, nothing is shown of it. A way read again that no row
     * takes adds nothing to {@code into}, since no row takes the way it was read from either.
     *
     * <p>Where nothing is shown of a way past the figure, the figure is why — a run allowed more
     * ways would have split it — and so is each figure the reading again reached, past which a
     * choice was kept as it stands. Those are added to {@code stopped}, which is what the relation
     * says it stopped at.
     */
    private boolean branchesOf(Reachability.Reaching way, List<Reachability.Reaching> into,
                               InputReading read, Set<CompositionBudget> stopped) {
        return switch (way.ways()) {
            case Reachability.Ways.One _ -> into.add(way);
            case Reachability.Ways.Each each -> {
                for (Reachability.Reaching branch : each.along()) {
                    if (!branchesOf(branch, into, read, stopped)) {
                        yield false;
                    }
                }
                yield true;
            }
            case Reachability.Ways.Whole whole -> {
                AWayReadForARelation.ReadAgain again = readAgainForThis(whole, read);
                boolean shown = again.as().isPresent()
                        && (!(again.as().get() instanceof Reachability.Reaching reaching)
                                || branchesOf(reaching, into, read, stopped));
                if (!shown) {
                    stopped.add(whole.figure());
                    stopped.addAll(again.stoppedAt());
                }
                yield shown;
            }
        };
    }

    /**
     * The way {@code whole} was read from, read again with each choice on it as it comes to for
     * this relation ({@link AWayReadForARelation}) — or nothing where this relation reads places
     * that cannot be named.
     */
    private AWayReadForARelation.ReadAgain readAgainForThis(Reachability.Ways.Whole whole,
                                                            InputReading read) {
        Set<TermPath> bearing = positionsRead();
        return bearing == null ? new AWayReadForARelation.ReadAgain(Optional.empty(), Set.of())
                : AWayReadForARelation.of(whole, bearing, declarationsOf(read));
    }

    /**
     * What the declarations of {@code read} say of the positions a way is read again over.
     *
     * <p>Made for one reading again, which asks of every pair of positions whether they are tied:
     * the classes each is in are worked out once a position, and let go with the reading.
     */
    private static AWayReadForARelation.Declarations declarationsOf(InputReading read) {
        return new AWayReadForARelation.Declarations() {
            @Override
            public boolean tie(TermPath one, TermPath other) {
                return overlap(one, other) || tiedByARule(one, other, read);
            }

            @Override
            public boolean nameNothingAt(TermPath at) {
                return namedByTheDeclarations(at, read) == Named.NOT;
            }

            @Override
            public NumericDomain.Bounds leaveEveryValueBetween(NumericTerm term) {
                // A value at a place inside an element, or under a key, is one only where the
                // row holds such an element, and a statement of it is of some of them.
                if (!(term instanceof NumericTerm.ValueOf value) || !value.position().steps()
                        .stream().allMatch(step -> step instanceof TermPath.Step.Field
                                || step instanceof TermPath.Step.Refine)) {
                    return null;
                }
                return everyValueTheDeclarationsLeave(value, read, false);
            }

            @Override
            public boolean leaveAValueOf(TypeSymbol leaf) {
                return aValueIsShownToExist(Type.ref(leaf), read);
            }
        };
    }

    /**
     * The ends between which a row may hold {@code value} at every value and at no other: what
     * the declarations leave it, within where its type stops — or null where that is not shown.
     * Shown only of a number on an order that is a count or a decimal, that no rule of a value
     * around it names — or, where {@code aRuleMayNameIt}, that rules name only so that its ends
     * are the whole of what they leave it.
     */
    private static NumericDomain.Bounds everyValueTheDeclarationsLeave(
            NumericTerm.ValueOf value, InputReading read, boolean aRuleMayNameIt) {
        // A number is given a value only on an order that is a count or a decimal, whose
        // every whole number between its ends is one of its values; a string's place on
        // its order has no count under it to give.
        TermOrders orders = read.quantities().ordersOf(value);
        Carrier carrier = orders == null ? null : orders.answered();
        Source source = sourceOf(value, read);
        if (carrier == null || spacingOf(carrier) == null || source == null
                || (source.named() && (!aRuleMayNameIt || source.relaxed()))) {
            return null;
        }
        NumericDomain.Bounds declared = switch (source.takes()) {
            case Takes.Every _ -> NumericDomain.Bounds.OPEN;
            case Takes.Some some -> !source.onlyItsEnds() ? null
                    : some.ends() == null ? NumericDomain.Bounds.OPEN : some.ends();
        };
        // Every value the declarations leave it is one its type holds only up to where the
        // type stops: an Int past the greatest is no Int, whatever the rules leave.
        return declared == null ? null : declared.meet(carrier.whereItStops());
    }

    /**
     * The positions this relation reads: those of its places, and those a walk handing a side its
     * value walks or starts from — or null where some side is read off places this cannot name,
     * as what an operation answered of something unnamed is.
     */
    private Set<TermPath> positionsRead() {
        Set<TermPath> out = new LinkedHashSet<>();
        places().forEach(place -> out.add(place.path()));
        for (Side each : sides) {
            if (each.number() != null) {
                out.addAll(each.number().placesReadOff());
            }
            switch (each.along()) {
                case null -> {
                    if (each.madeOf().isEmpty() && each.number() == null) {
                        return null;
                    }
                }
                case Quantity.KeptSoFar kept -> {
                    out.add(kept.container());
                    out.addAll(kept.ofEach().placesReadOff());
                    if (kept.seed() instanceof Quantity.KeptSoFar.Seed.OfTheInput(var from)) {
                        out.addAll(from.placesReadOff());
                    }
                }
                case Quantity.PositionInTheWalk position -> out.add(position.container());
                case Quantity.HowManyMeet counted -> {
                    Optional<List<TermPath>> reads =
                            PositionsAStatementReads.of(counted.ofTheElement());
                    if (reads.isEmpty()
                            || !(counted.container() instanceof DecisionSubject.AnInput(
                                    TermPath container))) {
                        return null;
                    }
                    out.add(container);
                    out.addAll(reads.get());
                }
            }
        }
        return out;
    }

    /**
     * What a way states, as what each statement turns on: what it took in, each as the demand it
     * is, and each case it requires.
     */
    private static List<OnAWay> conditionsOf(Reachability.Reaching way, RemainderSide remainder) {
        List<OnAWay> out = new ArrayList<>();
        way.boundedOnTheWay().forEach(taken -> {
            // Where the relation's remainder lies, which is read apart ({@link
            // #remaindersLeftAlong}).
            if (remainder != null && taken.demand() instanceof RowDemand.OnARemainder on
                    && remainder.isAskedBy(on)) {
                return;
            }
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
                 RowDemand.SoMany _, RowDemand.OnARemainder _, RowDemand.ForTheRun _ -> null;
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
     * @param remainders the remainders the way leaves this relation's remainder, or null where it
     *                 states nothing of it ({@link #remaindersLeftAlong})
     * @param declined the parameters what the way declined may name a position under, or empty
     *                 where it may name any ({@link #parametersDeclined})
     * @param past     what the run works out asks of a row: the numbers it narrows, which the
     *                 region took in and the way does not state as a condition, and the places
     *                 it ties together, which a region does not say
     */
    private WhatItLeaves leftAlong(InputReading read, List<Source> sources,
                                   List<Carrier> carriers, SearchRegion region,
                                   List<OnAWay> written, WholeNumberRuns remainders,
                                   boolean heldWhole,
                                   Optional<Set<String>> declined, DemandReading.Answered past,
                                   CountWitnesses.Lookup witnesses) {
        // A way stating nothing but that the rows are off the line this relation draws — the form
        // held unequal to nought, as `sign == 0` taken the other way holds
        // `Decimal.compare(a, b)` — ties no side to anything: it takes the rows on the line away,
        // and each side is asked of the rows the declarations leave either side of it
        // (WhatARelationLeavesUndivided#leavesOffItsLine). Only where that is all it states: the
        // region it answers holds the line taken out, which no run is, and beside another
        // statement there is no region of the rest to ask instead.
        TakenConstraint.Affine asStated = remainder == null ? askedAsAStatement() : null;
        boolean offItsLine = asStated != null && !written.isEmpty()
                && written.stream().allMatch(each -> keepsOffTheLineOf(each, asStated));
        List<OnAWay> unfree = offItsLine ? List.of()
                : withoutWhatAFreeNumberMeets(written, declined, past, read);
        // What the way leaves of the lengths of the strings this relation is between, asked once
        // for everything below that reads it. Where a value of the numbers it ties a length to is
        // shown for every length the string has, what it states of the length leaves its strings
        // as they were.
        RoomOnTheWay lengthsRoom = heldWhole
                ? roomAmongTheSides(carriers, written, past, declined, read) : null;
        if (!offItsLine && lengthsRoom != null && lengthsRoom.counts() == null) {
            unfree = unfree.stream()
                    .filter(each -> !lengthsRoom.statements().contains(each)).toList();
        }
        // What the way states of the form asked is decided, or leaves no row, by every statement
        // of it, so it is asked before any is taken away.
        WhatStatementsOfOneFormDecide.Verdict decided = WhatStatementsOfOneFormDecide.of(
                unfree.stream().map(OnAWay::affine).toList(), askedAsAStatement());
        // The way as it states itself, which every reading but the terms' own is made of.
        WayRead entire = wayRead(unfree, past, unfree.size() != written.size(), region,
                offItsLine, read, sources, heldWhole);
        // A statement a row beside this relation's line meets leaves the sides as they stand to
        // one another there, whatever the others hold. Each term is read without it, and no
        // other reading is: they speak of the whole of what the way leaves, and a row beside the
        // line is not that. What is left of the way still ties the terms it ties: a witness is a
        // term nothing ties to any other, so two terms the rest of the way holds to one another
        // are neither of them one, and a value is settled only over every value the others may
        // hold, which a tie among them cannot widen.
        List<TakenConstraint.Affine> met = offItsLine ? List.of()
                : metByARowAtTheLine(unfree, past.narrowing());
        WayRead beside = met.isEmpty() ? entire : wayRead(
                unfree.stream().filter(each -> each.affine() == null
                        || !met.contains(each.affine())).toList(),
                past.without(met), true, region, offItsLine, read, sources, heldWhole);
        SearchRegion along = entire.along();
        SearchRegion declared = entire.declared();
        LeftToTheCalendar left = entire.left();
        List<OnAWay> conditions = left.conditions();
        List<List<OnAWay>> stating = entire.stating();
        Set<Figure> stopped = new LinkedHashSet<>();
        Set<FilingCoordinate> byTheFormat = heldWhole ? leftByTheFormat(read, conditions, stopped)
                : null;
        // The rules of the declarations a row at this line needs nothing of leave the numbers they
        // relate as the way's own statements do: each is read over the run the region answers.
        Roomy room = offItsLine ? Roomy.NONE
                : rulesLeavingRoomAroundTheLine(read, placesTheWayTouches(conditions, past));        List<WhatARelationLeavesUndivided.Term<FilingCoordinate>> terms =
                termsAlong(read, withoutWhatARowAtTheLineNeeds(sources, room, read), carriers,
                        beside.along().withoutTheRelationOf(room.parts()),
                        beside.declared().withoutTheRelationOf(room.parts()),
                        beside.conditions(), remainders, beside.stating(), heldWhole,
                        beside.narrowing(), byTheFormat != null);
        Set<FilingCoordinate> out = new LinkedHashSet<>(amongThemselves);
        Map<NumericTerm, WhatARelationLeavesUndivided.Leaves.Settled> settled =
                new LinkedHashMap<>();
        if (decided.noRowArrives()) {
            return WhatItLeaves.ofAWayNoRowComesAlong(places());
        }
        if (decided.relationIsDecided()) {
            out.addAll(places());
            return new WhatItLeaves(out, settled);
        }
        // A way that relates a term to other numbers leaves it the run the region answers, and
        // the pair is asked whether the way ties them as well as whether the declarations do.
        Set<Object> roomy = room.rules();
        TiedOnTheWay tied = TiedOnTheWay.of(beside.conditions(), read, roomy);
        List<Set<Object>> tiedTo = new ArrayList<>();
        for (int i = 0; i < sides.size(); i++) {
            tiedTo.add(tiedTo(i, tied, beside.conditions(), sources, read, roomy));
        }
        // A code point of the string the remainder's form is of stands apart from the form where
        // the format shows the form leaves every remainder whatever that code point is, and the
        // way states nothing of it that holds a string back: then all the way ties the two by is
        // what every string of the format meets.
        WhatARelationLeavesUndivided.Independence independent =
                (one, other) -> (byTheFormat != null && apartByTheFormat(one, other)
                        && terms.get(one).realizes() != null && terms.get(other).realizes() != null)
                        || (apartByTheDeclarations(one, other, sources, read, roomy)
                                && Collections.disjoint(tiedTo.get(one), tiedTo.get(other)));
        BiPredicate<FilingCoordinate, FilingCoordinate> overlapping = byTheFormat == null
                ? UndividedByARelation::overlap
                : (one, other) -> !apartByTheFormat(one, other) && overlap(one, other);
        if (kind == Kind.PRODUCT) {
            for (int at = 0; at < 2; at++) {
                int other = 1 - at;
                boolean apart = !overlapping(sides.get(at), sides.get(other))
                        && independent.between(at, other);
                putDown(at, WhatARelationLeavesUndivided.leavesOfAProduct(terms.get(at),
                        terms.get(other), constant.negated(), relation, apart,
                        greatestOf(carriers.get(at))), out, settled);
            }
            return reachedAlong(new WhatItLeaves(out, settled), past, read, along, written,
                    declined);
        }
        if (kind == Kind.DIVISIBILITY) {
            boolean apart = !overlapping(sides.get(0), sides.get(1))
                    && independent.between(0, 1);
            for (int at = 0; at < 2; at++) {
                putDown(at, WhatARelationLeavesUndivided.leavesOfADivisibility(terms.get(0),
                        terms.get(1), at == 0, relation, apart, endsOf(carriers.get(0)),
                        endsOf(carriers.get(1))), out, settled);
            }
            return reachedAlong(new WhatItLeaves(out, settled), past, read, along, written,
                    declined);
        }
        // A string inside another parts each by the strings the other can be inside, or hold: no
        // string is shown undivided, which is a claim about every pair of values, and the strings
        // the other can come to are what each is parted by.
        if (kind.inside() != null) {
            WhatItLeaves shown = new WhatItLeaves(out, settled, true, stopped);
            Set<TermPath> accounted = Set.of();
            if (heldWhole && !overlapping(sides.get(0), sides.get(1))
                    && independent.between(0, 1)) {
                Partnering partnering = stringsAPartnerCanHold(carriers, out, read, lengthsRoom,
                        lengths -> getsPastExactlyOn(past, read, along, written, declined, true,
                                lengths));
                shown = shown.partnered(partnering.strings());
                accounted = partnering.accountedFor();
            }
            return reachedAlong(shown, past, read, along, written, declined, accounted);
        }
        // Where an element stands in a walk, or how many elements meet a statement, lies beside
        // how many the container holds, and the two are asked together and not each apart.
        Within lying = offItsLine || !heldWhole || remainder != null ? null
                : Optional.ofNullable(positionWithinItsWalk(conditions))
                        .orElseGet(() -> countWithinItsContainer(conditions, witnesses, stopped));
        if (lying != null) {
            WhatARelationLeavesUndivided.WithinTheWhole within = lying.within();
            // How many the container holds takes each of its values in some row where the region
            // shows that of the container, whatever the declarations say a count answers.
            List<WhatARelationLeavesUndivided.Term<FilingCoordinate>> asked =
                    new ArrayList<>(terms);
            WhatARelationLeavesUndivided.Term<FilingCoordinate> whole = terms.get(within.whole());
            asked.set(within.whole(), new WhatARelationLeavesUndivided.Term<>(whole.madeOf(),
                    whole.weight(), whole.holds(), howManyAreHeld(lying.container(), read, along,
                            lying.anElementShown()),
                    whole.takes(), whole.itsPlace(), whole.spacing(), whole.runsTo()));
            WhatARelationLeavesUndivided.Leaves ofTheWhole =
                    WhatARelationLeavesUndivided.leavesOfTheWhole(asked, within, constant, relation,
                            greatestOf(carriers.get(within.whole())));
            if (settledAtEveryValue(ofTheWhole)) {
                out.addAll(places());
                return new WhatItLeaves(out, settled);
            }
            putDown(within.whole(), ofTheWhole, out, settled);
            return reachedAlong(new WhatItLeaves(out, settled), past, read, along, written,
                    declined);
        }
        // Each side asked once: whether another reaches it, and where it does not, which of its
        // values settle the relation.
        List<WhatARelationLeavesUndivided.Leaves> leaves = new ArrayList<>();
        List<WhatARelationLeavesUndivided.JointSupport> supports =
                datePartsTogether(sources, stating, heldWhole, left.years());
        WhatARelationLeavesUndivided.Operations operations = operationsOverTheSides(read);
        for (int at = 0; at < sides.size(); at++) {
            WhatARelationLeavesUndivided.Leaves each = offItsLine
                    ? WhatARelationLeavesUndivided.leavesOffItsLine(terms, at, constant, relation,
                            overlapping, independent,
                            granularityOf(carriers.get(at)), greatestOf(carriers.get(at)),
                            supports, operations)
                    : WhatARelationLeavesUndivided.leavesOf(terms, at, constant, relation,
                            overlapping, independent,
                            granularityOf(carriers.get(at)), greatestOf(carriers.get(at)),
                            supports, operations);
            leaves.add(each);
            if (settledAtEveryValue(each)) {
                out.addAll(places());
                return new WhatItLeaves(out, settled);
            }
            if (each instanceof WhatARelationLeavesUndivided.Leaves.Undivided) {
                // The remainder is left undivided by every number of its form at once, and a
                // number of the form is left undivided where the rest of the form takes it
                // through every remainder whatever value that number is at.
                out.addAll(remainder == null || at != 0 ? sides.get(at).madeOf()
                        : byTheFormat != null ? byTheFormat
                        : placesOfTheFormLeftEveryRemainder(read, conditions, heldWhole));
            }
        }
        // How far apart two sides are is asked of the relation as it stands, line and all. A row
        // on each side is shown by the sizes of the form's addends, which is so only where a row
        // within them is computed, asked of every side of the relation and not of the two. The
        // values a difference settles are asked of the operations as well, which check themselves.
        boolean sizesAreRowsComputed = operations.theSizesAreRowsComputed(terms, constant);        if (!out.containsAll(places()) && !offItsLine) {
            out.addAll(undividedByTheDifference(sources, carriers, stating, heldWhole, read,
                    declared, independent, operations, sizesAreRowsComputed));
        }
        // A side nothing above showed anything of is asked of the differences the two stand
        // apart by, each in the run the declarations leave it.
        if (!out.containsAll(places()) && !offItsLine) {
            List<WhatARelationLeavesUndivided.Leaves> apart =
                    leftByTheirDifference(sources, carriers, stating, heldWhole, read, along,
                            independent, operations, sizesAreRowsComputed);
            for (int at = 0; at < apart.size(); at++) {
                if (leaves.get(at) != null || out.containsAll(sides.get(at).madeOf())) {
                    continue;
                }
                if (apart.get(at) instanceof WhatARelationLeavesUndivided.Leaves.Undivided) {
                    out.addAll(sides.get(at).madeOf());
                } else {
                    leaves.set(at, apart.get(at));
                }
            }
        }
        for (int at = 0; at < sides.size(); at++) {
            if (leaves.get(at) instanceof WhatARelationLeavesUndivided.Leaves.Settled
                    && !out.containsAll(sides.get(at).madeOf())) {
                putDown(at, leaves.get(at), out, settled);
            }
        }
        WhatItLeaves shown = new WhatItLeaves(out, settled, true, stopped);
        Set<TermPath> accountedFor = Set.of();
        if (sides.size() == 2 && heldWhole && independent.between(0, 1)) {
            Partnering partnering = stringsAPartnerCanHold(carriers, out, read, lengthsRoom,
                    lengths -> getsPastExactlyOn(past, read, along, written, declined, true,
                            lengths));
            shown = shown.partnered(partnering.strings());
            accountedFor = partnering.accountedFor();
        }
        return reachedAlong(shown, past, read, along, written, declined, accountedFor);
    }

    /**
     * The strings each side of an equality is parted by, and the places whose lengths that
     * parting accounts for.
     *
     * @param strings      what each side the equality parts is parted by
     * @param accountedFor the places of strings whose every length is one a run gets past what
     *                     the way ties it to, or whose lengths a run gets past it at are the
     *                     ones {@code strings} shows and the rest it leaves open: a tie of the
     *                     way that reads only such places is not one the run may stop on. A place
     *                     is here for the claim made of that place itself, and never for a claim
     *                     made of the other side
     */
    private record Partnering(Map<NumericTerm.FromOnePosition, StringsAPartnerCanHold> strings,
                              Set<TermPath> accountedFor) {

        static final Partnering NONE = new Partnering(Map.of(), Set.of());
    }

    /**
     * The strings each side of an equality between the strings at two positions is parted by, for
     * the sides not already shown undivided: the strings some value of the other side is, and the
     * strings no value of it is.
     *
     * <p>Where the two sides are free of one another, a value of this side can be the other's
     * exactly when the other can hold it, so the other's declarations are the whole of what parts
     * this side — and the equality is true at none of the strings the other cannot hold, whatever
     * is written at the other. Nothing is said where the other's strings are not worked out
     * exactly, since a value it cannot hold would then be counted among those it can.
     *
     * <p>Along a way that states something or works something out before the relation, only where
     * none of that reaches the strings of either side: a statement about the container an element
     * is in, or about whether a value is there, leaves the strings of both as they were, and a
     * stop on a value that is no string of theirs does too.
     *
     * <p>Where the way ties the length of a string to other numbers — states a sum of the length
     * and a number of the row, or works out one that must stay within its type — the strings are
     * parted at the lengths some value of those numbers gets the run past, and at no other
     * ({@link #roomOnTheWay}). A string of another length is shown neither way.
     *
     * @param shown      the places already shown undivided, which need no other word
     * @param room       what the way leaves of the lengths of the two strings, or null where this
     *                   is no equality between two strings, nor one string inside another, or
     *                   that is not worked out
     * @param reachExactlyOn the case conversions the run is shown to get to the relation past only
     *                   exactly, given the places whose lengths are accounted for, or nothing
     *                   where it is not shown to get there at the values it reads; asked only
     *                   once a pair of strings is otherwise parted
     */
    private Partnering stringsAPartnerCanHold(
            List<Carrier> carriers, Set<FilingCoordinate> shown, InputReading read,
            RoomOnTheWay room,
            Function<Set<TermPath>, Optional<List<ConvertedOn>>> reachExactlyOn) {
        if (room == null) {
            return Partnering.NONE;
        }
        boolean inside = kind.inside() != null;
        Optional<List<ConvertedOn>> reach = null;
        Map<NumericTerm.FromOnePosition, StringsAPartnerCanHold> out = new LinkedHashMap<>();
        Set<TermPath> accountedFor = new LinkedHashSet<>();
        for (int at = 0; at < 2; at++) {
            Side here = sides.get(at);
            Side there = sides.get(1 - at);
            NumericTerm.ValueOf mine = placeOf(here);
            NumericTerm.ValueOf theirs = placeOf(there);
            if (mine == null || theirs == null
                    || (here.piece() != null && there.piece() != null)
                    || !(carriers.get(at) instanceof Carrier.Text)
                    || !(carriers.get(1 - at) instanceof Carrier.Text)) {
                continue;
            }
            // A side already shown undivided needs no other word, but for the strings a run does
            // not get to the relation at: those it shows over a region only.
            boolean undivided = shown.contains(FilingCoordinate.of(mine));
            // A place every length of which gets a run past what the way ties it to is accounted
            // for whatever becomes of its parting. One whose lengths do at some only is accounted
            // for where its parting leaves the rest open, which is below.
            if (room.counts() == null && room.place() != null) {
                accountedFor.add(room.place());
            }
            ValueSet theirStrings = stringsShownAt(theirs.subjectPath(), read);
            if (theirStrings == null) {
                continue;
            }
            // A string is inside the partner's only if the partner is a string the run gets to the
            // relation with, so the strings it is inside are those of the lengths it gets there at.
            boolean partnerHeld = room.counts() != null
                    && room.limitedTo().equals(theirs.subjectPath());
            if (inside && partnerHeld) {
                Language partner = languageOf(theirStrings);
                Language reaching = partner == null ? null : Partitions.ofTheLengths(partner,
                        room.counts(), PatternPlan.Budget.OF_THE_PIECES_OF_A_LANGUAGE.meter());
                if (reaching == null) {
                    continue;
                }
                theirStrings = ValueSet.matching(reaching);
            }
            String called = inside ? calledInside(at == 0, there.text(), theirs.subjectPath())
                    : there.piece() == null ? theirs.subjectPath().toString()
                    : there.piece().calledOver(theirs.subjectPath().toString());
            ValueSet mineHolds = stringsAtMostAt(mine.subjectPath(), read);
            StringsAPartnerCanHold strings = partnerCanHold(at == 0, here, there, theirStrings,
                    mineHolds, called);
            if (room.counts() != null && room.counts().strings() == null) {
                continue;
            }
            if (strings != null && room.counts() != null) {
                strings = !partnerHeld ? strings.reachedAt(room.counts())
                        : inside ? strings : strings.partnerHeldTo(room.counts());
            }
            // Nothing to part where every string is shown on one side: none may be the partner's,
            // or every one is shown to be. Where every one only may be, some are open, and the
            // strings shown on a side are still parted from them.
            if (strings == null || strings.mayBe().isEmpty()
                    || strings.mayBe() instanceof ValueSet.WholeRuns
                    || (!undivided && strings.mayBe().isAny() && strings.leavesNoneOpen())) {
                continue;
            }
            if (reach == null) {
                reach = reachExactlyOn.apply(
                        room.place() == null ? Set.of() : Set.of(room.place()));
            }
            if (reach.isEmpty() || (undivided && reach.get().isEmpty())) {
                continue;
            }
            StringsAPartnerCanHold exact = onlyWhereTheRunGetsPast(strings, reach.get(),
                    at == 0, here, there, mine.subjectPath(), theirs.subjectPath(), theirStrings,
                    mineHolds);
            if (exact != null && !(undivided && exact.leavesNoneOpen())) {
                out.put(mine, exact);
            }
        }
        // A place parted with the other lengths left open has the claim made of the place itself
        // met. Where it is the partner's lengths that are held, the claim made of the partner is
        // not that parting's and is left to its own: it is read off what was recorded for each
        // place, and not set beside it.
        out.forEach((place, strings) -> {
            if (strings.reached() != null) {
                accountedFor.add(place.subjectPath());
            }
        });
        return new Partnering(out, accountedFor);
    }

    /**
     * What a way leaves of the lengths of the strings at two places: whether it ties the length of
     * one of them to other numbers, and at which lengths the run to the relation still gets there.
     *
     * @param place        the place whose length the way ties to other numbers, or null where it
     *                     ties the length of neither
     * @param limitedTo    the place whose strings the way holds to {@code lengths}, or null where
     *                     it holds the strings of neither
     * @param counts       the lengths, or the numbers of code points of a class, at which the run
     *                     gets to the relation, or null where it does so at every one the place
     *                     holds
     * @param statements   the statements of the way that {@code counts} takes account of, which
     *                     leave the strings as they were where {@code counts} is null
     */
    private record RoomOnTheWay(TermPath place, TermPath limitedTo,
                                StringsPastTheWay counts, Set<OnAWay> statements) {

        /** A way that leaves the strings of both as the declarations hold them. */
        static final RoomOnTheWay UNTOUCHED = new RoomOnTheWay(null, null, null, Set.of());
    }

    /**
     * What the way leaves of the lengths of the strings at {@code mine} and {@code theirs}, or
     * null where it leaves something of them that is not worked out.
     *
     * <p>A statement of the way that turns on the length of a string, and an operation the run
     * works out that must stay within its type, hold the length against other numbers of the row.
     * The numbers the declarations leave free of everything else, each at every value between its
     * ends, are taken out of those statements together ({@link LengthsPastTheWay}), and what is
     * left is the lengths a run gets to the relation with. Where they are every length the place
     * holds, the strings are as the declarations hold them.
     *
     * <p>Not for a piece of a string, which is the strings of another length than the place's.
     */
    private static RoomOnTheWay roomOnTheWay(TermPath mine, TermPath theirs,
                                             List<OnAWay> written,
                                             DemandReading.Answered past,
                                             Optional<Set<String>> declined, InputReading read,
                                             PiecesOfAString piece) {
        if (piece != null || past.narrowing().stream().anyMatch(constraint ->
                constraint.terms().stream().anyMatch(term -> overlap(term.subjectPath(), mine)
                        || overlap(term.subjectPath(), theirs)))) {
            return leavesTheStringsOf(mine, theirs, written, past.narrowing(), piece)
                    ? RoomOnTheWay.UNTOUCHED : null;
        }
        List<TakenConstraint> system = new ArrayList<>();
        Set<OnAWay> stated = new LinkedHashSet<>();
        for (OnAWay each : written) {
            boolean saysNothingOfValues = each.whatStands() && each.relation() == null
                    && each.elementsOf() == null;
            if (saysNothingOfValues) {
                continue;
            }
            if (each.elementsOf() != null) {
                return null;
            }
            if (reaches(each, mine) || reaches(each, theirs)) {
                if ((each.whatStands() && !endsACountOfAStringAt(each, mine, theirs))
                        || !(each.relation() instanceof TakenConstraint.Affine)) {
                    return null;
                }
                system.add(each.relation());
                stated.add(each);
            }
        }
        Set<DemandReading.Tie> ties = new LinkedHashSet<>();
        for (DemandReading.Tie tie : past.tied()) {
            if (touchesAny(tie.places(), List.of(mine, theirs))) {
                if (tie.by() == null) {
                    return null;
                }
                system.add(tie.by());
                ties.add(tie);
            }
        }
        if (system.isEmpty()) {
            return RoomOnTheWay.UNTOUCHED;
        }
        // Everything the run states or works out of the numbers that stand beside the length is
        // part of what those numbers are held to: a statement the way makes, a tie it keeps, and
        // what a region carries of an operation over numbers outside a container. A number held
        // to something outside the system is not one a value can be chosen for by the system
        // alone, so a hold on such a number that is not taken in leaves nothing proved.
        boolean grew = true;
        Set<TakenConstraint> narrowed = new LinkedHashSet<>();
        List<TermPath> beside = new ArrayList<>();
        while (grew) {
            grew = false;
            beside = placesBesideTheCount(system, mine, theirs);
            List<TermPath> asked = beside;
            for (TakenConstraint each : past.narrowing()) {
                if (narrowed.contains(each) || each.terms().stream().noneMatch(term ->
                        asked.stream().anyMatch(place -> overlap(term.subjectPath(), place)))) {
                    continue;
                }
                if (!(each instanceof TakenConstraint.Affine)) {
                    return null;
                }
                system.add(each);
                narrowed.add(each);
                grew = true;
            }
            for (OnAWay each : written) {
                if (stated.contains(each) || each.relation() == null || each.elementsOf() != null
                        || beside.stream().noneMatch(place -> reaches(each, place))) {
                    continue;
                }
                if (each.whatStands() || !(each.relation() instanceof TakenConstraint.Affine)) {
                    return null;
                }
                system.add(each.relation());
                stated.add(each);
                grew = true;
            }
            for (DemandReading.Tie tie : past.tied()) {
                if (ties.contains(tie) || !touchesAny(tie.places(), beside)) {
                    continue;
                }
                if (tie.by() == null) {
                    return null;
                }
                system.add(tie.by());
                ties.add(tie);
                grew = true;
            }
        }
        // An operation the run may stop at whose owner says where it answers holds the numbers it
        // reads to what no statement here carries, so a value chosen for one of these numbers is
        // not shown to get the run past it.
        for (Pullback.StopObligation owed : past.owed()) {
            if (touchesAny(owed.places(), beside)) {
                return null;
            }
        }
        // And a condition the way declined to read may hold them to what is not said at all.
        if (!beside.isEmpty() && (declined.isEmpty() || beside.stream()
                .anyMatch(place -> declined.get().contains(place.head())))) {
            return null;
        }
        NumericTerm length = null;
        List<TermPath> places = new ArrayList<>();
        for (TakenConstraint constraint : system) {
            for (NumericTerm term : constraint.terms()) {
                if (isACountOfAStringAt(term, mine) || isACountOfAStringAt(term, theirs)) {
                    if (length != null && !length.equals(term)) {
                        return null;
                    }
                    length = term;
                } else if (term instanceof NumericTerm.ValueOf) {
                    places.add(term.subjectPath());
                } else {
                    return null;
                }
            }
        }
        if (length == null) {
            return null;
        }
        places.add(length.subjectPath());
        TermPath limited = length.subjectPath();
        LengthsPastTheWay.Lengths lengths = LengthsPastTheWay.of(length, system,
                number -> endsOfAFreeNumber(number, places, mine, theirs, read));
        if (lengths == null || read.domain().at(limited) == null || lengths.isEmpty()) {
            return null;
        }
        Language strings = stringsAtMostAt(limited, read) instanceof ValueSet.Matching(
                Language language) ? language : null;
        Language.Ends ends = strings == null ? null : strings.lengths();
        // Of the code points of a class the fewest a string holds is none, whatever its length.
        BigInteger fewest = BigInteger.valueOf(
                ends == null || length instanceof NumericTerm.CodePointClassCount
                        ? 0 : ends.least());
        BigInteger most = BigInteger.valueOf(longestOf(strings));
        // Whether the place holds a string of one of these counts is not asked here. The counts
        // are a proof about numbers; the strings of the place at them are met with what it admits
        // where the classes are made, under the allowance of the place, and a side that holds
        // none is drawn as no class ({@link Classing}).
        if (lengths.holds(fewest, most)) {
            return new RoomOnTheWay(limited, null, null, stated);
        }
        StringsPastTheWay counts = length instanceof NumericTerm.CodePointClassCount count
                ? new CodePointsPastTheWay(count.counted(), lengths) : lengths;
        return new RoomOnTheWay(limited, limited, counts, stated);
    }

    /**
     * What the way leaves of the lengths of the strings on the two sides, where this relation is
     * an equality between two strings, or null where it is not or that is not worked out
     * ({@link #roomOnTheWay}). Asked once for a relation: it is the same for both sides.
     */
    private RoomOnTheWay roomAmongTheSides(List<Carrier> carriers, List<OnAWay> written,
                                           DemandReading.Answered past,
                                           Optional<Set<String>> declined, InputReading read) {
        if (sides.size() != 2 || (kind.inside() == null && (kind != Kind.AFFINE
                        || remainder != null || (relation != Rel.EQ && relation != Rel.NE)
                        || !WhatARelationLeavesUndivided.eachStandsAtTheOthersValue(
                                sides.stream().map(Side::weight).toList(), constant)))
                || !(carriers.get(0) instanceof Carrier.Text)
                || !(carriers.get(1) instanceof Carrier.Text)
                || (sides.get(0).piece() != null && sides.get(1).piece() != null)) {
            return null;
        }
        NumericTerm.ValueOf first = placeOf(sides.get(0));
        NumericTerm.ValueOf second = placeOf(sides.get(1));
        PiecesOfAString piece = sides.get(0).piece() != null ? sides.get(0).piece()
                : sides.get(1).piece();
        return first == null || second == null ? null
                : roomOnTheWay(first.subjectPath(), second.subjectPath(), written, past,
                        declined, read, piece);
    }

    /** The places of the numbers {@code system} reads other than the counts of the strings at
     *  {@code mine} and {@code theirs}. */
    private static List<TermPath> placesBesideTheCount(List<TakenConstraint> system,
                                                       TermPath mine, TermPath theirs) {
        List<TermPath> beside = new ArrayList<>();
        system.forEach(constraint -> constraint.terms().forEach(term -> {
            if (!isACountOfAStringAt(term, mine) && !isACountOfAStringAt(term, theirs)) {
                beside.add(term.subjectPath());
            }
        }));
        return beside;
    }

    /**
     * Whether {@code statement} is an end on the length of the string at {@code mine} or at
     * {@code theirs}, or on how many of its code points are in a class, and on nothing else. Such
     * an end is on the strings themselves, whereas the count of a container says nothing of what
     * its elements are ({@link OnAWay#whatStands}).
     */
    private static boolean endsACountOfAStringAt(OnAWay statement, TermPath mine,
                                                 TermPath theirs) {
        return statement.relation() instanceof TakenConstraint.Affine(var form, _)
                && !form.coefs().isEmpty()
                && form.coefs().keySet().stream().allMatch(term ->
                        isACountOfAStringAt(term, mine) || isACountOfAStringAt(term, theirs));
    }

    /**
     * Whether {@code term} is the number of code points of the string at {@code place}, or the
     * number of them in a class. Not of what a case conversion makes of the string, whose code
     * points are not those of the string.
     */
    private static boolean isACountOfAStringAt(NumericTerm term, TermPath place) {
        return isTheLengthOfAStringAt(term, place)
                || (term instanceof NumericTerm.CodePointClassCount count
                        && count.through().equals(CaseMapping.NONE)
                        && count.position().equals(place));
    }

    /** Whether {@code term} is the number of code points of the string at {@code place}. */
    private static boolean isTheLengthOfAStringAt(NumericTerm term, TermPath place) {
        return term instanceof NumericTerm.TakenOf taken
                && taken.operation().equals(ValueName.Stdlib.operation("String", "length"))
                && taken.arguments().equals(TakenArguments.NONE)
                && taken.transformation().equals(ValueTransformation.NONE)
                && taken.position().equals(place);
    }

    /**
     * The ends between which {@code number} may be held at every value, where it is a whole number
     * the declarations tie to none of {@code places}, or null where it is not shown.
     */
    private static LengthsPastTheWay.Ends endsOfAFreeNumber(NumericTerm number,
                                                            List<TermPath> places,
                                                            TermPath mine, TermPath theirs,
                                                            InputReading read) {
        if (!(number instanceof NumericTerm.ValueOf value)) {
            return null;
        }
        TermOrders orders = read.quantities().ordersOf(value);
        if (orders == null || granularityOf(orders.answered()) != Granularity.DISCRETE) {
            return null;
        }
        for (TermPath other : Stream.concat(places.stream(), Stream.of(mine, theirs)).toList()) {
            if (!other.equals(value.subjectPath()) && (overlap(value.subjectPath(), other)
                    || tiedByARule(value.subjectPath(), other, read))) {
                return null;
            }
        }
        NumericDomain.Bounds bounds = everyValueTheDeclarationsLeave(value, read, true);
        return bounds == null ? null : new LengthsPastTheWay.Ends(
                wholeEnd(bounds.min(), true), wholeEnd(bounds.max(), false));
    }

    /** The least whole number {@code end} allows, or the greatest where {@code lower} is false;
     *  null where there is no end. */
    private static BigInteger wholeEnd(Endpoint end, boolean lower) {
        if (end == null || !(end.at() instanceof Count count)) {
            return null;
        }
        ExactRatio at = count.exactly();
        ExactAnswer<BigInteger> rounded = lower ? at.ceiling() : at.floor();
        if (!(rounded instanceof ExactAnswer.Held<BigInteger>(BigInteger whole))) {
            return null;
        }
        boolean on = end.inclusive() || !at.isWhole();
        return on ? whole : lower ? whole.add(BigInteger.ONE) : whole.subtract(BigInteger.ONE);
    }

    /**
     * What a model calls the other side of a string standing inside another: {@code theirs}, the
     * text at {@code path}, which this side is inside or holds as this relation says.
     */
    private String calledInside(boolean hereIsFirst, ConvertedText theirs, TermPath path) {
        String text = theirs == null ? path.toString() : theirs.writtenAround(path.toString());
        StringsInsideStrings.Where where = kind.inside();
        if (hereIsFirst) {
            return switch (where) {
                case ANYWHERE -> "a string inside " + text;
                case AT_THE_START -> "a start of " + text;
                case AT_THE_END -> "an end of " + text;
            };
        }
        return switch (where) {
            case ANYWHERE -> "a string holding " + text;
            case AT_THE_START -> "a string starting with " + text;
            case AT_THE_END -> "a string ending with " + text;
        };
    }

    /**
     * The strings of the side {@code mine} that some string of the other side, {@code theirs}, can
     * stand inside, or hold, as this relation says, and those no string of it can, as far as each
     * is shown ({@link StringsAPartnerCanHold}); or null where the strings are not a language, or
     * the machines for them are more than a piece's allowance.
     *
     * <p>The string looked for stands inside a string of the other side exactly when it is one of
     * the factors, starts or ends of the strings the other side comes to, and a string looked in
     * holds one exactly when it has one of the strings the other side comes to inside it
     * ({@link StringsInsideStrings}). What a side comes to is the conversion done to it, which is
     * exactly a map on the strings it is exactly one for ({@link CodeMap}); the strings it is not
     * exact on come to strings of the code points the conversion leaves, and nothing narrower is
     * said of them.
     */
    private StringsAPartnerCanHold stringsInside(boolean hereIsFirst, ConvertedText mine,
                                                 ConvertedText theirs, ValueSet theirStrings,
                                                 ValueSet mineHolds, String called) {
        Language partner = languageOf(theirStrings);
        if (mine == null || theirs == null || partner == null) {
            return null;
        }
        Meter meter = PatternPlan.Budget.OF_THE_PIECES_OF_A_LANGUAGE.meter();
        StringsInsideStrings.Where where = kind.inside();
        CodeMap theirMap = theirs.through().equals(CaseMapping.NONE) ? null
                : CaseMaps.of(theirs.through());
        // The strings the other side comes to, as far as it is shown: the values it is exactly a
        // map on, converted. And as far as it may come to: those, and the code points a
        // conversion leaves for the strings it is not exact on.
        Language shownOther;
        Language mayOther;
        if (theirMap == null) {
            shownOther = partner.heldAsWritten().language(meter);
            mayOther = partner;
        } else {
            Language exact = theirMap.strings(meter);
            Language within = exact == null ? null : partner.and(exact, meter);
            Language outside = exact == null ? null : partner.and(exact.not(meter), meter);
            shownOther = within == null ? null : theirMap.answersTo(within, meter);
            Language left = outside == null || outside.isEmpty() ? null
                    : CodeMap.stringsOf(theirMap.leftAlone(), meter);
            mayOther = shownOther == null || outside == null ? null
                    : left == null ? shownOther : shownOther.or(left, meter);
        }
        if (shownOther == null || mayOther == null) {
            return null;
        }
        Language shownHere = hereIsFirst ? StringsInsideStrings.standingIn(shownOther, where, meter)
                : StringsInsideStrings.havingInside(shownOther, where, meter);
        Language mayHere = hereIsFirst ? StringsInsideStrings.standingIn(mayOther, where, meter)
                : StringsInsideStrings.havingInside(mayOther, where, meter);
        if (shownHere == null || mayHere == null) {
            return null;
        }
        CodeMap mineMap = mine.through().equals(CaseMapping.NONE) ? null
                : CaseMaps.of(mine.through());
        Language canBe = mineMap == null ? shownHere
                : mineMap.stringsConvertedInto(shownHere, meter);
        Language mayBe = mayHere;
        if (mineMap != null) {
            Language exact = mineMap.strings(meter);
            Language back = mineMap.stringsConvertedInto(mayHere, meter);
            Language inexact = exact == null ? null : exact.not(meter);
            mayBe = back == null || inexact == null ? null : back.or(inexact, meter);
        }
        if (canBe == null || mayBe == null) {
            return null;
        }
        // A string looked for that is shown inside a value stands in one written round it, which
        // is longer than it by what the machine needs before and after.
        long upTo = hereIsFirst
                ? TextExtents.LONGEST_STRING - 2L * (shownOther.size() + 1L)
                : TextExtents.LONGEST_STRING;
        List<String> operations = new ArrayList<>(
                operationsNotExactOver(mine.through(), languageOf(mineHolds)));
        operations.addAll(operationsNotExactOver(theirs.through(), partner));
        if (upTo < 0) {
            return StringsAPartnerCanHold.unreached(ValueSet.NONE, ValueSet.matching(mayBe), null,
                    called).withTheImagesNotShownOf(operations);
        }
        return StringsAPartnerCanHold.unreached(ValueSet.matching(canBe),
                ValueSet.matching(mayBe), hereIsFirst ? upTo : null, called)
                .withTheImagesNotShownOf(operations);
    }

    /**
     * The strings of this side {@code there}, the other, can come to, as far as each is shown
     * ({@link StringsAPartnerCanHold}), or null where none is: {@code theirStrings} are what its
     * place holds, and {@code mine} what this side's does.
     */
    private StringsAPartnerCanHold partnerCanHold(boolean hereIsFirst, Side here, Side there,
                                                  ValueSet theirStrings, ValueSet mine,
                                                  String called) {
        if (kind.inside() != null) {
            return stringsInside(hereIsFirst, here.text(), there.text(), theirStrings, mine,
                    called);
        }
        if (there.piece() != null) {
            return stringsThatAreThePiece(there.piece(), theirStrings, mine, called);
        }
        if (here.piece() != null) {
            return stringsWithAPiece(here.piece(), theirStrings, mine, called);
        }
        return theirStrings.isEmpty() ? null
                : StringsAPartnerCanHold.unreached(theirStrings, called);
    }

    /**
     * {@code strings} for the strings a run gets to the relation at, where it gets there only past
     * {@code conversions} exactly: a string of the other side is the partner's only if the run
     * gets to the relation at it, so those the conversion is not exactly a map on are shown
     * neither way; and a string of this side is shown either way only where the run gets to the
     * relation at it, so the strings the conversion is not exactly a map on are left open. Or null
     * where a conversion is of a place neither side is, or the strings are not a language.
     */
    private StringsAPartnerCanHold onlyWhereTheRunGetsPast(
            StringsAPartnerCanHold strings, List<ConvertedOn> conversions, boolean hereIsFirst,
            Side here, Side there, TermPath mine, TermPath theirs, ValueSet theirStrings,
            ValueSet mineHolds) {
        if (conversions.isEmpty()) {
            return strings;
        }
        Meter meter = PatternPlan.Budget.OF_THE_PIECES_OF_A_LANGUAGE.meter();
        Language onMine = null;
        Language onTheirs = null;
        for (ConvertedOn each : conversions) {
            Language exact = CaseMaps.of(each.conversion()).strings(meter);
            boolean ofMine = each.place().equals(mine);
            if (exact == null || (!ofMine && !each.place().equals(theirs))) {
                return null;
            }
            Language had = ofMine ? onMine : onTheirs;
            Language both = had == null ? exact : had.and(exact, meter);
            if (both == null) {
                return null;
            }
            if (ofMine) {
                onMine = both;
            } else {
                onTheirs = both;
            }
        }
        StringsAPartnerCanHold out = strings;
        if (onTheirs != null) {
            Language partnerHolds = languageOf(theirStrings);
            Language reaching = partnerHolds == null ? null : partnerHolds.and(onTheirs, meter);
            if (reaching == null) {
                return null;
            }
            StringsAPartnerCanHold narrowed = partnerCanHold(hereIsFirst, here, there,
                    ValueSet.matching(reaching), mineHolds, strings.partner());
            out = narrowed == null ? strings.showing(ValueSet.NONE, strings.mayBe(), null)
                    : strings.showing(narrowed.canBe(), strings.mayBe(), narrowed.upTo());
        }
        if (onMine != null) {
            Language canBe = languageOf(out.canBe());
            Language mayBe = languageOf(out.mayBe());
            Language neverReached = onMine.not(meter);
            Language canBeThere = canBe == null ? null : canBe.and(onMine, meter);
            Language mayBeOrNot = mayBe == null || neverReached == null ? null
                    : mayBe.or(neverReached, meter);
            if (canBeThere == null || mayBeOrNot == null) {
                return null;
            }
            out = out.showing(ValueSet.matching(canBeThere), ValueSet.matching(mayBeOrNot),
                    out.upTo());
        }
        // Each conversion the run is gotten past exactly is one whose image is shown only where
        // it is exact, and the strings it is not exact on are the ones left open.
        List<String> operations = new ArrayList<>();
        for (ConvertedOn each : conversions) {
            operations.addAll(operationsNotExactOver(each.conversion(),
                    each.place().equals(mine) ? languageOf(mineHolds)
                            : languageOf(theirStrings)));
        }
        return out.withTheImagesNotShownOf(operations);
    }

    /**
     * The operations of the library that {@code conversion} is made of whose image is not shown
     * over {@code over}: the ones at whose step a string of {@code over} first stops being one the
     * conversion done so far is exactly a map on ({@link CodeMap}).
     *
     * <p>Named by what made them open, and not by being written. A conversion exact on every
     * string of {@code over} leaves nothing open and is named for nothing, and of two done in turn
     * the one named is the one whose step the strings fail at. Where which strings {@code over}
     * holds is not worked out, or the machines for them are more than a piece's allowance, every
     * operation is named: a name too many says where to look, and a name too few says to look
     * elsewhere.
     *
     * @param over the strings the conversion is done to, or null where they are not a language
     */
    private static List<String> operationsNotExactOver(CaseMapping conversion, Language over) {
        List<String> operations = conversion.operations();
        if (over == null) {
            return operations;
        }
        Meter meter = PatternPlan.Budget.OF_THE_PIECES_OF_A_LANGUAGE.meter();
        List<CaseMapping> doneSoFar = conversion.doneSoFar();
        List<String> named = new ArrayList<>();
        Language notExactBefore = Language.EVERY_STRING.not(meter);
        for (int step = 0; step < doneSoFar.size(); step++) {
            Language exact = CaseMaps.of(doneSoFar.get(step)).strings(meter);
            Language notExact = exact == null ? null : over.and(exact.not(meter), meter);
            Language fresh = notExact == null ? null
                    : notExact.and(notExactBefore.not(meter), meter);
            Language notExactNow = notExact == null ? null : notExactBefore.or(notExact, meter);
            if (fresh == null || notExactNow == null) {
                return operations;
            }
            if (!fresh.isEmpty()) {
                named.add(operations.get(step));
            }
            notExactBefore = notExactNow;
        }
        return named;
    }

    /**
     * The strings the place holds, as far as they are shown to be all of them ({@link
     * StringsHeld}), or null where they are not. The strings of the other side of a relation are
     * parted by these, so a place not shown has nothing to part by.
     */
    private static ValueSet stringsShownAt(TermPath place, InputReading read) {
        Position at = read.domain().at(place);
        // A place the declarations are not shown to leave a set of values is not shown to hold
        // any of its strings ({@link #takes}).
        return at == null || sourceOf(new NumericTerm.ValueOf(place), read) == null ? null
                : StringsHeld.at(at);
    }

    /**
     * The strings the place holds at most: those shown to be all of them where they are, and
     * what its set of values admits where they are not; any string where there is no position.
     * Every question of this side of a relation that is asked of the strings it holds is asked
     * of these.
     */
    private static ValueSet stringsAtMostAt(TermPath place, InputReading read) {
        ValueSet shown = stringsShownAt(place, read);
        if (shown != null) {
            return shown;
        }
        Position at = read.domain().at(place);
        return at == null ? ValueSet.ANY : at.admitted().approximation();
    }

    /** The strings {@code set} is, where it is a language of strings, or null. */
    static Language languageOf(ValueSet set) {
        if (set instanceof ValueSet.Matching(Language language)) {
            return language;
        }
        if (set.isAny()) {
            return Language.EVERY_STRING;
        }
        return set.isEmpty()
                ? Language.EVERY_STRING.not(PatternPlan.Budget.OF_THE_PIECES_OF_A_LANGUAGE.meter())
                : null;
    }

    /**
     * The position whose strings {@code side} is read off: the position it is a number of, or the
     * position of the string it is a piece of — or null where it is neither.
     */
    private static NumericTerm.ValueOf placeOf(Side side) {
        if (side.number() instanceof NumericTerm.ValueOf place) {
            return place;
        }
        if (side.text() != null) {
            return side.text().place();
        }
        return side.piece() == null ? null : side.piece().place();
    }

    /**
     * The strings that have a piece of {@code piece} in some string of {@code partner}, and those
     * that have none, or null where {@code partner} is not a language of strings or the machine
     * for them is more than a piece's allowance.
     *
     * <p>A string that has the piece in the strings of the partner is some value's: the piece and
     * the rest of the string are written round it. Where the pieces are those of a string a case
     * conversion made, the strings are the ones the conversion is exactly a map on whose answer has
     * the piece ({@link CodeMap}), and a string it is not exactly a map on is shown neither way.
     */
    private static StringsAPartnerCanHold stringsWithAPiece(PiecesOfAString piece,
                                                            ValueSet partner, ValueSet mineHolds,
                                                            String called) {
        ConvertedText whole = piece.whole();
        if (whole == null || !(partner instanceof ValueSet.Matching(Language language))) {
            return null;
        }
        Meter meter = PatternPlan.Budget.OF_THE_PIECES_OF_A_LANGUAGE.meter();
        Language having = StringsOfAPiece.wholesWithAPieceInWindow(language, piece.separator(),
                piece.window().from(), piece.until(), meter);
        if (having == null) {
            return null;
        }
        if (whole.through().equals(CaseMapping.NONE)) {
            return having.isEmpty() ? null
                    : StringsAPartnerCanHold.unreached(ValueSet.matching(having), called);
        }
        CodeMap map = CaseMaps.of(whole.through());
        Language exact = map.strings(meter);
        Language converted = exact == null ? null : map.stringsConvertedInto(having, meter);
        Language inexact = exact == null ? null : exact.not(meter);
        Language mayBe = converted == null || inexact == null ? null : converted.or(inexact, meter);
        return mayBe == null || mayBe.isEmpty() ? null
                : StringsAPartnerCanHold.unreached(ValueSet.matching(converted),
                        ValueSet.matching(mayBe), null, called)
                        .withTheImagesNotShownOf(operationsNotExactOver(whole.through(),
                                languageOf(mineHolds)));
    }

    /**
     * The strings at {@code mine} shown to be {@code piece} of some value of {@code whole}, and
     * those shown to be that of none, or null where {@code whole} is not a language of strings or
     * the machines for them are more than a piece's allowance
     * ({@link StringsOfAPiece#piecesOfValuesIn}).
     *
     * <p>Told exactly where every string {@code mine} holds is short enough, and its pieces of the
     * strings are its pieces of the values. Otherwise what is shown is kept apart from what is not:
     * the pieces of the strings held as written, up to the length a value is written round each,
     * are values' pieces, and nothing outside the pieces of the strings is — and the strings
     * between are told neither way.
     */
    private static StringsAPartnerCanHold stringsThatAreThePiece(PiecesOfAString piece,
                                                                 ValueSet whole, ValueSet mine,
                                                                 String called) {
        ConvertedText made = piece.whole();
        if (made == null || !(whole instanceof ValueSet.Matching(Language language))) {
            return null;
        }
        Meter meter = PatternPlan.Budget.OF_THE_PIECES_OF_A_LANGUAGE.meter();
        if (!made.through().equals(CaseMapping.NONE)) {
            return piecesOfWhatAConversionAnswers(piece, made.through(), language, mine, called);
        }
        StringsOfAPiece.Shown shown = StringsOfAPiece.piecesOfValuesIn(language,
                piece.separator(), piece.window().from(), piece.until(), meter);
        if (shown == null) {
            return null;
        }
        Language held = mine instanceof ValueSet.Matching(Language strings) ? strings : null;
        long longest = longestOf(held);
        if (shown.allUpTo(longest)) {
            return StringsAPartnerCanHold.unreached(ValueSet.matching(shown.ofTheStrings()),
                    called);
        }
        // No piece is shorter than what is written round it, so none is shown a value's piece.
        if (shown.upTo() < 0) {
            return StringsAPartnerCanHold.unreached(ValueSet.NONE,
                    ValueSet.matching(shown.ofTheStrings()), null, called);
        }
        // Only what this side holds is asked about, so the pieces of strings no value is written
        // as are no gap where this side holds none of them.
        boolean alike = shown.ofTheStrings().equals(shown.ofTheValues());
        if (!alike && held != null) {
            Language between = shown.ofTheStrings().and(shown.ofTheValues().not(meter), meter);
            Language heldBetween = between == null ? null : between.and(held, meter);
            alike = heldBetween != null && heldBetween.isEmpty();
        }
        return StringsAPartnerCanHold.unreached(ValueSet.matching(shown.ofTheValues()),
                ValueSet.matching(alike ? shown.ofTheValues() : shown.ofTheStrings()),
                longest <= shown.upTo() ? null : shown.upTo(), called);
    }

    /**
     * {@link #stringsThatAreThePiece} for the pieces of what {@code conversion} answers of a string
     * of {@code whole}.
     *
     * <p>A string of {@code whole} the conversion is exactly a map on ({@link CodeMap}) answers the
     * string its code points are sent to, as long as it is, so the pieces of those answers are the
     * pieces of values of the conversion. A string it is not exactly a map on may answer anything
     * the conversion answers, and every code point of an answer is one the conversion leaves, so
     * no piece with another is a piece of any value — and a piece with only those is shown neither
     * way unless the exact strings answer it.
     */
    private static StringsAPartnerCanHold piecesOfWhatAConversionAnswers(
            PiecesOfAString piece, CaseMapping conversion, Language whole, ValueSet mine,
            String called) {
        Meter meter = PatternPlan.Budget.OF_THE_PIECES_OF_A_LANGUAGE.meter();
        CodeMap map = CaseMaps.of(conversion);
        Language exact = map.strings(meter);
        Language kept = exact == null ? null : whole.and(exact, meter);
        Language answers = kept == null ? null : map.answersTo(kept, meter);
        StringsOfAPiece.Shown shown = answers == null ? null
                : StringsOfAPiece.piecesOfValuesIn(answers, piece.separator(),
                        piece.window().from(), piece.until(), meter);
        Language alone = CodeMap.stringsOf(map.leftAlone(), meter);
        Language mayBe = shown == null || alone == null ? null
                : alone.or(shown.ofTheValues(), meter);
        if (mayBe == null) {
            return null;
        }
        List<String> notShown = operationsNotExactOver(conversion, whole);
        if (shown.upTo() < 0) {
            return StringsAPartnerCanHold.unreached(ValueSet.NONE, ValueSet.matching(mayBe), null,
                    called).withTheImagesNotShownOf(notShown);
        }
        Language held = mine instanceof ValueSet.Matching(Language strings) ? strings : null;
        long longest = longestOf(held);
        return StringsAPartnerCanHold.unreached(ValueSet.matching(shown.ofTheValues()),
                ValueSet.matching(mayBe), longest <= shown.upTo() ? null : shown.upTo(), called)
                .withTheImagesNotShownOf(notShown);
    }

    /**
     * The most code points a string of {@code held} has: what the language bounds, and the most a
     * {@code String} holds where that is no bound or the strings are not a language.
     */
    private static long longestOf(Language held) {
        Language.Ends lengths = held == null ? null : held.lengths();
        return lengths != null && lengths.most() != null ? lengths.most()
                : TextExtents.LONGEST_STRING;
    }

    /**
     * Whether what a way states, and what the numbers outside a container say along the run,
     * leave the strings at {@code mine} and {@code theirs} as the declarations hold them.
     *
     * <p>A statement of which case a value is, or of how many a container holds, says nothing of
     * the values there; any other statement does not reach them only where it names neither
     * place nor one that holds a place or is held by it. Where {@code theirs} is the string a piece is of, a statement that the string holds
     * the separators the piece's index needs is one the piece's strings already stand on.
     *
     * @param piece the piece the partner is, or null where it is the strings at {@code theirs}
     */
    private static boolean leavesTheStringsOf(TermPath mine, TermPath theirs,
                                              List<OnAWay> written,
                                              List<TakenConstraint> narrowing,
                                              PiecesOfAString piece) {
        for (OnAWay each : written) {
            boolean saysNothingOfValues = each.whatStands() && each.relation() == null
                    && each.elementsOf() == null;
            if (!saysNothingOfValues && !holdsTheSeparatorsOf(each, piece)
                    && (reaches(each, mine) || reaches(each, theirs)
                    || each.elementsOf() != null)) {
                return false;
            }
        }
        return narrowing.stream().noneMatch(constraint -> constraint.terms().stream()
                .anyMatch(term -> overlap(term.subjectPath(), mine)
                        || overlap(term.subjectPath(), theirs)));
    }

    /**
     * Whether {@code statement} turns on {@code place}, or on a place that holds it or is held by
     * it. A statement of what stands at a value that holds the place, how many a container holds,
     * says nothing of the place's values, so only what stands at the place or under it is theirs.
     */
    private static boolean reaches(OnAWay statement, TermPath place) {
        return statement.positions().stream().anyMatch(at -> statement.whatStands()
                ? at.isAtOrUnder(place) : overlap(at, place));
    }

    /**
     * Whether {@code statement} says the string {@code piece} is of holds at least as many of the
     * separator as the piece's index needs and nothing else, which the strings that have a piece
     * at that index all do.
     */
    private static boolean holdsTheSeparatorsOf(OnAWay statement, PiecesOfAString piece) {
        ConvertedText whole = piece == null ? null : piece.whole();
        if (whole == null) {
            return false;
        }
        TermPath string = whole.place().subjectPath();
        if (statement.elementsOf() != null
                || !statement.positions().equals(Set.of(string))
                || !(statement.relation() instanceof TakenConstraint.Affine(
                        LinearForm<NumericTerm> form, Rel rel)) || rel != Rel.GE
                || form.coefs().size() != 1) {
            return false;
        }
        Map.Entry<NumericTerm, ExactRatio> only = form.coefs().entrySet().iterator().next();
        return only.getKey() instanceof NumericTerm.CodePointClassCount count
                && count.position().equals(string)
                && countsTheSeparatorsTheWayThePiecesAreParted(count.through(), whole.through(),
                        piece.separator())
                && count.counted().equals(new CodePointClass.OneOf(
                        CodePoints.of(piece.separator())))
                && only.getValue().equals(ExactRatio.ONE)
                && ExactRatio.of(piece.first()).compareTo(form.constant().negated()) >= 0;
    }

    /**
     * Whether separators counted in a string that {@code counted} was done to are the ones the
     * pieces of a string that {@code parted} was done to are parted at: the same conversion, or
     * none where the conversion sends no other code point to the separator and leaves it.
     */
    private static boolean countsTheSeparatorsTheWayThePiecesAreParted(CaseMapping counted,
                                                                      CaseMapping parted,
                                                                      int separator) {
        if (counted.equals(parted)) {
            return true;
        }
        if (!counted.equals(CaseMapping.NONE)) {
            return false;
        }
        CodeMap map = CaseMaps.of(parted);
        CodePoints only = CodePoints.of(separator);
        return map.domain().has(separator) && map.preimage(only).equals(only)
                && map.image(only).equals(only);
    }

    /**
     * {@code shown}, which says what every value of each place does where it gets to this
     * relation, along a run that works out {@code past} on the way to it: as it is where every
     * value there is shown to get there, and with the places it shows undivided said not to be
     * shown getting there at every value where the run may stop on what nothing here says on a
     * value this relation reads. What it shows of them is kept, since a value that gets there is
     * left as it says.
     *
     * <p>Not asked of a relation that comes out one way wherever a row gets to it, which divides
     * none of its places whichever values get there. And no line is drawn where a run may stop:
     * that is no line of the model, and where it falls is what nothing here says.
     */
    private WhatItLeaves reachedAlong(WhatItLeaves shown, DemandReading.Answered past,
                                      InputReading read, SearchRegion region,
                                      List<OnAWay> conditions, Optional<Set<String>> declined) {
        return reachedAlong(shown, past, read, region, conditions, declined, Set.of());
    }

    /**
     * The same, where the lengths of the strings at {@code accountedFor} are those some value of
     * the numbers the way ties them to gets the run past, or are parted with the rest left open,
     * so that a run stopped by a tie reading only such places is not one the relation is
     * claimed to be reached despite ({@link #roomOnTheWay}).
     */
    private WhatItLeaves reachedAlong(WhatItLeaves shown, DemandReading.Answered past,
                                      InputReading read, SearchRegion region,
                                      List<OnAWay> conditions, Optional<Set<String>> declined,
                                      Set<TermPath> accountedFor) {
        return mayStopOnWhatItReads(past, read, region, conditions, declined, accountedFor)
                ? shown.mayStopBefore(places()) : shown;
    }

    /**
     * Whether a run working out {@code past} may stop on what nothing here says on a value this
     * relation reads: an operator on what no place holds, after which no number is known to take
     * every value it did, or one tying a place a side reads to others
     * ({@link DemandReading.Answered#tied}), which the region the relation is read over does not
     * hold — or an operator owed a proof that some run gets past it, whatever it reads, that the
     * witness is not shown to get past ({@link Witness}). A side whose places are not known is
     * taken to read any.
     *
     * <p>Or where what the applications of a closure before the one the relation is reached in
     * work out may. Every operator owed is asked of one witness, so that what is shown of each is
     * shown of one row: one where every container those applications walk holds the one element
     * the relation is read at, so that there are none, where such a witness is shown; and
     * otherwise one holding as few as the way and the rules leave, on which the applications
     * before are asked like the rest.
     */
    private boolean mayStopOnWhatItReads(DemandReading.Answered past, InputReading read,
                                         SearchRegion region, List<OnAWay> conditions,
                                         Optional<Set<String>> declined,
                                         Set<TermPath> accountedFor) {
        return getsPastExactlyOn(past, read, region, conditions, declined, false, accountedFor)
                .isEmpty();
    }

    /**
     * The case conversions a run working out {@code past} gets to this relation only past exactly,
     * or nothing where it may stop on something else, or on a conversion this does not say a
     * place for ({@link #mayStopOnWhatItReads}).
     *
     * <p>A conversion of the string at a place a side reads ends a run for the strings whose answer
     * is longer than a {@code String} holds, and for no other ({@link GetsPast.WhereTheTextFits}).
     * The strings the conversion is exactly a map on ({@link CodeMap}) are not among them, so a run
     * gets to the relation at every one of those, and which of the others it stops on is not said.
     * Said of a reader that parts the strings it reads by what it is shown over, which asks for
     * {@code exactlyOnConversions}: it answers the conversions here and shows nothing of the
     * strings they are not exact on. Any other reader takes a conversion of a string it reads as
     * a stop.
     */
    private Optional<List<ConvertedOn>> getsPastExactlyOn(DemandReading.Answered past,
                                                          InputReading read, SearchRegion region,
                                                          List<OnAWay> conditions,
                                                          Optional<Set<String>> declined,
                                                          boolean exactlyOnConversions,
                                                          Set<TermPath> accountedFor) {
        List<ConvertedOn> exact = new ArrayList<>();
        List<ConvertedOn> collecting = exactlyOnConversions ? exact : null;
        if (past.unsaid()) {
            return Optional.empty();
        }
        if (past.tied().isEmpty() && past.owed().isEmpty() && past.before().isEmpty()) {
            return Optional.of(exact);
        }
        List<TermPath> reads = new ArrayList<>();
        amongThemselves.forEach(each -> reads.add(each.path()));
        for (Side side : sides) {
            Optional<List<TermPath>> placesOfTheSide = placesRead(side);
            if (placesOfTheSide.isEmpty()) {
                return Optional.empty();
            }
            reads.addAll(placesOfTheSide.get());
        }
        Witness witness = new Witness(reads, read, region, conditions, declined, Set.of());
        Optional<Set<TermPath>> walked = walkedByTheApplicationsBefore(past, read);
        if (walked.isPresent()) {
            Witness ofOne = new Witness(reads, read, region, conditions, declined, walked.get());
            if (walked.get().stream()
                    .allMatch(each -> ofOne.holds(each).equals(Optional.of(BigInteger.ONE)))) {
                return stopsOn(past, reads, ofOne, false, read, collecting, false, accountedFor)
                        ? Optional.empty() : Optional.of(exact);
            }
        }
        return stopsOn(past, reads, witness, true, read, collecting, false, accountedFor)
                ? Optional.empty() : Optional.of(exact);
    }

    /**
     * Whether every place {@code tie} touches among {@code reads} is one whose lengths are
     * accounted for, so that a run stopped by the tie stops on no value of the relation that is
     * not shown left open.
     *
     * <p>Place by place and not tie by tie: what accounts for a place is a claim made of that
     * place, and a tie that reads another place as well is not met by it.
     */
    static boolean readsOnlyWhatIsAccountedFor(DemandReading.Tie tie, List<TermPath> reads,
                                               Set<TermPath> accountedFor) {
        for (TermPath read : reads) {
            if (touchesAny(tie.places(), List.of(read))
                    && accountedFor.stream().noneMatch(place -> overlap(place, read))) {
                return false;
            }
        }
        return true;
    }

    /**
     * Whether a run working out {@code past} may stop on a value the relation reads, shown of
     * {@code witness} ({@link #mayStopOnWhatItReads}); what the applications before work out is
     * asked as well where {@code applicationsBefore}, and is not where the witness makes none.
     * Where {@code exactOn} is given, a conversion of a string a side reads is not a stop but is
     * added to it; {@code earlier} where {@code past} is what the applications before work out.
     */
    private boolean stopsOn(DemandReading.Answered past, List<TermPath> reads, Witness witness,
                            boolean applicationsBefore, InputReading read,
                            List<ConvertedOn> exactOn, boolean earlier,
                            Set<TermPath> accountedFor) {
        if (past.unsaid()) {
            return true;
        }
        for (DemandReading.Tie tie : past.tied()) {
            if (touchesAny(tie.places(), reads) && !readsOnlyWhatIsAccountedFor(tie, reads,
                    accountedFor)) {
                return true;
            }
        }
        // An owed operator is asked of the witness whatever it reads: one reading no place the
        // relation reads still stops a run on the witness where what it builds there does not
        // fit, and a run stopped there reaches the relation at no value.
        WhereARunReachingARelationStands standing = new WhereARunReachingARelationStands(reads);
        for (Pullback.StopObligation owed : past.owed()) {
            if (owed.completion() instanceof GetsPast.WhereTheTextFits(int operand)) {
                // What a conversion ends a run for turns on the text it is handed. It is let go of
                // only where that text is the string a side reads, whose strings it ends no run
                // for are said, or stands where no run that reaches the relation does. A
                // conversion of any other text ends a run at values nothing here says, whether or
                // not the relation reads a place of it.
                if (owed.onWhatNoPlaceHolds()) {
                    return true;
                }
                ConversionOfAString text = conversionOfAString(owed, operand, read);
                if (text == null) {
                    return true;
                }
                for (TermPath place : text.places()) {
                    if (reads.contains(place)) {
                        // The string a side reads is exactly the string every application
                        // converts only where the place is one value of the row. Under an element
                        // an earlier application converts another element's string, which no
                        // class is drawn over.
                        if (exactOn == null || (earlier
                                && !WhereARunReachingARelationStands.isOneValueOfARow(place))) {
                            return true;
                        }
                        exactOn.add(new ConvertedOn(place, text.conversion()));
                    } else if (standing.mayStandAt(place)) {
                        return true;
                    }
                }
                continue;
            }
            if (!witness.answers(owed)) {
                return true;
            }
        }
        if (applicationsBefore) {
            for (DemandReading.PriorApplications prior : past.before()) {
                // What accounts for a place is a claim about the application the relation is
                // reached in. An earlier application works out the same statements over values of
                // its own, which that claim does not reach. Nor does the exactness of a
                // conversion: the string an earlier application converts is another element's,
                // at a place that reads alike, and it is no string the classes are drawn over.
                if (stopsOn(prior.workedOut(), reads, witness, true, read, exactOn, true,
                        Set.of())) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * The conversions of the string at a place that a run gets past exactly on.
     *
     * @param place      the place of the string the conversions are done to
     * @param conversion what they make of it, outermost last
     */
    private record ConvertedOn(TermPath place, CaseMapping conversion) {}

    /**
     * What {@code owed}, a case conversion of the text at {@code operand}, is done to: the string
     * that stands at one of some places, and what is done to it. Or null where the text is not
     * that — made by anything but case conversions of a string the input holds at a place.
     *
     * <p>The places are found where the text stands, read as the walk that met the obligation read
     * it: a name the text stands in may stand for one of several places, of which the run is on
     * one.
     */
    private static ConversionOfAString conversionOfAString(Pullback.StopObligation owed,
                                                           int operand, InputReading read) {
        List<ValueName> done = new ArrayList<>();
        Core call = Core.withoutStanding(owed.operation());
        Core innermost = call;
        while (AnOperationApplied.of(call) instanceof AnOperationApplied applied
                && applied.operation() instanceof ValueName.Stdlib
                && CaseMapping.isAConversion(applied.operation())
                && applied.args().size() == 1) {
            done.add(applied.operation());
            innermost = call;
            call = Core.withoutStanding(applied.args().get(done.size() == 1 ? operand : 0));
        }
        // How the names of the text are read is recorded where the walk met the conversion handed
        // the text, which is not a node of the text.
        if (done.isEmpty()) {
            return null;
        }
        // Where the text may come from is the places the obligation was read off. A place with
        // another under it only says which string, so the strings are the places with none.
        List<TermPath> places = owed.places().stream()
                .filter(place -> owed.places().stream().noneMatch(
                        other -> !other.equals(place) && other.isAtOrUnder(place)))
                .toList();
        if (places.isEmpty()) {
            return null;
        }
        // And each of them is shown to be the text itself by what the text stands as, and not by
        // where it came from: a value made from a string is not that string ({@link
        // PathResolution.MadeOf}), so a place the text came from is no place of it until the
        // text is followed to the string there.
        InputReads at = owed.readsAt(innermost);
        List<TermPath> shown = at == null ? null : placesStoodAt(call, at,
                read.rules().symbols(), read.rules().newtypes(), Set.of());
        if (shown == null || !new HashSet<>(shown).containsAll(places)) {
            return null;
        }
        CaseMapping conversion = CaseMapping.NONE;
        for (ValueName each : done.reversed()) {
            conversion = CaseMapping.applying(each, conversion);
        }
        return new ConversionOfAString(places, conversion);
    }

    /**
     * The places the value {@code text} is stands at, read in {@code at}, followed through the
     * names it is handed through; or null where it is not shown to be the value at a place — a
     * value an operation makes, or a name nothing says what it stands for.
     *
     * <p>A field read off a name is the field of what the name stands as: the name is followed to
     * the places it stands for and the fields {@link ElementsApart#readOff} says are read off it
     * are put after each. What stops the walk is a name met twice on the way, {@code met}, and
     * not a number of names.
     */
    private static List<TermPath> placesStoodAt(Core text, InputReads at, Symbols symbols,
                                                DeclarationNewtypes newtypes,
                                                Set<BindingId> met) {
        Denotation stands = at.standing(text, symbols, newtypes);
        Core e = Core.withoutStanding(stands.value());
        if (AnOperationApplied.of(e) != null) {
            return null;
        }
        List<TermPath> held = stringsHeldAt(stands.at().pathOf(e, newtypes));
        if (held != null) {
            return held;
        }
        ElementsApart.ReadOff off = ElementsApart.readOff(e, newtypes);
        Set<BindingId> now = new HashSet<>(met);
        if (!(Core.withoutStanding(off.holder()) instanceof Core.Read name)
                || !now.add(name.binding())) {
            return null;
        }
        List<TermPath> holders = switch (stands.at().meaningOf(name, symbols, newtypes)) {
            case ReadMeaning.Position position -> List.of(position.path());
            case ReadMeaning.Through through -> placesStoodAt(through.denotes().value(),
                    through.denotes().at(), symbols, newtypes, now);
            case ReadMeaning.OneOf oneOf -> placesOfEach(
                    oneOf.valuesWhere(ReadMeaning.WhereKept.NOTHING_DECIDED), symbols, newtypes,
                    now);
            default -> null;
        };
        return holders == null || off.path().steps().isEmpty() ? holders
                : holders.stream().map(place -> place.then(off.path().steps())).toList();
    }

    /** The places each of {@code values} stands at, or null where one is not shown to stand at
     *  a place: a name that stands for one of several values stands at the places of each. */
    private static List<TermPath> placesOfEach(List<Denotation> values, Symbols symbols,
                                               DeclarationNewtypes newtypes, Set<BindingId> met) {
        Set<TermPath> every = new LinkedHashSet<>();
        for (Denotation each : values) {
            List<TermPath> there = placesStoodAt(each.value(), each.at(), symbols, newtypes, met);
            if (there == null) {
                return null;
            }
            every.addAll(there);
        }
        return List.copyOf(every);
    }

    /**
     * The places a value stands at, on the run it is on one of them, or null where it stands at
     * none.
     *
     * <p>Where a value stands and where it came from are two answers ({@link
     * PathResolution.MadeOf}): a value made from a string is not that string, so a text a helper
     * built out of a place, or a name stands for the result of, may be longer than the string and
     * is not taken for it.
     */
    private static List<TermPath> stringsHeldAt(PathResolution resolved) {
        return switch (resolved) {
            case PathResolution.At it -> List.of(it.path());
            case PathResolution.MayStandAt it -> it.among();
            default -> null;
        };
    }

    /**
     * A case conversion done to the string that stands at one of {@code places}, of which the run
     * is on one.
     */
    private record ConversionOfAString(List<TermPath> places, CaseMapping conversion) {}

    /**
     * Every container of the input walked by a call applying a closure the relation is reached in,
     * where each such call applies its closure from the first element one after another, so that
     * a witness holding one element in each makes no application before — or empty where one
     * does not, or walks what is at no position of the input and is not shown to hold no more
     * than one element.
     *
     * <p>A container built of what is written alone, such as the one case of a sum a helper
     * picks a list out of, holds one element at most on every run, and no witness need hold it to
     * one: the application the relation is reached in is the only one.
     */
    private static Optional<Set<TermPath>> walkedByTheApplicationsBefore(
            DemandReading.Answered past, InputReading read) {
        Set<TermPath> out = new LinkedHashSet<>();
        for (DemandReading.PriorApplications prior : past.before()) {
            if (prior.walked().isEmpty()) {
                return Optional.empty();
            }
            for (DemandReading.PriorApplications.WalkedOver each : prior.walked().get()) {
                if (each.reads().pathOf(each.container(), read.rules().newtypes())
                        instanceof PathResolution.At(TermPath collection)) {
                    out.add(collection);
                } else if (!ContainerSizesUnderAWitness
                        .mostHeldWhateverTheInputHolds(each.container())
                        .map(most -> most.compareTo(BigInteger.ONE) <= 0).orElse(false)) {
                    return Optional.empty();
                }
            }
        }
        return Optional.of(out);
    }

    /** Whether some place of {@code places} overlaps one of {@code reads}. */
    private static boolean touchesAny(Set<TermPath> places, List<TermPath> reads) {
        for (TermPath place : places) {
            for (TermPath at : reads) {
                if (overlap(place, at)) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * One run standing for every value this relation shows of its places, by how many elements
     * each collection of the input holds on it — of which a run gets past an owed operator where
     * {@link ContainerSizesUnderAWitness} shows it does.
     *
     * <p>A row showing a value here, with a collection cut down to so many, is a row of that value
     * and of the way where each of these holds. The rules leave the collection that many, and
     * nothing of theirs reads inside its elements, which a cut could break
     * ({@link UndividedByARelation#howManyAreHeld}). Nothing the way states, or declined to read,
     * says anything of the
     * collection or of what is in it but how many it holds at least — a statement turning on no
     * position it names may say anything of it; or, where the collection is
     * held to the one element the relation is read at, of what is in that element alone, which
     * the region the relation is read over took in. And each side keeps its value cut down: an
     * element's own value, and an end, kept by copies of the element holding it; a total only
     * where one element is left, since the relation reads a total on the run of one element's
     * value ({@link UndividedByARelation#summedAs}); nothing else made of the collection. And
     * every collection cut on the run is cut alone: no rule relates how many it holds to another
     * collection cut, or to a place the relation reads outside it, so the fewest each is left on
     * its own are left together, and beside the relation's values. Where any of these is not
     * shown, nothing is.
     */
    private final class Witness {

        private final List<TermPath> reads;
        private final InputReading read;
        private final SearchRegion region;
        private final List<OnAWay> conditions;
        private final Optional<Set<String>> declined;
        private final Set<TermPath> heldToOne;
        private final Map<TermPath, Optional<BigInteger>> sizes = new HashMap<>();
        private final Set<TermPath> asked = new LinkedHashSet<>();

        /**
         * @param reads     the places the relation reads
         * @param read      the reading of the input
         * @param region    the region the relation is read over
         * @param conditions what the way states
         * @param declined  the parameters what the way declined may name a position under, or
         *                  empty where it may name any
         * @param heldToOne the collections held to the one element the relation is read at
         */
        Witness(List<TermPath> reads, InputReading read, SearchRegion region,
                List<OnAWay> conditions, Optional<Set<String>> declined,
                Set<TermPath> heldToOne) {
            this.reads = reads;
            this.read = read;
            this.region = region;
            this.conditions = conditions;
            this.declined = declined;
            this.heldToOne = heldToOne;
        }

        /** Whether a run gets past {@code owed} on this witness. */
        boolean answers(Pullback.StopObligation owed) {
            return ContainerSizesUnderAWitness.answersOn(owed.within(), owed.operation(),
                    owed.completion(), node -> {
                        InputReads at = owed.readsAt(node);
                        return at != null && at.pathOf(node, read.rules().newtypes())
                                instanceof PathResolution.At(TermPath path)
                                ? holds(path) : Optional.empty();
                    });
        }

        /** How many elements {@code collection} holds here, or nothing where no such run is
         *  shown. */
        Optional<BigInteger> holds(TermPath collection) {
            return sizes.computeIfAbsent(collection, this::fewest);
        }

        private Optional<BigInteger> fewest(TermPath collection) {
            boolean ofOne = heldToOne.contains(collection);
            if (declined.isEmpty() || declined.get().contains(collection.head())) {
                return Optional.empty();
            }
            // How many it holds is cut alone only where no rule relates it to another value the
            // run stands on here — another collection cut on this run, or a place the relation
            // reads outside it. A place inside it is the side's to keep (keptCutDown).
            for (TermPath other : reads) {
                if (!overlap(other, collection) && tiedByARule(collection, other, read)) {
                    return Optional.empty();
                }
            }
            for (TermPath other : asked) {
                if (!overlap(other, collection) && tiedByARule(collection, other, read)) {
                    return Optional.empty();
                }
            }
            asked.add(collection);
            BigInteger asked = ofOne ? BigInteger.ONE : BigInteger.ZERO;
            for (OnAWay each : conditions) {
                // A statement turning on no position the way names may turn on anything,
                // the collection and what is in it as well.
                if (each.positions().isEmpty()) {
                    return Optional.empty();
                }
                if (each.positions().stream().noneMatch(at -> overlap(at, collection))) {
                    continue;
                }
                if (ofOne && ofTheElementAtHand(each, collection)) {
                    continue;
                }
                // Which case an element is, said of the element and nothing else, asks the
                // collection for the element it is said of.
                if (saysOnlyWhatStandsInside(each, collection)) {
                    asked = asked.max(BigInteger.ONE);
                    continue;
                }
                Optional<BigInteger> least = holdsAtLeast(each, collection, read);
                if (least.isEmpty()) {
                    return Optional.empty();
                }
                asked = asked.max(least.get());
            }
            boolean aTotal = false;
            for (Side side : sides) {
                Optional<List<TermPath>> placesOfTheSide = placesRead(side);
                boolean ofTheCollection = placesOfTheSide.isEmpty() || placesOfTheSide.get()
                        .stream().anyMatch(at -> overlap(at, collection));
                switch (keptCutDown(side)) {
                    case AT_ANY_SIZE -> { }
                    case AT_ONE -> aTotal |= ofTheCollection;
                    case NOT -> {
                        if (ofTheCollection) {
                            return Optional.empty();
                        }
                    }
                }
            }
            BigInteger inside = BigInteger.ZERO;
            for (TermPath at : reads) {
                if (at.equals(collection) || collection.isAtOrUnder(at)) {
                    return Optional.empty();
                }
                if (at.isAtOrUnder(collection)) {
                    inside = BigInteger.ONE;
                }
            }
            inside = inside.max(heldAgainstEachOther(collection));
            NumericDomain.Bounds held = howManyAreHeld(collection, read, region);
            if (held == null || !held.holdsAValue()) {
                return Optional.empty();
            }
            BigInteger fewest = BigInteger.ZERO;
            if (held.min() != null) {
                if (!(held.min().at() instanceof Count least)
                        || !(least.exactly().ceiling() instanceof ExactAnswer.Held<BigInteger>(
                                BigInteger up))) {
                    return Optional.empty();
                }
                fewest = held.min().inclusive() || !least.exactly().isWhole() ? up
                        : up.add(BigInteger.ONE);
            }
            BigInteger witness = fewest.max(asked).max(inside);
            if (held.max() != null) {
                if (!(held.max().at() instanceof Count most)
                        || most.exactly().compareTo(ExactRatio.of(witness)) < 0) {
                    return Optional.empty();
                }
            }
            if ((aTotal || ofOne) && !witness.equals(BigInteger.ONE)) {
                return Optional.empty();
            }
            return Optional.of(witness);
        }
    }

    /**
     * Whether {@code statement} says something of the element at hand in {@code collection} and of
     * nothing else, which the region the relation is read over took in: a relation of positions
     * inside the element, not a statement of what some or every element meets.
     */
    private static boolean ofTheElementAtHand(OnAWay statement, TermPath collection) {
        return statement.elementsOf() == null && statement.relation() != null
                && !statement.whatStands()
                && statement.positions().stream()
                        .allMatch(at -> !at.equals(collection) && at.isAtOrUnder(collection));
    }

    /**
     * Whether {@code statement} says what stands at a value inside {@code collection} and nothing
     * of the values that stand there beside another, such as which case an element is: an element
     * is reached only where the collection holds one, and that is all it asks of how many.
     */
    private static boolean saysOnlyWhatStandsInside(OnAWay statement, TermPath collection) {
        return statement.whatStands() && statement.relation() == null
                && statement.elementsOf() == null
                && statement.positions().stream()
                        .allMatch(at -> !at.equals(collection) && at.isAtOrUnder(collection));
    }

    /** How a side keeps its value where a collection it is made of is cut down. */
    private enum CutDown {
        /** At any number of elements: an element's own value, or an end, kept by copies of the
         *  element holding it. */
        AT_ANY_SIZE,
        /** Only at one element: a total, which the relation reads on one element's run. */
        AT_ONE,
        /** Not shown to keep it. */
        NOT
    }

    /** How {@code side} keeps its value where a collection it is made of is cut down. */
    private static CutDown keptCutDown(Side side) {
        if (side.along() instanceof Quantity.KeptSoFar) {
            return CutDown.AT_ANY_SIZE;
        }
        if (side.along() != null) {
            return CutDown.NOT;
        }
        return switch (side.number()) {
            case NumericTerm.ValueOf _, NumericTerm.ExtremeOfItsKey _ -> CutDown.AT_ANY_SIZE;
            case NumericTerm.TakenOver over ->
                    over.takenAs() instanceof TakenAs.TheSumOfWhatItHolds ? CutDown.AT_ONE
                            : CutDown.NOT;
            case NumericTerm.TakenOf of ->
                    of.takenAs() instanceof TakenAs.TheSumOfWhatItHolds ? CutDown.AT_ONE
                            : CutDown.NOT;
            case NumericTerm.GatheredUnderItsKey filed -> switch (filed.gathering()) {
                case NumericTerm.GatheredUnderItsKey.Gathering.End _ -> CutDown.AT_ANY_SIZE;
                case NumericTerm.GatheredUnderItsKey.Gathering.Total _ -> CutDown.AT_ONE;
                case NumericTerm.GatheredUnderItsKey.Gathering.SinceAPut _ -> CutDown.NOT;
            };
            case null -> CutDown.NOT;
            case NumericTerm.CodePointClassCount _, NumericTerm.CodePointValueSum _,
                 NumericTerm.CodePointAt _, NumericTerm.WholeUnitsOf _, NumericTerm.Multiplicity _,
                 NumericTerm.OccurrencesOfItsValue _, NumericTerm.OccurrencesOfAKey _,
                 NumericTerm.GatheredUnderAKey _ -> CutDown.NOT;
        };
    }

    /**
     * How many elements of {@code collection}, the outermost holding a place whose values this
     * relation holds against each other, those values stand in: one for each side reading the
     * place, and two at least. Nought where it is the outermost holding none.
     */
    private BigInteger heldAgainstEachOther(TermPath collection) {
        BigInteger out = BigInteger.ZERO;
        for (FilingCoordinate each : amongThemselves) {
            if (!each.path().isAtOrUnder(collection)
                    || !each.path().containersHoldingIt().getFirst().equals(collection)) {
                continue;
            }
            long reading = sides.stream().filter(side -> side.madeOf().stream()
                    .anyMatch(place -> place.path().equals(each.path()))).count();
            out = out.max(BigInteger.valueOf(Math.max(2, reading)));
        }
        return out;
    }

    /**
     * The fewest elements {@code statement} asks the collection at {@code collection} to hold,
     * where all it asks is that: a number of them held at least, said of how many it holds and of
     * nothing else. Nothing where it asks anything else of it.
     */
    private static Optional<BigInteger> holdsAtLeast(OnAWay statement, TermPath collection,
                                                     InputReading read) {
        if (!statement.positions().equals(Set.of(collection))
                || !(statement.relation() instanceof TakenConstraint.Affine(var form, var rel))
                || (rel != Rel.GE && rel != Rel.GT) || form.coefs().size() != 1) {
            return Optional.empty();
        }
        RuleReadingSource rules = read.rules();
        Type type = read.domain().typeAt(collection, rules);
        NumericTerm.TakenOf count = type == null ? null
                : NumericTerm.TakenOf.howManyHeldAt(NumericMeasures.takenOf(type, rules.inners()),
                        collection, type, rules.inners(), rules.symbols());
        ExactRatio weight = count == null ? null : form.coefs().get(count);
        if (weight == null || weight.signum() <= 0
                || !(form.constant().negated().dividedBy(weight)
                        instanceof ExactAnswer.Held<ExactRatio>(ExactRatio bound))
                || !(bound.ceiling() instanceof ExactAnswer.Held<BigInteger>(BigInteger up))) {
            return Optional.empty();
        }
        boolean strict = rel == Rel.GT && bound.isWhole();
        return Optional.of((strict ? up.add(BigInteger.ONE) : up).max(BigInteger.ZERO));
    }

    /**
     * The two sides as where an element stands in a walk and how many the walk is over, the first
     * lying from nought to one below the second — or null where they are not those two, or where
     * {@code conditions} say something of what the walk is over.
     *
     * <p>Every position is reached in a row only where nothing on the way picks out some elements:
     * a step that compares where the element stands only for an element above nought compares it
     * at the positions of those. So a statement about the container, a value it is inside or
     * anything inside it leaves the two apart from what this says, but for one stating only how
     * many it holds, which the region already holds of the second side.
     */
    private Within positionWithinItsWalk(List<OnAWay> conditions) {
        if (sides.size() != 2) {
            return null;
        }
        for (int part = 0; part < 2; part++) {
            Quantity.PositionInTheWalk position = sides.get(part).position();
            if (position == null || !position.howMany().equals(sides.get(1 - part).number())) {
                continue;
            }
            TermPath container = position.container();
            return picksOut(conditions, container, Set.of()) ? null
                    : new Within(new WhatARelationLeavesUndivided.WithinTheWhole(part, 1 - part,
                            BigInteger.ZERO, BigInteger.ONE), container, false);
        }
        return null;
    }

    /**
     * A part lying within a whole, read off one container, and whether a row shows an element of
     * it can be written.
     *
     * @param container      the container both are read off
     * @param anElementShown whether a row was shown holding an element of the container, which is
     *                       then known to have a value whatever its type's rules are read to leave
     */
    private record Within(WhatARelationLeavesUndivided.WithinTheWhole within, TermPath container,
                          boolean anElementShown) {}

    /**
     * The two sides as how many elements of a container meet a statement and how many the
     * container holds, the first lying from none to all of the second — or null where they are not
     * those two, or nothing shows every count of them is written.
     *
     * <p>A count of {@code k} beside {@code n} elements is a row only where the statement holds of
     * {@code k} of them and fails of the rest, each beside everything else the row holds. A witness
     * shows one element it holds of and one it fails of beside one value of everything else, at a
     * row that gets to this relation ({@link CountWitnesses}): those two, the first {@code k} times
     * and the second the rest, are a row of every count {@code k} of every {@code n}, where three
     * things hold besides. The container holds an element over again with nothing kept apart,
     * which is how many it holds ({@link #howManyAreHeld}). What the statement reads outside the
     * element is under another parameter than the container, so no rule of a declaration ties the
     * two and the container's elements and count move with the rest as the witness has them. And
     * nothing on the way says anything of the container, but how many it holds, or of what the
     * statement reads outside the element: the way is met at the witness by everything but the
     * container, which is as the witness has it in every one of those rows.
     *
     * <p>Every count of every size, where both an element it holds of and one it fails of are
     * shown. A row of only elements it holds of shows the count at the size and no other, which is
     * not this, and nothing is said of that here.
     *
     * <p>Where the search for a witness stopped short of everything it would have tried, the
     * figures it stopped at go into {@code stopped}: nothing is shown, and a run allowed more may
     * show it.
     */
    private Within countWithinItsContainer(List<OnAWay> conditions,
                                           CountWitnesses.Lookup witnesses,
                                           Set<Figure> stopped) {
        if (sides.size() != 2) {
            return null;
        }
        for (int part = 0; part < 2; part++) {
            Quantity.HowManyMeet counted = sides.get(part).counted();
            if (counted == null
                    || !(counted.container() instanceof DecisionSubject.AnInput(TermPath container))
                    || container.insideAContainer()
                    || !Quantity.PositionInTheWalk.counts(sides.get(1 - part).number(),
                            container)) {
                continue;
            }
            Optional<List<TermPath>> read = PositionsAStatementReads.of(counted.ofTheElement());
            if (read.isEmpty()) {
                return null;
            }
            // What the statement reads is the element's own, or a place under another parameter:
            // the container itself — how many it holds, another of its elements, a value taken of
            // all of them — differs between the rows made of the witness, and so may what the
            // statement says of the same element.
            Set<TermPath> outside = new LinkedHashSet<>();
            for (TermPath place : read.get()) {
                if (place.isAtOrUnder(container.element()) || place.isAtOrUnder(container.key())) {
                    continue;
                }
                if (place.head().equals(container.head())) {
                    return null;
                }
                outside.add(place);
            }
            if (picksOut(conditions, container, outside)) {
                return null;
            }
            CountWitnesses.Sought sought = witnesses.of(counted);
            if (sought.found().isEmpty()) {
                stopped.addAll(sought.stoppedAt());
                return null;
            }
            return new Within(new WhatARelationLeavesUndivided.WithinTheWhole(part, 1 - part,
                    BigInteger.ZERO, BigInteger.ZERO), container, true);
        }
        return null;
    }

    /**
     * Whether {@code conditions} say anything of {@code container} but how many it holds, or
     * anything of {@code besides}: such a way reaches the relation at some of the rows a part read
     * along the container takes, and not at every one.
     */
    private static boolean picksOut(List<OnAWay> conditions, TermPath container,
                                    Set<TermPath> besides) {
        return conditions.stream().anyMatch(each -> each.positions().stream().anyMatch(at ->
                besides.stream().anyMatch(other -> overlap(at, other)))
                || (!(each.whatStands() && each.positions().equals(Set.of(container)))
                        && each.positions().stream().anyMatch(at -> overlap(at, container))));
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
     * {@code conditions} without each statement holding a form unequal to nought where a number
     * of the form is free to meet it ({@link #freeToMeet}).
     *
     * <p>Whatever the rest of the form comes to, it takes one value of that number away and leaves
     * it another, so the statement takes no row away from anything else: a fixed wage held unequal
     * to the one before it, the one before it read nowhere else, leaves the wage every value. What
     * working the statement out asks of a row is a statement of its own on the way
     * ({@link DemandReading#stated}), and stays there. Taken away one at a time, each against the
     * statements still left: a number the next one is free in is chosen after every number in the
     * statements left, which do not read it.
     */
    private List<OnAWay> withoutWhatAFreeNumberMeets(List<OnAWay> conditions,
                                                     Optional<Set<String>> declined,
                                                     DemandReading.Answered past,
                                                     InputReading read) {
        List<OnAWay> out = new ArrayList<>(conditions);
        for (OnAWay each : conditions) {
            TakenConstraint.Affine affine = each.affine();
            if (affine != null && affine.rel() == Rel.NE && affine.form().coefs().keySet()
                    .stream().anyMatch(term ->
                            freeToMeet(term, each, out, declined, past, read))) {
                out.remove(each);
            }
        }
        return out;
    }

    /**
     * Whether {@code term} is a number nothing the way says of the input but {@code statement} may
     * name — no side of the relation reads it ({@link #placesRead}), no other statement of
     * {@code conditions} does, nothing the way declined may ({@code declined}), no operator the
     * source works out on the way ties it to another place ({@code tied}), and no rule of a value
     * around it names it — and which is shown to take two values or more among those the
     * declarations leave and the run narrows it to ({@code past}).
     *
     * <p>What the source works out and not what its form comes to: {@code a + M - M != p} is
     * {@code a != p} as a form and stops at every {@code a} above nought as written, which the way
     * holds as a statement of {@code a} and not of {@code p}.
     */
    private boolean freeToMeet(NumericTerm term, OnAWay statement, List<OnAWay> conditions,
                               Optional<Set<String>> declined, DemandReading.Answered past,
                               InputReading read) {
        if (!(term instanceof NumericTerm.FromOnePosition number)
                || past.unsaidOrOwedOnWhatNoPlaceHolds()) {
            return false;
        }
        for (Side side : sides) {
            Optional<List<TermPath>> reads = placesRead(side);
            if (reads.isEmpty() || reads.get().stream().anyMatch(place ->
                    number.placesReadOff().stream().anyMatch(at -> overlap(place, at)))) {
                return false;
            }
        }
        for (OnAWay other : conditions) {
            if (!other.equals(statement) && touches(number, other.positions())) {
                return false;
            }
        }
        for (Set<TermPath> ties : past.tiedOrOwed()) {
            if (touches(number, ties)) {
                return false;
            }
        }
        if (declined.isEmpty() || number.placesReadOff().stream()
                .anyMatch(at -> declined.get().contains(at.head()))) {
            return false;
        }
        Source source = sourceOf(number, read);
        if (source == null || source.named()) {
            return false;
        }
        // The values it takes are those the run leaves it: a number the run narrows is taken at
        // the values the run lets a row hold, whatever the declarations leave it.
        // Each narrowing is of one number alone, so only those naming this one move its values.
        List<TakenConstraint> ofIt = past.narrowing().stream()
                .filter(each -> each.terms().contains(number)).toList();
        SearchRegion left = read.quantities().region();
        if (!ofIt.isEmpty()) {
            left = TakenConstraint.narrowedBy(ofIt, left);
            if (left.emptiness().isPresent()) {
                return false;
            }
        }
        NumericDomain.Bounds takes = realized(number, source, left,
                ofIt.isEmpty() ? Way.UNTOUCHED : Way.NARROWED);
        return takesTwoValues(takes) && workedOutBeside(statement.affine(), number, takes, read);
    }

    /**
     * Whether {@code statement}'s form is worked out on every row the declarations leave with
     * {@code free} at either of its two whole values nearest nought, of {@code takes}: every other
     * term weighed at the end of its run furthest from nought, added up on each side of nought, and
     * neither sum past the greatest value of the type the form is worked out in.
     *
     * <p>Taking the statement off leaves the rows a way where it may not be worked out, and nothing
     * here says where it is. No sum the source works out of the form — whatever order it adds the
     * terms in, and whichever side of the comparison it writes each on — is further from nought
     * than those, so the statement is worked out wherever the rest stand and the number stands
     * where a row needs it. Not where a term runs open, or the type is not one this knows the
     * greatest value of: {@code a + Date.day(d) != 0} beside an amount up to the greatest
     * {@code Int} is not worked out at the greatest, whichever day.
     *
     * <p>A value held against another value, or against a number, with nothing weighed is compared
     * and not added, and there is nothing to work out.
     */
    private static boolean workedOutBeside(TakenConstraint.Affine statement,
                                           NumericTerm.FromOnePosition free,
                                           NumericDomain.Bounds takes, InputReading read) {
        Collection<ExactRatio> weights = statement.form().coefs().values();
        if (weights.stream().allMatch(each -> each.abs().compareTo(ExactRatio.ONE) == 0)
                && (weights.size() == 1 || (weights.size() == 2
                        && statement.form().constant().signum() == 0
                        && weights.stream().mapToInt(ExactRatio::signum).sum() == 0))) {
            return true;
        }
        Carrier workedOutIn = null;
        for (NumericTerm each : statement.form().coefs().keySet()) {
            TermOrders orders = read.quantities().ordersOf(each);
            if (workedOutIn == null && orders != null) {
                workedOutIn = orders.answered();
            }
        }
        BigInteger greatest = greatestOf(workedOutIn);
        if (greatest == null) {
            return false;
        }
        ExactRatio constant = statement.form().constant();
        ExactRatio up = constant.signum() > 0 ? constant : ExactRatio.ZERO;
        ExactRatio down = constant.signum() < 0 ? constant.negated() : ExactRatio.ZERO;
        for (Map.Entry<NumericTerm, ExactRatio> each : statement.form().coefs().entrySet()) {
            if (each.getKey().equals(free)) {
                continue;
            }
            if (!(read.quantities().region().projectionOf(each.getKey())
                    instanceof NumericDomain.FormProjection.Within(NumericDomain.Bounds run))
                    || !(run.min() != null && run.min().at() instanceof Count least)
                    || !(run.max() != null && run.max().at() instanceof Count most)) {
                return false;
            }
            ExactRatio low = least.exactly().times(each.getValue()).orNull();
            ExactRatio high = most.exactly().times(each.getValue()).orNull();
            if (low == null || high == null) {
                return false;
            }
            ExactRatio furthestUp = low.compareTo(high) > 0 ? low : high;
            ExactRatio furthestDown = low.compareTo(high) > 0 ? high : low;
            up = furthestUp.signum() > 0 ? up.plus(furthestUp).orNull() : up;
            down = furthestDown.signum() < 0 && up != null
                    ? down.plus(furthestDown.negated()).orNull() : down;
            if (up == null || down == null) {
                return false;
            }
        }
        List<BigInteger> standing = twoNearestNought(takes);
        if (standing == null) {
            return false;
        }
        ExactRatio most = ExactRatio.of(greatest);
        for (BigInteger at : standing) {
            ExactRatio weighed = ExactRatio.of(at).times(statement.form().coefs().get(free))
                    .orNull();
            ExactRatio upAt = weighed == null ? null
                    : weighed.signum() > 0 ? up.plus(weighed).orNull() : up;
            ExactRatio downAt = weighed == null ? null
                    : weighed.signum() < 0 ? down.plus(weighed.negated()).orNull() : down;
            if (upAt == null || downAt == null || upAt.compareTo(most) > 0
                    || downAt.compareTo(most) > 0) {
                return false;
            }
        }
        return true;
    }

    /** The whole value of {@code run} nearest nought and the one next nearest beside it, or null
     *  where it holds no two or an end is no number. */
    private static List<BigInteger> twoNearestNought(NumericDomain.Bounds run) {
        BigInteger low = null;
        BigInteger high = null;
        if (run.min() != null) {
            if (!(run.min().at() instanceof Count least)) {
                return null;
            }
            low = run.min().inclusive() ? least.exactly().ceiling().orNull()
                    : least.exactly().floor().map(at -> at.add(BigInteger.ONE)).orNull();
        }
        if (run.max() != null) {
            if (!(run.max().at() instanceof Count most)) {
                return null;
            }
            high = run.max().inclusive() ? most.exactly().floor().orNull()
                    : most.exactly().ceiling().map(at -> at.subtract(BigInteger.ONE)).orNull();
        }
        if ((run.min() != null && low == null) || (run.max() != null && high == null)) {
            return null;
        }
        BigInteger first = low != null && low.signum() > 0 ? low
                : high != null && high.signum() < 0 ? high : BigInteger.ZERO;
        BigInteger up = first.add(BigInteger.ONE);
        BigInteger second = first.signum() < 0 ? first.subtract(BigInteger.ONE)
                : first.signum() > 0 || high == null || up.compareTo(high) <= 0 ? up
                : first.subtract(BigInteger.ONE);
        for (BigInteger at : List.of(first, second)) {
            if ((low != null && at.compareTo(low) < 0) || (high != null && at.compareTo(high) > 0)) {
                return null;
            }
        }
        return List.of(first, second);
    }

    /**
     * What the declarations leave, narrowed by {@code conditions} as a way's region is — or null
     * where one of them narrowed it some way a statement does not carry: a case of a value taken
     * out of its order, or a container held to an element.
     *
     * <p>A way's region is the declarations' with each relation on it taken in, the cases it
     * leaves out and the containers it holds to an element ({@link WayToTheBorder#narrowing}).
     * What else a way states — a statement of a value the body works out, of how many elements
     * meet something, of every element — narrows nothing there, and nothing here.
     */
    private static SearchRegion narrowedBy(List<OnAWay> conditions, InputReading read) {
        if (!narrowsByItsRelationsAlone(conditions)) {
            return null;
        }
        List<TakenConstraint> relations = new ArrayList<>();
        for (OnAWay each : conditions) {
            if (each.relation() != null) {
                relations.add(each.relation());
            }
        }
        return TakenConstraint.narrowedBy(relations, read.quantities().region());
    }

    /** Whether each of {@code conditions} narrows a way's region by its relation or not at all,
     *  so that they say all the region is ({@link #narrowedBy}). */
    private static boolean narrowsByItsRelationsAlone(List<OnAWay> conditions) {
        return conditions.stream().allMatch(each -> each.relation() != null
                || (!each.whatStands() && each.elementsOf() == null));
    }

    /** Whether {@code run} holds two values or more: some value, and its ends not one value. */
    private static boolean takesTwoValues(NumericDomain.Bounds run) {
        return run != null && run.holdsAValue() && run.holdsOneWholeNumber() == null
                && (run.min() == null || run.max() == null
                        || !run.min().at().equals(run.max().at()));
    }

    /**
     * The way as one reading of it takes it.
     *
     * @param along     the region the rows of the way are read in
     * @param declared  what the declarations leave, with what the run got past taken in
     * @param left      what the way states, the parts of a date it leaves alone marked
     * @param stating   what the way states of each side
     * @param narrowing what the run narrows
     */
    private record WayRead(SearchRegion along, SearchRegion declared, LeftToTheCalendar left,
                           List<List<OnAWay>> stating, List<TakenConstraint> narrowing) {

        List<OnAWay> conditions() {
            return left.conditions();
        }
    }

    /**
     * The way as {@code stated} and {@code answered} state it.
     *
     * @param tookAway whether a statement of the way or of what the run narrows has been taken
     *                 away, so that its own region is no longer the one the rows were found in
     */
    private WayRead wayRead(List<OnAWay> stated, DemandReading.Answered answered,
                            boolean tookAway, SearchRegion region, boolean offItsLine,
                            InputReading read, List<Source> sources, boolean heldWhole) {
        // Without a statement taken away, the region is the one its rows were found in; with one,
        // the one the rest of them leave, where the rest can be taken in again.
        SearchRegion rest = tookAway ? narrowedBy(stated, read) : null;
        // And the run is what it got past working out as much without the statement: taking one
        // off the way takes no operator off the run.
        rest = rest == null ? null : TakenConstraint.narrowedBy(answered.narrowing(), rest);
        SearchRegion declared = answered.leaving(read.quantities().region());
        SearchRegion along = offItsLine ? declared : rest != null ? rest : region;
        LeftToTheCalendar left = leavingPartsAlone(stated, read);
        return new WayRead(along, declared, left,
                stating(sources, left.conditions(), heldWhole, read), answered.narrowing());
    }

    /**
     * The statements of the way, and of what the run narrows, that hold the relation's own form to
     * an interval a row at its line is in
     * ({@link WhatStatementsOfOneFormDecide#leavingRoomAroundTheLine}).
     *
     * <p>Such a row puts one side at the line and the others where the declarations leave them,
     * and the statement holds there whatever they are. So which values of a side settle the
     * relation, and which leave it either way, is what it is without the statement: it takes
     * away no row there that the others could have supplied, and makes none the others could not.
     */
    private List<TakenConstraint.Affine> metByARowAtTheLine(List<OnAWay> conditions,
                                                            List<TakenConstraint> narrowing) {
        TakenConstraint.Affine asked = askedAsAStatement();
        if (asked == null) {
            return List.of();
        }
        List<TakenConstraint.Affine> stated = new ArrayList<>();
        for (OnAWay each : conditions) {
            if (each.affine() != null) {
                stated.add(each.affine());
            }
        }
        for (TakenConstraint each : narrowing) {
            if (each instanceof TakenConstraint.Affine affine) {
                stated.add(affine);
            }
        }
        return WhatStatementsOfOneFormDecide.leavingRoomAroundTheLine(stated, asked);
    }

    /**
     * The rules of the declarations that hold the relation's own form to an interval a row can
     * stand anywhere near the line in, and say nothing else
     * ({@link WhatStatementsOfOneFormDecide#leavingRoomAroundTheLine}).
     *
     * <p>Only a clause the declaration publishes as exactly such comparisons
     * ({@link ClauseAffineMeaning.Exact}) is one: a clause that states more besides ties the places
     * it reads by what it states besides. And only for a reading that moves one term while the
     * others stand where they may, as the statements of a way are; a reading that moves two terms
     * together still finds the rule tying them. Worked out for this relation and kept out of what
     * is remembered of the declarations, since which rules a row at this line needs is a question
     * of this line.
     *
     * <p>What the exclusion rests on is three things. A row at
     * the line has the form within a step of the line, where each of the rule's comparisons holds
     * whatever else the row says, so a point of the region without the rule that lies there is a
     * row of the region with it. The run each field has is the one the original reading derived
     * of it with the rule in force ({@link SearchRegion#withoutTheRelationOf}), so the region
     * without the rule never gives a field a value the rule took from it. And nothing else ties
     * the fields: what keeps the bounds of a place from being the whole of what the rules leave it
     * is this rule's relation and nothing else ({@link #certifiedAsideFromTheRelationOf}).
     *
     * <p>That holds only for a rule that satisfies all of: the clause is exactly such
     * comparisons; each of them holds on both sides of the line over the greatest weight; and the
     * rule is applied at the one place of its parameter. A rule that fails one stays in the
     * reading and ties as it did.
     */
    private Roomy rulesLeavingRoomAroundTheLine(InputReading read, Set<TermPath> touched) {
        TakenConstraint.Affine asked = askedAsAStatement();
        if (asked == null) {
            return Roomy.NONE;
        }
        Map<TiedOnTheWay.Rule, ClauseMeaning.Stated> leaving = new LinkedHashMap<>();
        for (Side side : sides) {
            for (FilingCoordinate place : placesAsked(side)) {
                for (Object node : reachedByTheDeclarations(place.path(), read).nodes().ties()) {
                    if (node instanceof TiedOnTheWay.Rule rule && rule.clause() >= 0
                            && !leaving.containsKey(rule)) {
                        leaving.put(rule, leavingRoomAroundTheLine(rule, asked, touched, read));
                    }
                }
            }
        }
        Set<Object> nodes = new LinkedHashSet<>();
        Map<String, Set<RuleRef>> refs = new LinkedHashMap<>();
        Map<String, Set<PartId<RuleRef.Invariant>>> parts = new LinkedHashMap<>();
        leaving.forEach((rule, stated) -> {
            // A rule is put aside by its declaration, at every place the declaration holds at. So
            // it is put aside only if the rule at every place of it this reads is one that leaves
            // room, and no place of it is left to be widened that this does not read.
            if (stated != null && leaving.entrySet().stream().allMatch(other ->
                    !sameClause(other.getKey(), rule) || other.getValue() != null)) {
                nodes.add(rule);
                refs.computeIfAbsent(rule.at().head(), _ -> new LinkedHashSet<>())
                        .add(new RuleRef.Invariant(stated.ref()));
                parts.computeIfAbsent(rule.at().head(), _ -> new LinkedHashSet<>())
                        .addAll(stated.parts().ids());
            }
        });
        return new Roomy(nodes, refs, parts);
    }

    /** Whether {@code one} and {@code other} are the same clause of one declaration, at any
     *  places of a parameter. */
    private static boolean sameClause(TiedOnTheWay.Rule one, TiedOnTheWay.Rule other) {
        return one.at().head().equals(other.at().head()) && one.worn().equals(other.worn())
                && one.clause() == other.clause();
    }

    /**
     * The places of the input a way states something of, or the run narrows: a rule of a
     * declaration put aside leaves them as they are, and no other place that rule holds at is
     * a place they speak of.
     */
    private Set<TermPath> placesTheWayTouches(List<OnAWay> conditions,
                                              DemandReading.Answered past) {
        Set<TermPath> out = new LinkedHashSet<>();
        for (OnAWay each : conditions) {
            out.addAll(each.positions());
            if (each.relation() != null) {
                each.relation().terms().forEach(term -> out.add(term.subjectPath()));
            }
        }
        for (TakenConstraint each : past.narrowing()) {
            each.terms().forEach(term -> out.add(term.subjectPath()));
        }
        return out;
    }

    /**
     * The rules a row at the line of this relation needs nothing of.
     *
     * <p>Each is put aside where it was shown to leave room and nowhere else: a rule of a
     * declaration is a rule of every value of it, so the proof for one place of a parameter is not
     * one for another place of it ({@link #leavingRoomAroundTheLine}) nor for another parameter,
     * and the region is read again without the rule only for the parameters it was shown for.
     *
     * @param rules the tying of the declarations they are, as {@link #tiedByTheDeclarations}
     *              names them
     * @param refs  the same rules as the reading of the bounds names them
     * @param parts every rule each of them was written as, under the parameter it was shown for,
     *              which is what a region is read again without
     */
    private record Roomy(Set<Object> rules, Map<String, Set<RuleRef>> refs,
                         Map<String, Set<PartId<RuleRef.Invariant>>> parts) {

        static final Roomy NONE = new Roomy(Set.of(), Map.of(), Map.of());

        /** The rules put aside for the parameter {@code head}, and for no other. */
        Set<RuleRef> refsOf(String head) {
            return refs.getOrDefault(head, Set.of());
        }
    }

    /** The clause {@code rule} is of where it states exactly comparisons of the form
     *  {@code asked} is of, each holding it on both sides of the line over the greatest weight;
     *  null otherwise. */
    private static ClauseMeaning.Stated leavingRoomAroundTheLine(TiedOnTheWay.Rule rule,
                                                                 TakenConstraint.Affine asked,
                                                                 Set<TermPath> touched,
                                                                 InputReading read) {
        if (!(rule.worn() instanceof TypeSymbol.AtModule name)) {
            return null;
        }
        PublishedRules rules = RulesRead.of(read).byName().computeIfAbsent(name,
                each -> PublishedRules.governing(each, read.rules().published()));
        List<ClauseMeaning> reached = rules.reached();
        if (!rules.everyRuleReached() || rule.clause() >= reached.size()
                || !(reached.get(rule.clause()) instanceof ClauseMeaning.Stated stated)
                || !(stated.affine() instanceof ClauseAffineMeaning.Exact exact)) {
            return null;
        }
        // The one place the rule is applied in its parameter: the region is read again without it
        // by declaration, and a second place it holds at is a place the proof below was not made
        // for.
        for (TermPath other : appliedAt(rule, read)) {
            if (!other.equals(rule.at())
                    && touched.stream().anyMatch(place -> place.isAtOrUnder(other))) {
                return null;
            }
        }
        List<TakenConstraint.Affine> statements = new ArrayList<>();
        for (ClauseAffineMeaning.Comparison each : exact.conjuncts()) {
            Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
            for (Map.Entry<RuleKey, ExactRatio> weighed : each.form().coefs().entrySet()) {
                List<TermPath> places = read.domain().positionsNamed(rule.at(), weighed.getKey());
                if (places.size() != 1) {
                    return null;
                }
                coefs.put(new NumericTerm.ValueOf(places.getFirst()), weighed.getValue());
            }
            statements.add(new TakenConstraint.Affine(
                    new LinearForm<>(each.form().constant(), coefs), each.rel()));
        }
        for (TakenConstraint.Affine each : statements) {
            if (WhatStatementsOfOneFormDecide.leavingRoomAroundTheLine(List.of(each), asked)
                    .isEmpty() && !leavesRoomAsAPartOf(each, asked, read)) {
                return null;
            }
        }
        return stated;
    }

    /**
     * Whether {@code statement}, an order on some of the numbers {@code asked} is a form of, holds
     * of every row near the line of {@code asked}.
     *
     * <p>A row near the line has the form of {@code asked} within the greatest weight of it. The
     * numbers the statement does not name come to no less (or no more) than the ends they have,
     * so what the statement's numbers come to, weighed as {@code asked} weighs them, lies from the
     * line less that greatest weight and less the most the rest comes to, to the line plus that
     * weight and less the least the rest comes to. The statement holds there when it holds at the
     * end it is an order towards: a bound above is met at the top of that range and a bound below
     * at the bottom of it.
     */
    private static boolean leavesRoomAsAPartOf(TakenConstraint.Affine statement,
                                               TakenConstraint.Affine asked, InputReading read) {
        Map<NumericTerm, ExactRatio> whole = asked.form().coefs();
        Map<NumericTerm, ExactRatio> named = new LinkedHashMap<>();
        Map<NumericTerm, ExactRatio> rest = new LinkedHashMap<>();
        whole.forEach((term, weight) ->
                (statement.form().coefs().containsKey(term) ? named : rest).put(term, weight));
        if (rest.isEmpty() || named.size() != statement.form().coefs().size()
                || statement.rel() == Rel.EQ || statement.rel() == Rel.NE
                || !WhatStatementsOfOneFormDecide.outsideEveryContainer(statement)) {
            return false;
        }
        ExactRatio weighs = WhatStatementsOfOneFormDecide.factorBetween(named,
                statement.form().coefs());
        FormRange others = FormRange.of(new LinearForm<>(ExactRatio.ZERO, rest), read);
        ExactRatio reach = whole.values().stream().map(ExactRatio::abs)
                .max(ExactRatio::compareTo).orElse(null);
        if (weighs == null || weighs.signum() <= 0 || others == null || reach == null) {
            return false;
        }
        ExactRatio line = asked.form().constant().negated();
        boolean bounded =statement.rel() == Rel.LE || statement.rel() == Rel.LT;
        ExactRatio end = bounded
                ? line.plus(reach).flatMap(top -> top.minus(others.least())).orNull()
                : line.minus(reach).flatMap(bottom -> bottom.minus(others.greatest())).orNull();
        ExactRatio value = end == null ? null : weighs.times(end)
                .flatMap(scaled -> scaled.plus(statement.form().constant())).orNull();
        return value != null && statement.rel().holds(value.signum());
    }

    /** The relation as a statement is held, the sides weighed and added to the constant and held
     *  against nought, or null where it is not of terms of the input. A term the sides weigh to
     *  nothing is not in the form, as in every form. */
    private TakenConstraint.Affine askedAsAStatement() {
        if (kind != Kind.AFFINE || constant == null || sides.isEmpty()) {
            return null;
        }
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        for (Side each : sides) {
            if (each.statedTerm() == null || each.kept() != null
                    || coefs.merge(each.statedTerm(), each.weight(),
                            (one, other) -> one.plus(other).orNull()) == null) {
                return null;
            }
        }
        coefs.values().removeIf(ExactRatio::isZero);
        return coefs.isEmpty() ? null
                : new TakenConstraint.Affine(new LinearForm<>(constant, coefs), relation);
    }

    /**
     * Whether {@code statement} holds the form {@code asked} is of unequal to nought: the same
     * numbers, each weighed the same times one number, the constant too, held apart from it.
     */
    private static boolean keepsOffTheLineOf(OnAWay statement, TakenConstraint.Affine asked) {
        TakenConstraint.Affine affine = statement.affine();
        if (affine == null || affine.rel() != Rel.NE
                || !affine.form().coefs().keySet().equals(asked.form().coefs().keySet())) {
            return false;
        }
        Map.Entry<NumericTerm, ExactRatio> first =
                asked.form().coefs().entrySet().iterator().next();
        if (!(affine.form().coefs().get(first.getKey()).dividedBy(first.getValue())
                instanceof ExactAnswer.Held<ExactRatio>(ExactRatio times))) {
            return false;
        }
        for (Map.Entry<NumericTerm, ExactRatio> each : asked.form().coefs().entrySet()) {
            if (!(each.getValue().times(times) instanceof ExactAnswer.Held<ExactRatio>(
                    ExactRatio weighed)) || weighed.compareTo(affine.form().coefs()
                            .get(each.getKey())) != 0) {
                return false;
            }
        }
        return asked.form().constant().times(times) instanceof ExactAnswer.Held<ExactRatio>(
                ExactRatio moved) && moved.compareTo(affine.form().constant()) == 0;
    }

    /** The conditions of a way, marked, and the years its statements of years put the dates in,
     *  or null where they leave the months and days to no years. */
    private record LeftToTheCalendar(List<OnAWay> conditions,
                                     WhatStatementsOfDatePartsLeaveAlone.YearsChosen years) {}

    /** The months and the days the sides take of each date, after the move of each. */
    private Map<TermPath, List<DatesThatStandInEveryYear.Part>> monthsAndDaysTheSidesTake() {
        Map<TermPath, List<DatesThatStandInEveryYear.Part>> out = new LinkedHashMap<>();
        for (Side side : sides) {
            if (side.number() instanceof NumericTerm.TakenOf taken
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
            if (side.number() instanceof NumericTerm.TakenOf taken
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
            if (sides.get(i).number() instanceof NumericTerm.TakenOf taken
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
                NumericTerm.TakenOf taken = (NumericTerm.TakenOf) sides.get(i).number();
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

    /**
     * What {@code leaves} says of the side at {@code at}, put where it goes. Values settling it
     * are kept against the side's number, whatever number it is; where the lines between them part
     * no place — the orders' ends alone draw them, or they are lines on a total of a run — the
     * model draws none on the places the side is made of and they are undivided too.
     */
    private void putDown(int at, WhatARelationLeavesUndivided.Leaves leaves,
                        Set<FilingCoordinate> undivided,
                        Map<NumericTerm, WhatARelationLeavesUndivided.Leaves.Settled> settled) {
        switch (leaves) {
            case null -> { }
            case WhatARelationLeavesUndivided.Leaves.Undivided _ ->
                    undivided.addAll(sides.get(at).madeOf());
            case WhatARelationLeavesUndivided.Leaves.Settled runs -> {
                if (sides.get(at).number() != null) {
                    settled.put(sides.get(at).number(), runs);
                }
                if (runs.leavesItsPlacesUndivided(sides.get(at).number())) {
                    undivided.addAll(sides.get(at).madeOf());
                }
            }
        }
    }

    /**
     * Whether {@code leaves} settles the relation one way at every value its term may hold: one
     * run, and no line between it and a value it leaves. Every row then holds the term at one of
     * those values, so the relation comes out that way in every row, as it does where a way decides
     * it, and divides none of its places.
     */
    private static boolean settledAtEveryValue(WhatARelationLeavesUndivided.Leaves leaves) {
        return leaves instanceof WhatARelationLeavesUndivided.Leaves.Settled runs
                && runs.noRowShownComputed().isEmpty() && runs.lines().isEmpty();
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

    /** Where {@code carrier} stops, or null where there is none. */
    private static NumericDomain.Bounds whereItStops(Carrier carrier) {
        return carrier == null ? null : carrier.whereItStops();
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
        return carrier == null ? null : carrier.greatestWholeNumber();
    }

    /** The least whole number {@code carrier} holds, or null where it holds no least or none this
     *  reads as a number. */
    private static BigInteger leastOf(Carrier carrier) {
        return carrier == null ? null : carrier.leastWholeNumber();
    }

    /** Where {@code carrier} stops at either end. */
    private static WhatARelationLeavesUndivided.Ends endsOf(Carrier carrier) {
        return new WhatARelationLeavesUndivided.Ends(leastOf(carrier), greatestOf(carrier));
    }

    /** What the way states of each side, asked once and read by both readings. */
    private List<List<OnAWay>> stating(List<Source> sources, List<OnAWay> conditions,
                                       boolean heldWhole, InputReading read) {
        List<List<OnAWay>> out = new ArrayList<>();
        for (int i = 0; i < sides.size(); i++) {
            Side each = sides.get(i);
            // A value a rule names moves with the places the rule names beside it, so what the
            // way states of any place of its parameter is stated of it.
            // The end of a key's numbers is read off the places its elements stand at, so what the
            // way states of one of them is stated of it.
            List<NumericTerm.FromOnePosition> readOff = !heldWhole ? List.of()
                    : each.readOff() != null ? List.of(each.readOff())
                    : List.copyOf(each.placesOfItsEnd());
            Set<OnAWay> stated = new LinkedHashSet<>();
            for (NumericTerm.FromOnePosition term : readOff) {
                stated.addAll(sources.get(i) != null && sources.get(i).named()
                        ? statingAnythingOfItsParameter(term, conditions, read)
                        : statingAnythingOf(term, conditions));
            }
            out.add(List.copyOf(stated));
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
     * @param narrowedByTheRun what the region took in of the operators the run works out: the
     *                   way states none of it, and a number it names is read over the run the
     *                   region leaves
     */
    private List<WhatARelationLeavesUndivided.Term<FilingCoordinate>> termsAlong(
            InputReading read, List<Source> sources, List<Carrier> carriers, SearchRegion region,
            SearchRegion declared, List<OnAWay> conditions, WholeNumberRuns remainders,
            List<List<OnAWay>> stating, boolean heldWhole,
            List<TakenConstraint> narrowedByTheRun, boolean everyRemainderByTheFormat) {
        List<WhatARelationLeavesUndivided.Term<FilingCoordinate>> terms = new ArrayList<>();
        for (int i = 0; i < sides.size(); i++) {
            Side each = sides.get(i);
            if (remainder != null && i == 0) {
                terms.add(remainderAlong(read, conditions, remainders, heldWhole,
                        everyRemainderByTheFormat));
                continue;
            }
            if (each.kept() != null) {
                terms.add(keptAlong(each, sources.get(i), carriers.get(i), region, read,
                        conditions, stating.get(i), heldWhole));
                continue;
            }
            // Where it lies is asked of the number whatever it is a number of: a total over a run
            // lies where what the values it walks guarantee leave it. What it is shown to take is
            // asked of a position's, and of a total only as the totals of one element
            // (summedOverOneElement): a total of evens lies at nought or more and is never odd.
            NumericDomain.Bounds holds = asARelationReadsIt(each.number() != null
                    && region.projectionOf(each.number())
                    instanceof NumericDomain.FormProjection.Within(NumericDomain.Bounds within)
                    ? within : NumericDomain.Bounds.OPEN, carriers.get(i));
            Way way = each.atOnePosition() == null || !heldWhole ? Way.TIES
                    : wayOf(each.atOnePosition(), stating.get(i));
            if (way == Way.UNTOUCHED && narrowedByTheRun.stream().anyMatch(past ->
                    past.terms().stream().anyMatch(term -> term.equals(each.atOnePosition())))) {
                way = Way.NARROWED;
            }
            // A rule the bounds do not state narrows the term as a statement of the way does.
            if (way == Way.UNTOUCHED && sources.get(i) != null && sources.get(i).relaxed()) {
                way = Way.NARROWED;
            }
            Source source = way == Way.TIES ? null : sources.get(i);            // A statement shown to leave a part alone is taken into the region, which then does not
            // answer for that part: it is answered by what the declarations leave it.
            SearchRegion answering = way == Way.UNTOUCHED && conditions.stream()
                    .anyMatch(statement -> statement.leavesAlone(each.atOnePosition()))
                    ? declared : region;
            NumericDomain.Bounds realizes = source != null
                    ? asARelationReadsIt(realized(each.atOnePosition(), source, answering, way),
                            carriers.get(i))
                    : each.number() instanceof NumericTerm.TakenOver over
                    ? asARelationReadsIt(summedOverOneElement(over, read, region, conditions,
                            heldWhole, carriers.get(i)), carriers.get(i))
                    : each.number() instanceof NumericTerm.OccurrencesOfItsValue counted
                    ? asARelationReadsIt(occurrencesOfOneValue(counted, read, region, conditions,
                            heldWhole), carriers.get(i))
                    : each.number() instanceof NumericTerm.CodePointAt at
                    ? asARelationReadsIt(codePointsTakenAt(at, read, stating.get(i)),
                            carriers.get(i))
                    : isAnEndOfAKey(each.number())
                    ? asARelationReadsIt(shownOfAnEnd(each.number(), read, region, conditions,
                            heldWhole), carriers.get(i))
                    : null;
            Takes takes = source != null && way == Way.UNTOUCHED
                    && each.number() instanceof NumericTerm.ValueOf ? source.takes() : null;
            terms.add(new WhatARelationLeavesUndivided.Term<>(each.madeOf(), each.weight(), holds,
                    realizes, takes, each.number() instanceof NumericTerm.ValueOf,
                    spacingOf(carriers.get(i)), whereItStops(carriers.get(i)), each.number()));
        }
        return terms;
    }

    /**
     * The remainder side as a term: it lies between nought and one below the divisor, or among the
     * remainders the way leaves it, and takes every one of those where its form is shown to reach
     * one of each.
     *
     * <p>What it takes is said only where the remainders left are one run: a term takes the
     * values between its ends, and two runs apart are values between that it does not take.
     */
    private WhatARelationLeavesUndivided.Term<FilingCoordinate> remainderAlong(
            InputReading read, List<OnAWay> conditions, WholeNumberRuns remainders,
            boolean heldWhole, boolean everyRemainderByTheFormat) {
        WholeNumberRuns left = WholeNumberRuns.one(BigInteger.ZERO,
                remainder.divisor().subtract(BigInteger.ONE));
        if (remainders != null) {
            left = left.and(remainders);
        }
        List<WholeNumberRuns.Run> runsOf = left.runs();
        NumericDomain.Bounds runs = new NumericDomain.Bounds(
                Endpoint.inclusive(new Count(new BigDecimal(runsOf.getFirst().from()))),
                Endpoint.inclusive(new Count(new BigDecimal(runsOf.getLast().to()))));
        Side side = sides.getFirst();
        return new WhatARelationLeavesUndivided.Term<>(side.madeOf(), side.weight(), runs,
                runsOf.size() == 1 && (everyRemainderByTheFormat
                        || reachesEveryRemainder(null, read, conditions, heldWhole))
                        ? runs : null, null, false, Granularity.DISCRETE, null);
    }

    /**
     * Whether the form the remainder is of is shown to leave every remainder, whatever the other
     * numbers of the form are put at — apart from {@code held}, a number of it that is put at one
     * value and so reaches none.
     *
     * <p>Shown by one number of the form, the witness, put at each of the values from nought to
     * one below the divisor with every other number of the form at nought. Each of those is a
     * row's values, and the remainders they leave are every remainder, when:
     * <ul>
     *   <li>the witness takes every whole number of its type, nothing in the declarations or on
     *   the way relates it to anything, and no other number of the form is read off a place it is;
     *   <li>its weight is prime to the divisor, so the divisor's worth of consecutive values leave
     *   each remainder once;
     *   <li>its type holds those values, and every other number of the form is of the same
     *   description and holds nought, so that putting it there is no value the declarations
     *   refuse; and
     *   <li>the form comes to a number the type holds at each of them — the weight times the
     *   greatest of those values lying within the type's ends — since a run that overflows is no
     *   row, and a remainder only an overflowing value leaves is not one a row has.
     * </ul>
     * Every number of the form is a whole number, since a form of other numbers leaves no
     * remainder where it comes to none. {@code held} is a number of the form left out of the
     * others: it stands at whatever value is asked of it, and which of its values have a row is
     * asked of the row.
     */
    private boolean reachesEveryRemainder(NumericTerm held, InputReading read,
                                          List<OnAWay> conditions, boolean heldWhole) {
        if (!heldWhole) {
            return false;
        }
        for (NumericTerm term : remainder.dividend().coefs().keySet()) {
            TermOrders orders = read.quantities().ordersOf(term);
            if (orders == null || !(orders.answered() instanceof Carrier.Whole)) {
                return false;
            }
        }
        for (Map.Entry<NumericTerm, ExactRatio> each : remainder.dividend().coefs().entrySet()) {
            if (each.getKey().equals(held)
                    || !(each.getKey() instanceof NumericTerm.ValueOf value)
                    || !(each.getValue().floor() instanceof ExactAnswer.Held<BigInteger>(
                            BigInteger weight))
                    || !weight.abs().gcd(remainder.divisor()).equals(BigInteger.ONE)) {
                continue;
            }
            Source source = sourceOf(value, read);
            if (source == null || !source.takes().every() || source.named()
                    || wayOf(value, statingAnythingOf(value, conditions)) != Way.UNTOUCHED
                    || sharesAPlaceWithAnotherNumberOfTheForm(value)) {
                continue;
            }
            Carrier carrier = read.quantities().ordersOf(value).answered();
            BigInteger window = remainder.divisor().subtract(BigInteger.ONE);
            if (holdsFromNoughtTo(carrier, window) && theFormIsComputedAtEachOf(weight, window,
                    carrier) && theOthersCanBeLeftAtNought(value, held, read, conditions)) {
                return true;
            }
        }
        return false;
    }

    /** Whether the values of {@code carrier} include every whole number from nought to
     *  {@code top}, an end it has none of being no end. */
    private static boolean holdsFromNoughtTo(Carrier carrier, BigInteger top) {
        BigInteger least = leastOf(carrier);
        BigInteger greatest = greatestOf(carrier);
        return (least == null || least.signum() <= 0)
                && (greatest == null || greatest.compareTo(top) >= 0);
    }

    /**
     * Whether the form, with the witness weighed by {@code weight} at any value from nought to
     * {@code top} and every other number at nought, comes to a number {@code carrier} holds.
     *
     * <p>In the type's own arithmetic, which stops the run where it overflows. The most it comes
     * to either way is the weight times {@code top}; every sum the run takes along the way is a
     * part of that, the numbers it is added to being nought. A type with no end overflows
     * nowhere.
     *
     * <p>The number the form is moved by is not part of this: the quantity holds it taken by the
     * divisor, as every reader of this remainder does, so what the run adds is not what the
     * quantity knows. Where the run adds more than the type has room for, the values it computes
     * are a window of the others', and which of them have a row is asked of the row.
     */
    private boolean theFormIsComputedAtEachOf(BigInteger weight, BigInteger top,
                                              Carrier carrier) {
        BigInteger most = weight.abs().multiply(top);
        BigInteger least = leastOf(carrier);
        BigInteger greatest = greatestOf(carrier);
        return (greatest == null || most.compareTo(greatest) <= 0)
                && (least == null || most.negate().compareTo(least) >= 0);
    }

    /**
     * The form the remainder is of, where it is made of code points of one string whose strings
     * the rules leave as a format's of one length — or null.
     *
     * <p>Read so that what the form leaves is worked out over the strings themselves
     * ({@link Language#remaindersLeft}), and nothing takes the indices apart: a format whose code
     * points go together — {@code (00|11)} — leaves what its strings leave and no more. Only where
     * the format is the whole of what the rules leave the string, no rule of a value around it
     * reads it, and nothing on the way states anything of a code point of the form beside the
     * remainder: each of those is something else holding the strings back.
     *
     * @param strings what the rules leave the string
     * @param weights what the form weighs the code point at each index by, taken by the divisor
     * @param beside  the indices of the code points of the string another side is
     */
    private record CodePointsOfTheForm(Quantities.StringsOfOneLength strings,
                                       Map<Integer, Long> weights, List<Integer> beside) {

        private CodePointsOfTheForm {
            weights = Map.copyOf(weights);
            beside = List.copyOf(beside);
        }
    }

    /** The form the remainder is of read as code points of {@code string}
     *  ({@link CodePointsOfTheForm}) — or null. */
    private CodePointsOfTheForm codePointsOfTheForm(TermPath string, InputReading read,
                                                    List<OnAWay> conditions) {
        Quantities.StringsOfOneLength strings = theStringsOf(string, read);
        if (strings == null) {
            return null;
        }
        // A way past which every string of the format still stands holds none of them back.
        List<OnAWay> holdingBack = conditions.stream()
                .filter(each -> !heldByEveryStringOf(each, string, strings.length())).toList();
        Map<Integer, Long> weights = new LinkedHashMap<>();
        for (Map.Entry<NumericTerm, ExactRatio> each : remainder.dividend().coefs().entrySet()) {
            if (!(each.getKey() instanceof NumericTerm.CodePointAt at)
                    || !string.equals(at.position())
                    || !(each.getValue().floor() instanceof ExactAnswer.Held<BigInteger>(
                            BigInteger weight))
                    || wayOf(at, statingAnythingOf(at, holdingBack)) != Way.UNTOUCHED) {
                return null;
            }
            weights.put(at.index(), weight.mod(remainder.divisor()).longValueExact());
        }
        List<Integer> beside = new ArrayList<>();
        for (Side side : sides.subList(1, sides.size())) {
            if (side.number() instanceof NumericTerm.CodePointAt at
                    && at.position().equals(string)) {
                beside.add(at.index());
            }
        }
        return new CodePointsOfTheForm(strings, weights, beside);
    }

    /**
     * Whether {@code each} states nothing of {@code string} but how many code points it holds,
     * and holds of a string of {@code length} code points.
     */
    private static boolean heldByEveryStringOf(OnAWay each, TermPath string, int length) {
        if (!(each.relation() instanceof TakenConstraint.Affine(var form, var rel))) {
            return false;
        }
        ExactRatio at = form.constant();
        for (Map.Entry<NumericTerm, ExactRatio> term : form.coefs().entrySet()) {
            if (!(term.getKey() instanceof NumericTerm.TakenOf taken)
                    || !taken.position().equals(string)
                    || !(taken.takenAs() instanceof TakenAs.HowManyItHolds)
                    || !(term.getValue().times(ExactRatio.of(length))
                            instanceof ExactAnswer.Held<ExactRatio>(ExactRatio weighed))
                    || !(at.plus(weighed) instanceof ExactAnswer.Held<ExactRatio>(
                            ExactRatio added))) {
                return false;
            }
            at = added;
        }
        return rel.holds(at.signum());
    }

    /**
     * Whether {@code form} leaves every remainder whatever the code points the other sides are,
     * and whatever the one at {@code held} is where that is an index of the form — each of
     * {@code work} remainders moved at most.
     *
     * <p>Each of those code points is held at each set of the code points that stand alike at its
     * index ({@link Language#alikeAt}) in turn, and the form is asked with the one at {@code held}
     * weighed by nought: every value of the set moves each remainder the rest leaves by one same
     * amount, so where the rest leaves every remainder, so does each of them.
     *
     * <p>Where the walks would move more remainders than {@code work}, it is not shown, and the
     * figure the work is allowed under goes into {@code stopped}.
     */
    private boolean leavesEveryRemainder(CodePointsOfTheForm form, Integer held, int work,
                                         Set<Figure> stopped) {
        Quantities.StringsOfOneLength strings = form.strings();
        StringsHeldAsWritten shown = strings.everyOneHeld();
        if (shown == null) {
            return false;
        }
        int divisor = remainder.divisor().intValueExact();
        Map<Integer, Long> weights = new LinkedHashMap<>(form.weights());
        List<Integer> fixed = new ArrayList<>(form.beside());
        if (held != null) {
            weights.remove(held);
            fixed.add(held);
        }
        // Whatever a code point held still is, of every one a value may hold at its index; and
        // a remainder reached, by a string that is a value. So every code point some value may
        // hold there is one a string shown to be a value holds there too.
        List<List<CodePoints>> alike = new ArrayList<>();
        long sets = 1;
        for (int index : fixed) {
            CodePoints taken = shown.codePointsAt(strings.length(), index);
            if (!strings.holding().codePointsAt(strings.length(), index).less(taken).isEmpty()) {
                return false;
            }
            alike.add(shown.alikeAt(strings.length(), index, taken));
            sets *= alike.getLast().size();
            if (sets > work) {
                stopped.add(CompositionBudget.STEPS_A_SEARCH_MAY_TAKE.figure());
                return false;
            }
        }
        int each = (int) (work / sets);
        int[] chosen = new int[fixed.size()];
        while (true) {
            Map<Integer, CodePoints> at = new LinkedHashMap<>();
            for (int i = 0; i < fixed.size(); i++) {
                at.put(fixed.get(i), alike.get(i).get(chosen[i]));
            }
            BitSet left = shown.remaindersLeft(strings.length(), weights,
                    remainder.shift().mod(remainder.divisor()).longValueExact(), divisor, at,
                    each);
            if (left == null) {
                stopped.add(CompositionBudget.STEPS_A_SEARCH_MAY_TAKE.figure());
                return false;
            }
            if (left.cardinality() < divisor) {
                return false;
            }
            int next = 0;
            while (next < chosen.length && ++chosen[next] == alike.get(next).size()) {
                chosen[next++] = 0;
            }
            if (next == chosen.length) {
                return true;
            }
        }
    }

    /**
     * What the format shows of the remainder and the places of its form, where the form is made of
     * code points of one string ({@link #codePointsOfTheForm}): whether the form leaves every
     * remainder whatever the code points of the string the other sides are, and the places of the
     * form that leave it so whatever their own code point is. Null where the form is no such
     * form or it does not leave every remainder.
     *
     * <p>One budget for every question asked of the strings, shared out among them; a question
     * the share runs out on is not shown, and the figure goes into {@code stopped}.
     */
    private Set<FilingCoordinate> leftByTheFormat(InputReading read, List<OnAWay> conditions,
                                                  Set<Figure> stopped) {
        if (remainder == null || !(remainder.dividend().coefs().keySet().iterator().next()
                instanceof NumericTerm.CodePointAt first)) {
            return null;
        }
        // A layer of the walk holds a remainder or not for each of the divisor's, so a divisor
        // past the work is a walk past it.
        int steps = CompositionBudget.STEPS_A_SEARCH_MAY_TAKE.maximum();
        if (remainder.divisor().compareTo(BigInteger.valueOf(steps)) > 0) {
            stopped.add(CompositionBudget.STEPS_A_SEARCH_MAY_TAKE.figure());
            return null;
        }
        CodePointsOfTheForm form = codePointsOfTheForm(first.position(), read, conditions);
        if (form == null) {
            return null;
        }
        int work = steps / (1 + remainder.dividend().coefs().size());
        if (!leavesEveryRemainder(form, null, work, stopped)) {
            return null;
        }
        Set<FilingCoordinate> out = new LinkedHashSet<>();
        for (NumericTerm each : remainder.dividend().coefs().keySet()) {
            if (each instanceof NumericTerm.CodePointAt at
                    && leavesEveryRemainder(form, at.index(), work, stopped)) {
                out.add(FilingCoordinate.of(each));
            }
        }
        return out;
    }

    /**
     * Whether the sides at {@code one} and {@code other} are the remainder and a code point of the
     * string its form is of, which the format shows apart where the form is such a form
     * ({@link #leftByTheFormat}).
     */
    private boolean apartByTheFormat(int one, int other) {
        int beside = one == 0 ? other : other == 0 ? one : -1;
        return remainder != null && beside > 0
                && sides.get(beside).number() instanceof NumericTerm.CodePointAt at
                && atTheStringOfTheForm(at);
    }

    /**
     * Whether {@code one} and {@code other} are a code point of the remainder's form and one at
     * another index of its string that the form holds no weight for, which the format shows apart
     * where the form is such a form ({@link #leftByTheFormat}).
     */
    private boolean apartByTheFormat(FilingCoordinate one, FilingCoordinate other) {
        if (remainder == null
                || !(one instanceof FilingCoordinate.OfTerm(NumericTerm.CodePointAt first))
                || !(other instanceof FilingCoordinate.OfTerm(NumericTerm.CodePointAt second))
                || first.index() == second.index()) {
            return false;
        }
        boolean firstOfTheForm = remainder.dividend().coefs().containsKey(first);
        boolean secondOfTheForm = remainder.dividend().coefs().containsKey(second);
        return firstOfTheForm != secondOfTheForm && atTheStringOfTheForm(first)
                && atTheStringOfTheForm(second);
    }

    /** Whether {@code at} is a code point of the string the remainder's form is made of code
     *  points of. */
    private boolean atTheStringOfTheForm(NumericTerm.CodePointAt at) {
        return remainder.dividend().coefs().keySet().stream().allMatch(each ->
                each instanceof NumericTerm.CodePointAt of && of.position().equals(at.position()));
    }

    /**
     * The strings at {@code string}, where they are a format's strings of one length and no rule
     * of a value around them reads them — or null. Which of them are shown to be values is the
     * reading's to say ({@link Quantities.StringsOfOneLength#everyOneHeld}).
     */
    private static Quantities.StringsOfOneLength theStringsOf(TermPath string,
                                                              InputReading read) {
        return namedByTheDeclarations(string, read) == Named.UNSEEN
                ? null : read.quantities().stringsOfOneLength(string);
    }

    /**
     * Every value the code point {@code at} is shown to take whatever the others of the relation
     * are: the code points standing at its index of the strings the rules leave, where those are
     * one run, it is the one number of its string among the other sides, and nothing of
     * {@code stating}, what the way states of it, holds a string of the format back. That the
     * remainder beside it is not held back by it is the remainder's to show
     * ({@link #leftByTheFormat}).
     */
    private NumericDomain.Bounds codePointsTakenAt(NumericTerm.CodePointAt at, InputReading read,
                                                   List<OnAWay> stating) {
        long ofTheString = sides.stream().filter(side -> side.number() != null
                && side.number().sharesAPlaceWith(new NumericTerm.ValueOf(at.position())))
                .count();
        Quantities.StringsOfOneLength strings = ofTheString == 1
                ? theStringsOf(at.position(), read) : null;
        if (strings == null || strings.everyOneHeld() == null
                || wayOf(at, stating.stream().filter(each ->
                        !heldByEveryStringOf(each, at.position(), strings.length())).toList())
                != Way.UNTOUCHED) {
            return null;
        }
        // Taken is what a string shown to be a value holds there, and not what the format places
        // there: a format places code points in sequences no value is.
        List<CodePoints.Range> runs = strings.everyOneHeld()
                .codePointsAt(strings.length(), at.index()).ranges();
        return runs.size() != 1 ? null : new NumericDomain.Bounds(
                Endpoint.inclusive(Count.of(runs.getFirst().from())),
                Endpoint.inclusive(Count.of(runs.getFirst().to())));
    }

    /**
     * Whether every number of the form other than the witness and {@code held} can stand at
     * nought, whatever else is put: each takes every whole number of its type, holds nought, is
     * related to nothing by the declarations or the way, and is read off a place no other number
     * of the form is. A number read off a place another is moves with it, so nought for one is not
     * nought for the other.
     */
    private boolean theOthersCanBeLeftAtNought(NumericTerm witness, NumericTerm held,
                                               InputReading read, List<OnAWay> conditions) {
        for (NumericTerm each : remainder.dividend().coefs().keySet()) {
            if (each.equals(witness) || each.equals(held)) {
                continue;
            }
            if (!(each instanceof NumericTerm.ValueOf value)
                    || sharesAPlaceWithAnotherNumberOfTheForm(each)) {
                return false;
            }
            Source source = sourceOf(value, read);
            if (source == null || !source.takes().every() || source.named()
                    || wayOf(value, statingAnythingOf(value, conditions)) != Way.UNTOUCHED
                    || !holdsFromNoughtTo(read.quantities().ordersOf(value).answered(),
                            BigInteger.ZERO)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Whether another number of the form the remainder is of is read off a place {@code term} is,
     * or one around it or under it.
     *
     * <p>Such a number moves with {@code term}: {@code x + Int.floorMod(x, 3)} is a function of
     * {@code x} alone, and moving {@code x} through every value moves the other with it, so the
     * form is not taken through a whole turn of the divisor by {@code x} however its weight leaves
     * the remainders. Two numbers are apart only when no place of one is a place of the other, and
     * two different numbers are not that for being different.
     */
    private boolean sharesAPlaceWithAnotherNumberOfTheForm(NumericTerm term) {
        for (NumericTerm other : remainder.dividend().coefs().keySet()) {
            if (!other.equals(term) && term.sharesAPlaceWith(other)) {
                return true;
            }
        }
        return false;
    }

    /** The places of the form the remainder is of that the relation is shown to leave undivided
     *  where the remainder is: those whose value leaves the rest of the form every remainder. */
    private Set<FilingCoordinate> placesOfTheFormLeftEveryRemainder(
            InputReading read, List<OnAWay> conditions, boolean heldWhole) {
        Set<FilingCoordinate> out = new LinkedHashSet<>();
        for (NumericTerm term : remainder.dividend().coefs().keySet()) {
            if (reachesEveryRemainder(term, read, conditions, heldWhole)) {
                out.add(FilingCoordinate.of(term));
            }
        }
        return out;
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
                    NumericDomain.Bounds.OPEN, null, null, false, spacingOf(carrier),
                    whereItStops(carrier));
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
                false, spacingOf(carrier), whereItStops(carrier));
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
                                ? statingAnythingOfItsParameter(number, conditions, read)
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
        return apartByTheDeclarations(one, other, sources, read, Set.of());
    }

    /** The same, without the rules in {@code ignoring} ({@link #rulesLeavingRoomAroundTheLine}). */
    private boolean apartByTheDeclarations(int one, int other, List<Source> sources,
                                           InputReading read, Set<Object> ignoring) {
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
                if (overlap(each, that)
                        || tiedByARule(each.path(), that.path(), read, ignoring)) {
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
     * <p>Each side is the value at a position the declarations leave every value of its type, or a
     * number taken of one whose operation declares that its ends are where the representation
     * stops ({@code Date.year}) and that every answer it can give has a source value. So nothing
     * of them ties it and none is unread. What the way holds of either is taken only as a
     * form over the two weighed one way and the other. A statement about either that is anything
     * else — an end on one of them alone, a form with a third number in it — leaves nothing shown,
     * since it may keep a side from values of its own.
     */
    private Set<FilingCoordinate> undividedByTheDifference(List<Source> sources,
                                                         List<Carrier> carriers,
                                                         List<List<OnAWay>> stating,
                                                         boolean heldWhole, InputReading read,
                                                         SearchRegion region,
                                                         WhatARelationLeavesUndivided.Independence
                                                                 independent,
                                                         WhatARelationLeavesUndivided.Operations
                                                                 operations,
                                                         boolean sizesAreRowsComputed) {
        TwoSides pair = heldWhole ? twoSidesStandingApart(sources, carriers, stating, region,
                independent) : null;
        if (pair == null || !apartByTheDeclarations(pair.first(), pair.second(), sources, read)) {
            return Set.of();
        }
        Carrier on = carriers.get(pair.first());
        List<WhatARelationLeavesUndivided.Term<FilingCoordinate>> terms = new ArrayList<>();
        for (int i : List.of(pair.first(), pair.second())) {
            Side each = sides.get(i);
            Source source = sources.get(i);
            boolean anEnd = !each.placesOfItsEnd().isEmpty();
            if ((each.atOnePosition() == null && !anEnd) || source == null
                    || !source.takes().every()
                    || (anEnd
                    && shownOfAnEnd(each.number(), read, region, stating.get(i), true) == null)) {
                return Set.of();
            }
            // An end is shown every value the carrier holds: that is what the places it is taken
            // of leave it, and what {@link #shownOfAnEnd} asked.
            NumericDomain.Bounds realizes = anEnd ? on.asARelationReadsIt()
                    : switch (each.atOnePosition()) {
                        case NumericTerm.ValueOf _ -> on.asARelationReadsIt();
                        case NumericTerm.TakenOf taken -> DefaultBoundOperationFacts.get()
                                .endsAreWhereTheRepresentationStops(taken.operation())
                                ? realized(taken, source, region, Way.TIES) : null;
                        default -> null;
                    };
            if (realizes == null) {
                return Set.of();
            }
            terms.add(new WhatARelationLeavesUndivided.Term<>(each.madeOf(), each.weight(),
                    on.asARelationReadsIt(), realizes, source.takes(),
                    each.number() instanceof NumericTerm.ValueOf
                            || each.number() instanceof NumericTerm.ExtremeOfItsKey
                            || each.number() instanceof NumericTerm.GatheredUnderItsKey,
                    on.spacingBetweenValues(), on.whereItStops(), each.number()));
        }
        List<WhatARelationLeavesUndivided.OnTheDifference> held = heldOfTheDifference(pair,
                stating);
        if (held == null) {
            return Set.of();
        }
        // Values taken of a place stop where the operation does, short of the type, and an
        // operation is given only when that is where the representation stops.
        NumericDomain.Bounds run = sides.get(pair.first()).number() instanceof NumericTerm.TakenOf
                ? terms.get(0).realizes()
                : on.whereItStops();
        return WhatARelationLeavesUndivided.ofTheirDifference(terms, pair.beside(), relation, held,
                new WhatARelationLeavesUndivided.WhereTheRepresentationStops(run),
                UndividedByARelation::overlap, greatestOf(on), operations, sizesAreRowsComputed);
    }

    /**
     * What the relation leaves each of two sides, in the order of the sides, where it and
     * everything a way states of the two is about how far apart they are and each is the value at
     * a position the declarations leave a run of its type
     * ({@link WhatARelationLeavesUndivided#leavesByTheirDifference}) — each null where nothing is
     * shown, and none where they are not two such sides.
     *
     * <p>What each side takes is asked of the way's region: the way's statements are the
     * differences, which the region holds the two to together and each alone to nothing narrower
     * than they imply, and whatever else the way states, of other places, is a row's to hold as
     * well — so a way no row takes inside where the types stop leaves each side no run
     * ({@link SearchRegion#wholeRunOf}).
     */
    private List<WhatARelationLeavesUndivided.Leaves> leftByTheirDifference(
            List<Source> sources, List<Carrier> carriers, List<List<OnAWay>> stating,
            boolean heldWhole, InputReading read, SearchRegion along,
            WhatARelationLeavesUndivided.Independence independent,
            WhatARelationLeavesUndivided.Operations operations, boolean sizesAreRowsComputed) {
        TwoSides pair = heldWhole ? twoSidesStandingApart(sources, carriers, stating, along,
                independent) : null;
        if (pair == null || !apartByTheDeclarations(pair.first(), pair.second(), sources, read)) {
            return List.of();
        }
        Carrier on = carriers.get(pair.first());
        List<WhatARelationLeavesUndivided.Term<FilingCoordinate>> terms = new ArrayList<>();
        for (int i : List.of(pair.first(), pair.second())) {
            Side each = sides.get(i);
            Source source = sources.get(i);
            if (!(each.atOnePosition() instanceof NumericTerm.ValueOf value) || source == null) {
                return List.of();
            }
            NumericDomain.Bounds realizes = asARelationReadsIt(
                    realized(value, source, along, Way.UNTOUCHED), on);
            NumericDomain.Bounds holds = asARelationReadsIt(along.projectionOf(value)
                    instanceof NumericDomain.FormProjection.Within(NumericDomain.Bounds within)
                    ? within : NumericDomain.Bounds.OPEN, on);
            if (realizes == null) {
                return List.of();
            }
            terms.add(new WhatARelationLeavesUndivided.Term<>(each.madeOf(), each.weight(), holds,
                    realizes, null, true, on.spacingBetweenValues(), on.whereItStops(),
                    each.number()));
        }
        List<WhatARelationLeavesUndivided.OnTheDifference> held = heldOfTheDifference(pair,
                stating);
        if (held == null) {
            return List.of();
        }
        // In the order of the sides, nothing for one held still beside the two.
        List<WhatARelationLeavesUndivided.Leaves> out = new ArrayList<>();
        for (int at = 0; at < sides.size(); at++) {
            out.add(null);
        }
        out.set(pair.first(), WhatARelationLeavesUndivided.leavesByTheirDifference(terms, 0,
                pair.beside(), relation, held, UndividedByARelation::overlap, greatestOf(on),
                operations, pair.standing(), sizesAreRowsComputed));
        out.set(pair.second(), WhatARelationLeavesUndivided.leavesByTheirDifference(terms, 1,
                pair.beside(), relation, held, UndividedByARelation::overlap, greatestOf(on),
                operations, pair.standing(), sizesAreRowsComputed));
        return out;
    }

    /**
     * The two sides a difference is asked of, and what they are held against.
     *
     * @param first    the first side's place in the relation's sides
     * @param second   the second side's
     * @param beside   the addends the two are held against, each apart: the relation's constant,
     *                 and with a third side held still, that side's weighed value at the value it
     *                 is held at. Null where the relation's constant is no number.
     * @param standing the value the third side is held at, before it is weighed, by the number
     *                 the operations call it; none with no third side
     */
    private record TwoSides(int first, int second, WhatARelationLeavesUndivided.Beside beside,
                            Map<Object, ExactRatio> standing) {}

    /**
     * The two sides that stand apart by a difference, where the relation is over two sides of one
     * carrier, or over those and one number besides that stands apart from both.
     *
     * <p>A third side is held at one value it takes and the relation asked of the two as it then
     * stands. The rows with that side at that value are rows of the model, so a value of either of
     * the two that is left either way among them is left either way. It is held only where it is
     * the value at a position the declarations leave a run of whole numbers, the way says nothing
     * of it, and nothing ties it to either of the two. A value near nought is the one held: it
     * keeps the constant, and so the sizes the arithmetic is asked at, near where they were.
     *
     * @return null where there are not two such sides
     */
    private TwoSides twoSidesStandingApart(
            List<Source> sources, List<Carrier> carriers, List<List<OnAWay>> stating,
            SearchRegion region, WhatARelationLeavesUndivided.Independence independent) {
        if (sides.size() == 2) {
            return carriers.get(0) != null && carriers.get(0).equals(carriers.get(1))
                    ? new TwoSides(0, 1, constant == null ? null
                            : WhatARelationLeavesUndivided.Beside.just(constant), Map.of()) : null;
        }
        if (sides.size() != 3 || kind != Kind.AFFINE || remainder != null) {
            return null;
        }
        for (int held = 0; held < 3; held++) {
            int first = held == 0 ? 1 : 0;
            int second = held == 2 ? 1 : 2;
            if (carriers.get(first) == null || !carriers.get(first).equals(carriers.get(second))
                    || carriers.get(held) == null
                    || !(sides.get(held).number() instanceof NumericTerm.ValueOf value)
                    || sources.get(held) == null || !stating.get(held).isEmpty()
                    || !independent.between(first, held) || !independent.between(second, held)
                    || overlapping(sides.get(first), sides.get(held))
                    || overlapping(sides.get(second), sides.get(held))) {
                continue;
            }
            NumericDomain.Bounds run = realized(value, sources.get(held), region, Way.TIES);
            ExactRatio at = run == null || !run.holdsAValue() ? null
                    : run.aValueNearestNought(carriers.get(held).spacingBetweenValues());
            ExactRatio weighed = at == null || (carriers.get(held).spacingBetweenValues()
                    == Granularity.DISCRETE && !at.isWhole()) ? null
                    : at.times(sides.get(held).weight()).orNull();
            if (weighed != null && constant != null) {
                return new TwoSides(first, second,
                        new WhatARelationLeavesUndivided.Beside(List.of(constant, weighed)),
                        Map.of(value, at));
            }
        }
        return null;
    }

    /** Everything a way states of each of the two sides {@code pair} asks about, held of them as
     *  statements about their difference — or null where something it holds is not. A statement
     *  about both sides is in each side's list; it is one statement. */
    private List<WhatARelationLeavesUndivided.OnTheDifference> heldOfTheDifference(
            TwoSides pair, List<List<OnAWay>> stating) {
        Set<OnAWay> aboutEither = new LinkedHashSet<>(stating.get(pair.first()));
        aboutEither.addAll(stating.get(pair.second()));
        List<WhatARelationLeavesUndivided.OnTheDifference> held = new ArrayList<>();
        for (OnAWay each : aboutEither) {
            WhatARelationLeavesUndivided.OnTheDifference statement = each.affine() == null ? null
                    : onTheDifference(each.affine().form(), each.affine().rel(), pair);
            if (statement == null) {
                return null;
            }
            held.add(statement);
        }
        return held;
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
     *
     * <p>A place of the parameter moves the term only where it is the term's own place, or a rule
     * of the declarations relates the two ({@link #tiedByARule}): a rule that reads the term alone
     * holds it beside nothing, so a statement about a place no rule reads with it says nothing of
     * the values it takes.
     */
    private static List<OnAWay> statingAnythingOfItsParameter(NumericTerm.FromOnePosition term,
                                                              List<OnAWay> conditions,
                                                              InputReading read) {
        List<OnAWay> out = new ArrayList<>();
        for (OnAWay each : conditions) {
            if (movesWithAPlaceOfItsParameter(term, each, read)
                    && !saysNothingOfTheValuesOf(term, each, true)) {
                out.add(each);
            }
        }
        return out;
    }

    /** Whether {@code statement} is about a place in a parameter {@code term} is read off that is
     *  the term's own, or one a rule of the declarations relates to a place the term is read off. */
    private static boolean movesWithAPlaceOfItsParameter(NumericTerm.FromOnePosition term,
                                                         OnAWay statement, InputReading read) {
        for (TermPath at : statement.positions()) {
            for (TermPath place : term.placesReadOff()) {
                if (place.head().equals(at.head())
                        && (overlap(place, at) || tiedByARule(place, at, read))) {
                    return true;
                }
            }
        }
        return false;
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
     * two sides, or about their sum where the relation weighs them alike — or null where it is
     * over anything else, or weighs them other than the relation does.
     */
    private WhatARelationLeavesUndivided.OnTheDifference onTheDifference(
            LinearForm<NumericTerm> form, Rel rel, TwoSides pair) {
        Side one = sides.get(pair.first());
        Side other = sides.get(pair.second());
        ExactRatio first = form.coefs().get(one.statedTerm());
        ExactRatio second = form.coefs().get(other.statedTerm());
        if (form.coefs().size() != 2 || first == null || second == null) {
            return null;
        }
        // A statement is about the combination the relation is about: a sum is not a difference.
        boolean asked = one.weight().equals(other.weight());
        boolean alike = first.equals(second);
        boolean opposed = first.plus(second) instanceof ExactAnswer.Held<ExactRatio>(
                ExactRatio sum) && sum.signum() == 0;
        if (asked ? !alike : !opposed) {
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
     * numbers it does not tie, so it is not this. A form over the term alone held off a value is:
     * the region answers the run whole only where its rules prove the hole outside it
     * ({@link NumericDomain#projectionCertification}), as a divisor kept above nought and off
     * nought runs from one. Keeping it off another number is not.
     */
    private static boolean inTheRegion(NumericTerm.FromOnePosition term, OnAWay statement) {
        Set<NumericTerm> over = switch (statement.relation()) {
            case null -> Set.of();
            case TakenConstraint.Affine affine -> affine.rel() != Rel.NE
                    || affine.form().coefs().size() == 1 ? affine.form().coefs().keySet()
                    : Set.of();
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
                               List<Source> sources, InputReading read, Set<Object> ignoring) {
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
                for (Object node : tiedByTheDeclarations(place.path(), read, ignoring)) {
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
        static TiedOnTheWay ofTheDeclarations(String head, InputReading read,
                                              Set<Object> ignoring) {
            TiedOnTheWay out = new TiedOnTheWay();
            for (Position each : read.domain().positions()) {
                if (!each.path().head().equals(head)) {
                    continue;
                }
                Object first = null;
                for (Object node : reachedByTheDeclarations(each.path(), read).nodes().reads()) {
                    if (ignoring.contains(node)) {
                        continue;
                    }
                    if (first == null) {
                        first = node;
                    } else {
                        out.join(first, node);
                    }
                }
            }
            return out;
        }

        static TiedOnTheWay of(List<OnAWay> conditions, InputReading read, Set<Object> ignoring) {
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
                        for (Object node : tiedByTheDeclarations(at, read, ignoring)) {
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
            // Every step of the answer's order has a value of the position's order in it, so the
            // steps the value falls in fill the answer's run wherever the value takes every value
            // its type holds.
            case NumericTerm.WholeUnitsOf units -> every
                    ? way == Way.UNTOUCHED ? NumericDomain.Bounds.OPEN : region.wholeRunOf(units)
                    : null;
            case NumericTerm.CodePointClassCount _, NumericTerm.CodePointValueSum _,
                 NumericTerm.CodePointAt _ -> null;
        };
    }

    /**
     * The value at the element a total over one container's elements is counted as, or null
     * where {@code number} is no such total. A sum answers what its elements are
     * ({@link TakenAs.TheSumOfWhatItHolds}), so it is counted on the order they are.
     */
    private static NumericTerm.FromOnePosition summedAs(NumericTerm number) {
        if (!(number instanceof NumericTerm.TakenOver over)
                || !(over.takenAs() instanceof TakenAs.TheSumOfWhatItHolds)) {
            return null;
        }
        List<NumericTerm.ValueOf> values = valuesOfOneElement(over);
        return values.isEmpty() ? null : values.getFirst();
    }

    /**
     * The value one element of the run {@code over} sums comes to, at each place it may stand: the
     * place itself for a run of a field, and for a run of what a {@code match} on the element
     * answers, the field each case answers. Empty where it is any other run, or a {@code match}
     * that answers something other than a field of the case it took, or leaves a case to a rest.
     */
    private static List<NumericTerm.ValueOf> valuesOfOneElement(NumericTerm.TakenOver over) {
        return switch (over.source()) {
            case RunSource.ProjectedOccurrences _ ->
                    List.of(new NumericTerm.ValueOf(over.subjectPath()));
            case RunSource.ComputedOccurrences computed
                    when computed.computation() instanceof ElementValue.OfItsCase choice
                    && choice.rest() == null -> {
                List<NumericTerm.ValueOf> out = new ArrayList<>();
                for (ElementValue.OfItsCase.Arm arm : choice.arms()) {
                    ElementProjection place = arm.value().asAPlace();
                    if (place == null) {
                        yield List.of();
                    }
                    out.add(new NumericTerm.ValueOf(place.from(computed.elements())));
                }
                yield out;
            }
            default -> List.of();
        };
    }

    /** Starting from nought and adding, which is the accumulation a sum declares. */
    private static final Accumulation SUMMED =
            new Accumulation(Accumulation.Identity.ZERO, Accumulation.Combine.ADD);

    /**
     * A run every value of which the total {@code over} is shown to take — or null where none is
     * shown: what the element's number is shown to take, and nought beside it where the container
     * may hold nothing and no value lies between.
     *
     * <p>Read off the accumulation the operation declares, and not off its name: starting from
     * nought and adding, a container of one element comes to that element's number, and one of
     * none comes to nought. So every value the number at the element is shown to take is a total,
     * where the container may hold one element and that element may stand at the value alone.
     * What the element is shown to take is a run some row holds it at with every rule read
     * ({@link #realized}), and a rule over the elements together or around the container leaves
     * it nothing shown; so the one element is a row's, and nothing the way states may touch it.
     * Which totals a container of two reaches is not asked, so this is a run only where one
     * element is.
     *
     * <p>That nought is a total is one value, and joins the run only where the run starts just
     * past it; between the two, nothing is shown.
     */
    private static NumericDomain.Bounds summedOverOneElement(NumericTerm.TakenOver over,
                                                             InputReading read,
                                                             SearchRegion region,
                                                             List<OnAWay> conditions,
                                                             boolean heldWhole, Carrier carrier) {
        List<NumericTerm.ValueOf> elements = valuesOfOneElement(over);
        if (!heldWhole || carrier == null || elements.isEmpty()
                || !SUMMED.equals(DefaultBoundOperationFacts.get().accumulation(over.operation()))) {
            return null;
        }
        List<TermPath> containers = over.subjectPath().containersHoldingIt();
        if (containers.size() != 1) {
            return null;
        }
        return shownOfAnElementAlone(elements, containers.getFirst(), read, region, conditions,
                carrier);
    }

    /**
     * A run every value of which one element is shown to take at whichever of {@code places} its
     * case puts it, where {@code container} may hold one element — or null where none is shown.
     *
     * <p>One element comes to the value at whichever place its case puts it, so a value is taken
     * where the element may stand at it at each of them: the runs of the places are one run only
     * where they are alike. What each is shown to take is a run some row holds it at with every
     * rule read ({@link #realized}), and a way touching it, or a rule over the elements together,
     * leaves nothing shown.
     *
     * @param nought the carrier of a total, which is nought where the container may hold nothing;
     *               null for a number that is one of the elements'
     */
    private static NumericDomain.Bounds shownOfAnElementAlone(
            List<? extends NumericTerm.FromOnePosition> places, TermPath container,
                                                              InputReading read,
                                                              SearchRegion region,
                                                              List<OnAWay> conditions,
                                                              Carrier nought) {
        NumericDomain.Bounds each = null;
        for (NumericTerm.FromOnePosition element : places) {
            Source source = sourceOf(element, read);
            if (source == null
                    || wayOf(element, statingAnythingOf(element, conditions)) != Way.UNTOUCHED) {
                return null;
            }
            NumericDomain.Bounds here = realized(element, source, region, Way.UNTOUCHED);
            if (here == null || (each != null && !each.equals(here))) {
                return null;
            }
            each = here;
        }
        NumericDomain.Bounds held = howManyAreHeld(container, read, region);
        if (each == null || !each.holdsAValue() || held == null || !held.admits(Count.of(1))) {
            return null;
        }
        return nought != null && held.admits(Count.ZERO) ? withNought(each, nought) : each;
    }

    /** Whether {@code number} is an end of the numbers of the elements of one key. */
    private static boolean isAnEndOfAKey(NumericTerm number) {
        return number instanceof NumericTerm.ExtremeOfItsKey
                || (number instanceof NumericTerm.GatheredUnderItsKey gathered
                && gathered.gathering() instanceof NumericTerm.GatheredUnderItsKey.Gathering.End);
    }

    /**
     * A run every value of which the end {@code end} of a key's numbers is shown to take — or null
     * where none is shown: what the number of an element is shown to take, where the container may
     * hold one element.
     *
     * <p>The end of the numbers of one key is, for a container holding one element, that
     * element's number, whichever key it holds, and at whichever place its case puts it. So every
     * value the element is shown to take is an end. Which ends a container of several reaches is
     * not asked.
     */
    private static NumericDomain.Bounds shownOfAnEnd(NumericTerm end, InputReading read,
                                                     SearchRegion region, List<OnAWay> conditions,
                                                     boolean heldWhole) {
        List<PlaceOfAnEnd> places = placesOfEnd(end);
        if (end instanceof NumericTerm.GatheredUnderItsKey gathered && gathered.selection() != null
                && !aLoneElementMeetsTheSelectionBeside(gathered.selection(), places, read)) {
            return null;
        }
        List<NumericTerm.FromOnePosition> measures = new ArrayList<>();
        for (PlaceOfAnEnd each : places) {
            NumericTerm.FromOnePosition measured = each.measure(read);
            if (measured == null) {
                return null;
            }
            measures.add(measured);
        }
        List<TermPath> containers = places.isEmpty() ? List.of()
                : places.getFirst().place().containersHoldingIt();
        return !heldWhole || containers.size() != 1 ? null
                : shownOfAnElementAlone(measures, containers.getFirst(), read, region, conditions,
                        null);
    }

    /**
     * Where one element has the number {@code end} is an end of, at each of the places its case
     * puts it — empty where {@code end} is the end of a selection of the elements that is more than
     * which cases they are in, or of anything but places. Whether one element is kept by such a
     * selection beside the place is asked where the end is shown reached
     * ({@link #aLoneElementMeetsTheSelectionBeside}).
     */
    private static List<PlaceOfAnEnd> placesOfOneElement(NumericTerm end) {
        return end instanceof NumericTerm.GatheredUnderItsKey gathered && gathered.selection() != null
                && gathered.selection().casesAsked().isEmpty() ? List.of() : placesOfEnd(end);
    }

    /**
     * Whether the one element of a container is kept by {@code selection} wherever it stands at
     * one of {@code places} — so that the end over the kept elements is that element's number.
     *
     * <p>True only where the selection is which cases positions of the element are in
     * ({@link KeptOccurrences#casesAsked}), and the element can be written in some way of meeting
     * it: every case of the way holds a value. Beside that, no place of the end sits at or under a
     * position the selection reads, and no rule of a value those positions sit in names one: the
     * element is then written at the cases the selection asks and at the number the end is asked
     * at, the one choice leaving the other free. A selection on a number, or one reading the
     * element as a whole, is not shown to be met together with the end.
     *
     * <p>Which way a row is written in is the composer's, against what else the row asks of the
     * same positions ({@code TermRealizations}); a place of the end never asks a case at a
     * position the selection reads, since it would sit under it.
     */
    private static boolean aLoneElementMeetsTheSelectionBeside(KeptOccurrences selection,
                                                               List<PlaceOfAnEnd> places,
                                                               InputReading read) {
        KeptOccurrences.CasesAsked asked = selection.casesAsked().orElse(null);
        if (places.isEmpty() || asked == null) {
            return false;
        }
        for (TermPath subject : asked.positions()) {
            if (namedDownTo(subject, subject.steps().size(), read, null) != Named.NOT) {
                return false;
            }
            for (PlaceOfAnEnd each : places) {
                TermPath place = each.place().position();
                if (place.isAtOrUnder(subject) || subject.isAtOrUnder(place)) {
                    return false;
                }
            }
        }
        return asked.ways().stream().anyMatch(way -> everyCaseHoldsAValue(way, places, read));
    }

    /**
     * Whether one element can stand at each of {@code places} and meet the statement in {@code way}
     * — the cases the way asks stand beside the cases each place is in — and the rules, every one
     * read, leave a value at every case the way asks of a position. A case they refuse holds none,
     * and one they were not read to the end of may hold none either: only an admission is a value
     * that can be written.
     */
    private static boolean everyCaseHoldsAValue(Requirements way, List<PlaceOfAnEnd> places,
                                                InputReading read) {
        for (PlaceOfAnEnd place : places) {
            if (!(way.merge(place.place().requirements()) instanceof Requirements.Merge.Merged)) {
                return false;
            }
        }
        for (Map.Entry<TermPath, CasesLeft> each : way.refinements().entrySet()) {
            for (PlaceOfAnEnd place : places) {
                if (!admittedBeside(each.getKey(), each.getValue(), place.place().requirements(),
                        read)) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * Whether the rules, every one read, leave a value at {@code cases} of the sum at {@code at},
     * in an element as {@code element} asks it to be. A name the cases of the element share
     * stands at one position under each of them, and the element is as one of those asks.
     */
    private static boolean admittedBeside(TermPath at, CasesLeft cases, Requirements element,
                                          InputReading read) {
        Position there = read.domain().at(at.position());
        if (there != null) {
            return admits(there, cases, read);
        }
        if (!(read.domain().reach().standingOf(at)
                instanceof NameReach.Standing.UnderTheCases(
                        List<NameReach.CaseStanding> standings))) {
            return false;
        }
        boolean any = false;
        for (NameReach.CaseStanding standing : standings) {
            if (element.merge(standing.assuming()) instanceof Requirements.Merge.Merged) {
                Position under = read.domain().at(standing.position().position());
                if (under == null || !admits(under, cases, read)) {
                    return false;
                }
                any = true;
            }
        }
        return any;
    }

    /**
     * Whether the rules of the position leave every one of {@code cases} a value, and each case a
     * sum has is one its declaration is shown to leave a value of: a position admits the case, and
     * only the declaration says whether anything can be made of it.
     */
    private static boolean admits(Position there, CasesLeft cases, InputReading read) {
        for (Refinement narrowing : cases.atoms()) {
            if (!(there.admissionOf(narrowing) instanceof Admits.Admitted)
                    || (narrowing instanceof Refinement.SumCase sum
                            && !aValueIsShownToExist(Type.ref(sum.leaf()), read))) {
                return false;
            }
        }
        return true;
    }

    private static List<PlaceOfAnEnd> placesOfEnd(NumericTerm end) {
        if (end instanceof NumericTerm.ExtremeOfItsKey extreme) {
            // The end of the steps the values fall in is the end of one element's steps, which is
            // the number of its value that counts them.
            return List.of(new PlaceOfAnEnd(extreme.value(), extreme.through(), extreme.steps()));
        }
        if (!(end instanceof NumericTerm.GatheredUnderItsKey gathered)
                || !(gathered.gathering() instanceof NumericTerm.GatheredUnderItsKey.Gathering.End)) {
            return List.of();
        }
        return switch (gathered.value()) {
            case ElementValue.OfItsCase choice when choice.rest() == null -> {
                List<PlaceOfAnEnd> out = new ArrayList<>();
                for (ElementValue.OfItsCase.Arm arm : choice.arms()) {
                    ElementProjection place = arm.value().asAPlace();
                    ElementValue.StepsOfAPlace steps = place == null
                            ? ElementValue.asTheStepsOfAPlace(arm.value()) : null;
                    if (steps != null && steps.weight().equals(ExactRatio.ONE)
                            && steps.constant().isZero()) {
                        // The steps one place of the arm falls in are a number of that place.
                        out.add(new PlaceOfAnEnd(steps.place().from(gathered.elements()),
                                steps.operation(), null));
                    } else if (place != null) {
                        out.add(new PlaceOfAnEnd(place.from(gathered.elements()), null, null));
                    } else {
                        yield List.of();
                    }
                }
                yield out;
            }
            default -> gathered.valuesTakenFrom() == null ? List.of()
                    : List.of(new PlaceOfAnEnd(gathered.valuesTakenFrom().position(), null, null));
        };
    }

    /**
     * A run every value of which how many times the value at an element occurs among the values
     * of {@code counted}'s run is shown to take — or null where none is shown.
     *
     * <p>Built from one element repeated. Where every container inside the list may hold one
     * element, some row holds an element of the list whose containers each hold one, the
     * innermost holding some value: that element is a row's, so every rule inside it holds. A list
     * holding it over again is a run in which that value occurs as many times as the list holds
     * elements. So every count the list may hold from one on is a count of the value, where
     * elements alike break nothing: no rule of a value around the list reads inside its elements
     * — a rule keeping them apart by an id would need as many ids as elements — and nothing the
     * way states touches them. A set holds an element once, so a set outermost holds no element
     * over again and shows nothing.
     */
    private static NumericDomain.Bounds occurrencesOfOneValue(
            NumericTerm.OccurrencesOfItsValue counted, InputReading read, SearchRegion region,
            List<OnAWay> conditions, boolean heldWhole) {
        TermPath at = counted.subjectPath();
        List<TermPath> containers = at.containersHoldingIt();
        if (!heldWhole || counted.selection() != null || containers.isEmpty()) {
            return null;
        }
        TermPath list = containers.getFirst();
        NumericTerm.ValueOf element = new NumericTerm.ValueOf(list.element());
        if (!read.domain().holdsAnElementOverAgain(list, read.rules())
                || namedDownTo(list.element(), list.steps().size(), read, null) != Named.NOT
                || wayOf(element, statingAnythingOf(element, conditions)) != Way.UNTOUCHED) {
            return null;
        }
        for (TermPath inside : containers.subList(1, containers.size())) {
            NumericDomain.Bounds held = howManyAreHeld(inside, read, region);
            if (held == null || !held.admits(Count.of(1))) {
                return null;
            }
        }
        NumericDomain.Bounds held = howManyAreHeld(list, read, region);
        NumericDomain.Bounds fromOne = held == null ? null : held.meet(
                new NumericDomain.Bounds(Endpoint.inclusive(Count.of(1)), null));
        return fromOne != null && fromOne.holdsAValue() ? fromOne : null;
    }

    /**
     * A run of how many {@code container} holds, every value of which some row in {@code region}
     * takes — or null where that is not shown.
     *
     * <p>What the region answers is what the rules on the numbers leave the count, and a count is
     * a row only where that many elements can be written together. Two things no number says hold
     * that back. A rule of a value around the container may read inside its elements — every
     * element one, and no two alike, leave a list of one at most — so where one does, nothing is
     * shown at all. A rule the clause cannot be true without, that only holds the elements apart
     * from one another, is the exception: a list of one meets it, so the run is taken at one
     * element at most, as a set's is. That is a list that is a witness, and not a bound on how
     * many such a container may hold. A rule reading the container for how many it holds is a
     * rule on the count, which the region holds. And the rules of the element's own type may
     * leave it no value, so past nought the run is taken only where a value of the element is
     * shown to exist ({@link #aValueIsShownToExist}). A map's entry is a key as well as a value, and both are
     * asked each of these. Then a list of so many copies of one such value is a row
     * at every count the region leaves. A set, or the keys of a map, holds a value once, and how
     * many different values the element has is not asked here, so past one nothing is shown of
     * those.
     */
    static NumericDomain.Bounds howManyAreHeld(TermPath container, InputReading read,
                                               SearchRegion region) {
        return howManyAreHeld(container, read, region, false);
    }

    /**
     * The same, where {@code anElementShown} says a row the boundary built holds an element of the
     * container: the entry then has a value, whatever its type's rules are read to leave it, and
     * the rest is asked as it is everywhere.
     */
    static NumericDomain.Bounds howManyAreHeld(TermPath container, InputReading read,
                                               SearchRegion region, boolean anElementShown) {
        RuleReadingSource rules = read.rules();
        Type type = read.domain().typeAt(container, rules);
        List<TermPath> entry = read.domain().entryOf(container, rules);
        KeptApart apart = new KeptApart();
        for (TermPath part : entry) {
            if (namedDownTo(part, container.steps().size(), read, null, apart) != Named.NOT) {
                return null;
            }
        }
        NumericTerm.TakenOf count = type == null ? null
                : NumericTerm.TakenOf.howManyHeldAt(NumericMeasures.takenOf(type, rules.inners()),
                        container, type, rules.inners(), rules.symbols());
        NumericDomain.Bounds run = count == null ? null : region.wholeRunOf(count);
        if (run == null) {
            return null;
        }
        int most;
        if (!anElementShown && !entry.stream().allMatch(part ->
                aValueIsShownToExist(read.domain().typeAt(part, rules), read))) {
            most = 0;
        } else if (apart.found || !read.domain().holdsAnElementOverAgain(container, rules)) {
            most = 1;
        } else {
            return run;
        }
        NumericDomain.Bounds upTo = run.meet(new NumericDomain.Bounds(null,
                Endpoint.inclusive(Count.of(most))));
        return upTo.holdsAValue() ? upTo : null;
    }

    /**
     * Whether some value of {@code type} is shown to exist: one no rule of its own is written on —
     * a number, a string, a time, a container, which may hold nothing, an option, which may be
     * none — or a declaration whose rules are shown to leave it one
     * ({@link FieldDomains#shownToHoldAValue}), the name it is written under and the record it
     * names alike. A sum, a tuple, or anything else, is not asked and shows nothing.
     */
    private static boolean aValueIsShownToExist(Type type, InputReading read) {
        if (type == null) {
            return false;
        }
        RuleReadingSource rules = read.rules();
        if (TypeOps.outermost(type, rules.inners()) instanceof TypeOps.Unwrapped worn
                && worn.layer().named() instanceof TypeSymbol.AtModule name
                && !FieldDomains.of(name, read.ruleReading()).shownToHoldAValue()) {
            return false;
        }
        return switch (TypeView.shapeOf(type, rules.inners(), rules.symbols(), rules.kinds(),
                rules.sums())) {
            case Shape.Scalar _, Shape.Unit _, Shape.Sequence _, Shape.Mapping _,
                 Shape.Optional _ -> true;
            case Shape.Product(TypeSymbol.AtModule record, var _) ->
                    FieldDomains.of(record, read.ruleReading()).shownToHoldAValue();
            // A sum holds a value where a case of it does and nothing of its own rules the value
            // out: the case is a value of the sum.
            case Shape.Sum(var _, SumCases.Cases reaches, var _) ->
                    reaches.cases().stream().anyMatch(each ->
                            each instanceof TypeSymbol.AtModule member
                            && aValueIsShownToExist(Type.ref(member), read));
            case null, default -> false;
        };
    }

    /** {@code run} with nought, where nought is in it or it starts just past nought on
     *  {@code carrier} — and {@code run} alone otherwise. */
    private static NumericDomain.Bounds withNought(NumericDomain.Bounds run, Carrier carrier) {
        Endpoint least = run.min();
        if (run.admits(ExactRatio.ZERO) || least == null || !(least.at() instanceof Count from)) {
            return run;
        }
        ExactRatio at = from.exactly();
        boolean justPast = (at.isZero() && !least.inclusive())
                || (carrier.spacingBetweenValues() == Granularity.DISCRETE
                        && at.equals(ExactRatio.ONE) && least.inclusive());
        return justPast ? new NumericDomain.Bounds(Endpoint.inclusive(Count.ZERO), run.max())
                : run;
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
     *                    ({@link #onlyItsEnds(Position, NumericTerm.ValueOf, boolean, Set)})
     * @param named       whether a rule of a value it sits in names it
     */
    private record Source(Takes takes, boolean onlyItsEnds, boolean named, boolean relaxed) {

        Source(Takes takes, boolean onlyItsEnds, boolean named) {
            this(takes, onlyItsEnds, named, false);
        }
    }

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
            // Every value of the value's type falls in some step, and where those steps are every
            // step of the answer's order, every step is one a value falls in; a narrowing of the
            // value is no narrowing of the steps it is shown to leave.
            case NumericTerm.WholeUnitsOf units -> {
                Source of = takes(new NumericTerm.ValueOf(units.position()), read);
                yield of == null || !of.takes().every() || !units.stepsFillTheAnswersOrder() ? null
                        : new Source(new Takes.Every(DefaultBoundOperationFacts.get()
                                .wholeUnitsAnswered(units.operation())), of.onlyItsEnds(),
                                of.named(), of.relaxed());
            }
            case NumericTerm.CodePointClassCount _, NumericTerm.CodePointValueSum _,
                 NumericTerm.CodePointAt _ -> null;
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
            kept = Optional.ofNullable(worksOut(value, read, Set.of(), false));
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
    private static Source worksOut(NumericTerm.ValueOf value, InputReading read,
                                   Set<RuleRef> except, boolean tiedToNoOtherTerm) {
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
                && (!(certifiedAsideFromTheRelationOf(at.projection(), except)
                        || (tiedToNoOtherTerm && onlyRelationsAreUnstated(at.projection())))
                        || !wholeOnItsOrder(value, read)))) {
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
                : new Takes.Some(at.type(), admitted, ends);
        // Related to numbers this reading asks nothing beside: the ends are the values the
        // position takes, and the relation only says which of them go with the others'.
        boolean relatedOnlyToOthers = byARule && tiedToNoOtherTerm
                && !certifiedAsideFromTheRelationOf(at.projection(), except)
                && onlyRelationsAreUnstated(at.projection());
        return new Source(takes,
                !every && (relatedOnlyToOthers || onlyItsEnds(at, value, byARule, except)),
                byARule, byARule && !at.projection().isCertified());
    }

    /**
     * Whether all the bounds fail to state of the rules is how the position is related to others.
     * Each end is then the end of the values the position takes, and what is lost is which of
     * those the others take beside it: a reader that asks a number alone, whose rules relate it to
     * no other number it is asked beside, loses nothing.
     */
    private static boolean onlyRelationsAreUnstated(ProjectionEvidence projection) {
        return projection instanceof ProjectionEvidence.NotCertified unproved
                && !unproved.causes().isEmpty()
                && unproved.causes().stream().allMatch(cause ->
                        cause instanceof ProjectionEvidence.Cause.Lossy lossy
                                && lossy.unstated().equals(
                                        Set.of(ProjectionEvidence.Cause.Unstated.A_RELATION)));
    }

    /**
     * Whether the bounds are shown to be the whole of what the rules leave, taking no account of
     * the relation of the rules in {@code except}: those the bounds cannot state because they
     * relate the position to another, and nothing else is left unproved.
     *
     * <p>That is a statement about the ends the bounds place and nothing more: that the run of a
     * region without those relations differs from the run of the declarations by those relations
     * alone. It is not that every value of the run has a partner in the places the rule names, so
     * it does not make the run one the original region realizes. What a row in the original
     * region is, for the rows a line asks for, is shown by the rule's comparisons holding there
     * ({@link #rulesLeavingRoomAroundTheLine}); the values past those rest on the bounds the
     * original reading derived with the relation, which the region without it keeps
     * ({@link SearchRegion#withoutTheRelationOf}).
     */
    private static boolean certifiedAsideFromTheRelationOf(ProjectionEvidence projection,
                                                           Set<RuleRef> except) {
        return projection.isCertified() || (!except.isEmpty()
                && projection instanceof ProjectionEvidence.NotCertified unproved
                && unproved.causes().stream().allMatch(cause ->
                        cause instanceof ProjectionEvidence.Cause.Lossy lossy
                                && lossy.unstated().equals(
                                        Set.of(ProjectionEvidence.Cause.Unstated.A_RELATION))
                                && except.contains(lossy.rule())));
    }

    /**
     * {@code sources} with a side the bounds are not shown to be the whole of only for rules this
     * relation's line needs nothing of left to what the region answers.
     *
     * <p>Such a side is read as a number a way's statement relates is: over the run the region
     * shows it takes, which holds the rule, and not over every value its type has.
     */
    private List<Source> withoutWhatARowAtTheLineNeeds(List<Source> sources, Roomy room,
                                                       InputReading read) {
        List<Source> out = new ArrayList<>(sources);
        for (int i = 0; i < sides.size(); i++) {
            Side side = sides.get(i);
            if (sources.get(i) == null && side.kept() == null
                    && side.atOnePosition() instanceof NumericTerm.ValueOf value) {
                Source relaxed = worksOut(value, read, room.refsOf(value.position().head()),
                        apartFromEveryOtherSide(i, sources, read, room.rules()));
                if (relaxed != null) {
                    out.set(i, relaxed);
                }
            }
        }
        return out;
    }

    /** Whether no rule of the declarations, besides those in {@code ignoring}, ties the side at
     *  {@code at} to any other side. */
    private boolean apartFromEveryOtherSide(int at, List<Source> sources, InputReading read,
                                            Set<Object> ignoring) {
        for (int other = 0; other < sides.size(); other++) {
            if (other != at && !apartByTheDeclarations(at, other, sources, read, ignoring)) {
                return false;
            }
        }
        return true;
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
    private static boolean onlyItsEnds(Position at, NumericTerm.ValueOf value, boolean byARule,
                                       Set<RuleRef> except) {
        if (!certifiedAsideFromTheRelationOf(at.projection(), except)) {
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
                             Map<Declared, TiedOnTheWay> declared,
                             Map<Written, List<TermPath>> placed,
                             Map<String, Map<Applied, Set<TermPath>>> appliedAt) {

        static RulesRead of(InputReading read) {
            return read.derived(RulesRead.class, _ -> new RulesRead(
                    new ConcurrentHashMap<>(), new ConcurrentHashMap<>(),
                    new ConcurrentHashMap<>(), new ConcurrentHashMap<>(),
                    new ConcurrentHashMap<>()));
        }
    }

    /** One clause of a declaration, whichever place of a parameter it holds at. */
    private record Applied(TypeSymbol worn, int clause) {}

    /**
     * Every place of the parameter {@code rule} is in that the clause it is one of holds at: more
     * than one where the declaration sits at several places of the parameter, a record with two
     * fields of it say.
     */
    private static Set<TermPath> appliedAt(TiedOnTheWay.Rule rule, InputReading read) {
        Map<Applied, Set<TermPath>> clauses = RulesRead.of(read).appliedAt()
                .computeIfAbsent(rule.at().head(), head -> {
                    Map<Applied, Set<TermPath>> out = new HashMap<>();
                    for (Position each : read.domain().positions()) {
                        if (!each.path().head().equals(head)) {
                            continue;
                        }
                        for (Object node : reachedByTheDeclarations(each.path(), read)
                                .nodes().ties()) {
                            if (node instanceof TiedOnTheWay.Rule held && held.clause() >= 0) {
                                out.computeIfAbsent(new Applied(held.worn(), held.clause()),
                                        _ -> new LinkedHashSet<>()).add(held.at());
                            }
                        }
                    }
                    return out;
                });
        return clauses.getOrDefault(new Applied(rule.worn(), rule.clause()), Set.of());
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
     * Whether a rule of a value around both {@code one} and {@code other} relates them: their
     * classes of the rules around each meet ({@link Nodes#ties}), and only then. Places under two
     * parameters never do, since no declaration relates one parameter to another.
     */
    private static boolean tiedByARule(TermPath one, TermPath other, InputReading read) {
        return tiedByARule(one, other, read, Set.of());
    }

    /** The same, without the rules in {@code ignoring} ({@link #rulesLeavingRoomAroundTheLine}). */
    private static boolean tiedByARule(TermPath one, TermPath other, InputReading read,
                                       Set<Object> ignoring) {
        return one.head().equals(other.head())
                && !Collections.disjoint(tiedByTheDeclarations(one, read, ignoring),
                        tiedByTheDeclarations(other, read, ignoring));
    }

    /**
     * The classes the rules around {@code path} are in ({@link Nodes#ties}), where two rules are in
     * one class if some place of the parameter is read by both ({@link Nodes#reads}), without the
     * rules in {@code ignoring}: they tie nothing, and join no rule to another by a place both
     * read. Remembered under the rules left out as well as the parameter, so what a question put
     * aside is a key of what is kept and never mixed into the classes of the rules as they stand.
     */
    private static Set<Object> tiedByTheDeclarations(TermPath path, InputReading read,
                                                     Set<Object> ignoring) {
        TiedOnTheWay declared = RulesRead.of(read).declared().computeIfAbsent(
                new Declared(path.head(), Set.copyOf(ignoring)),
                each -> TiedOnTheWay.ofTheDeclarations(each.head(), read, each.ignoring()));
        Set<Object> out = new LinkedHashSet<>();
        for (Object node : reachedByTheDeclarations(path, read).nodes().ties()) {
            if (!ignoring.contains(node)) {
                out.add(declared.classOf(node));
            }
        }
        return out;
    }

    /** The rules of one parameter, read without the rules in {@code ignoring}. */
    private record Declared(String head, Set<Object> ignoring) {}

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
        return namedDownTo(path, deepest, read, nodes, null);
    }

    /**
     * The same, where {@code apart} is given: a rule the clause cannot be true without, that only
     * keeps the elements of the container {@code path} is an element of apart from one another,
     * asks nothing a list of one fails. It names nothing of the element, and {@code apart} is told
     * there was one ({@link KeptApart}).
     */
    private static Named namedDownTo(TermPath path, int deepest, InputReading read,
                                     Nodes nodes, KeptApart apart) {
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
                out = out.and(namedBy(each, here, path, rest, read, nodes, apart));
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
                                 List<TermPath.Step> rest, InputReading read, Nodes nodes,
                                 KeptApart apart) {
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
                Named says = namedBy(reading, here, place, rest, read, apart);
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
            if (reading.kind() != ClauseRead.Kind.EACH_ELEMENTS_RUN
                    && reading.kind() != ClauseRead.Kind.ELEMENTS_THE_CLAUSE_NEEDS_APART) {
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
                                 List<TermPath.Step> rest, InputReading read, KeptApart apart) {
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
            return namedByARunOfEachElement(reading, here, place, read, null);
        }
        // Told to the caller only for a call the clause cannot be true without: one that is only
        // read may be denied, or be one way of several, and a list of one is then no witness.
        if (reading.kind() == ClauseRead.Kind.ELEMENTS_THE_CLAUSE_NEEDS_APART) {
            return namedByARunOfEachElement(reading, here, place, read, apart);
        }
        if (reading.kind() == ClauseRead.Kind.A_LOOKED_UP_MEMBER) {
            return Named.UNSEEN;
        }
        if (reading.kind() == ClauseRead.Kind.A_MEMBER_THE_CLAUSE_NEEDS) {
            return namedByAMemberTheClauseNeeds(at.size() == fields, here, rest, read);
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
        return mayHoldSome(new TermPath(here.head(), container), read) ? Named.NOT : Named.UNSEEN;
    }

    /**
     * What a rule reading a member of a container it cannot be true without says of the members
     * that stand where the container's keys or elements do: nothing, where the container has no
     * limit on how many it holds, and unseen of everything else the path goes on to.
     *
     * <p>Every value of a container the rule accepts has the member the rule looks for, because
     * the rule is false without it. So any other member is none the rule looks up, and adding it
     * changes no lookup the rule makes. Any value is then a member of some container the rule
     * accepts: it is there already, or it is added beside the members that are, with a value one
     * of them has. A rule that merely reads a member says nothing of that
     * ({@link ClauseRead.Kind#A_LOOKED_UP_MEMBER}): one that wants the member missing accepts no
     * container with it. The values of a map's entries are left out: a second entry takes a value
     * only under a key the type has a second value of.
     *
     * @param atTheContainer whether the fields the rule names end where the fields of the path do
     */
    private static Named namedByAMemberTheClauseNeeds(boolean atTheContainer, TermPath here,
                                                      List<TermPath.Step> rest,
                                                      InputReading read) {
        int fields = 0;
        while (fields < rest.size() && rest.get(fields) instanceof TermPath.Step.Field) {
            fields++;
        }
        if (!atTheContainer || fields + 1 != rest.size()) {
            return Named.UNSEEN;
        }
        List<TermPath.Step> container = new ArrayList<>(here.steps());
        container.addAll(rest.subList(0, fields));
        TermPath at = new TermPath(here.head(), container);
        Position held = read.domain().at(at.position());
        boolean standsWhereAMemberDoes = held != null && switch (held.view().shape()) {
            case Shape.Mapping _ -> rest.get(fields) instanceof TermPath.Step.Key;
            case Shape.Sequence _ -> rest.get(fields) instanceof TermPath.Step.Element;
            default -> false;
        };
        return standsWhereAMemberDoes && holdsWithoutLimit(at, read) ? Named.NOT : Named.UNSEEN;
    }

    /**
     * What a rule reading a run of each element says of {@code place}: nothing where the positions
     * it reads are neither the place, nor under it, nor a value it is a part of — the rule then
     * reads other fields of the elements — and unseen where they are, or where they are placed
     * nowhere.
     *
     * <p>Where {@code apart} is given, the clause cannot be true without the elements being apart
     * ({@link ClauseRead.Kind#ELEMENTS_THE_CLAUSE_NEEDS_APART}). If {@code place} is an element
     * whose own fields are all the rule reads of it, the rule only holds the elements of the
     * container apart from one another. That is false of no list of one element, so it names
     * nothing of the element, and is told to {@code apart}.
     */
    private static Named namedByARunOfEachElement(ClauseRead reading, TermPath here,
                                                  TermPath place, InputReading read,
                                                  KeptApart apart) {
        List<TermPath> reached = placesRead(reading, here, read);
        if (reached.isEmpty()) {
            return Named.UNSEEN;
        }
        for (TermPath each : reached) {
            if (place.isAtOrUnder(each) || each.isAtOrUnder(place)) {
                if (apart != null && readsOnlyFieldsOfTheElement(place, each)) {
                    apart.found = true;
                    continue;
                }
                return Named.UNSEEN;
            }
        }
        return Named.NOT;
    }

    /** Whether {@code place} is an element and {@code read} is that element or a chain of fields
     *  of it. */
    private static boolean readsOnlyFieldsOfTheElement(TermPath place, TermPath read) {
        List<TermPath.Step> steps = place.steps();
        if (steps.isEmpty() || !(steps.getLast() instanceof TermPath.Step.Element)
                || !read.isAtOrUnder(place)) {
            return false;
        }
        return read.steps().subList(steps.size(), read.steps().size()).stream()
                .allMatch(step -> step instanceof TermPath.Step.Field);
    }

    /** Whether a rule the clause cannot be true without, that holds the elements of a container
     *  apart from one another, read the element being asked about. */
    private static final class KeptApart {

        private boolean found;
    }

    /**
     * Whether the container at {@code at} is shown to hold an element beside some value of
     * everything else: some value of it exists, and a count of one or more is in a run of how
     * many it holds that the rules are shown to leave whole ({@link SearchRegion#wholeRunOf}) —
     * so some value holds that many.
     *
     * <p>A rule that reads only how many a container holds says nothing of what its elements are,
     * and the elements of a container holding as many as that count may all be one value. So the
     * count taken is every value of the elements standing in some value, whatever the count is. A
     * rule keeping the elements apart reads them, and is a reading of its own.
     *
     * <p>Shown of the count, not of the value whole. Whether the rules of everything the
     * container sits in project exactly is a question about all of them, and a pattern a field
     * beside it is held to says nothing of how many it holds.
     */
    private static boolean mayHoldSome(TermPath at, InputReading read) {
        NumericDomain.Bounds whole = howManyItHoldsWhole(at, read);
        if (whole == null) {
            return false;
        }
        if (whole.admits(ExactRatio.ONE)) {
            return true;
        }
        // Not one: the fewest the run holds, where that is more and the elements may repeat. A
        // set holds that many values apart, which is a question of the element's type.
        if (!elementsMayRepeat(at, read) || whole.min() == null || !(whole.min().at() instanceof Count least)
                || !(least.exactly().ceiling() instanceof ExactAnswer.Held<BigInteger>(
                        BigInteger up))) {
            return false;
        }
        BigInteger fewest = whole.min().inclusive() || !least.exactly().isWhole() ? up
                : up.add(BigInteger.ONE);
        return fewest.signum() > 0 && whole.admits(ExactRatio.of(fewest));
    }

    /** Whether the container at {@code at} is a list, whose elements may be one value as many
     *  times as it holds them. */
    private static boolean elementsMayRepeat(TermPath at, InputReading read) {
        Position container = read.domain().at(at.position());
        return container != null && container.view().shape()
                instanceof Shape.Sequence(Shape.Sequence.Kind kind, var _)
                && kind == Shape.Sequence.Kind.LIST;
    }

    /**
     * Whether the container at {@code at} is shown to hold as many as it is asked to and no
     * upper end is placed on how many: the rules are shown to leave the whole of the run of how
     * many it holds ({@link SearchRegion#wholeRunOf}), and it has no end above.
     */
    private static boolean holdsWithoutLimit(TermPath at, InputReading read) {
        NumericDomain.Bounds whole = howManyItHoldsWhole(at, read);
        return whole != null && whole.max() == null;
    }

    /** The run of how many the container at {@code at} holds that the rules are shown to leave
     *  whole, or null where there is none shown or no value of the container exists. */
    private static NumericDomain.Bounds howManyItHoldsWhole(TermPath at, InputReading read) {
        Position container = read.domain().at(at.position());
        if (container == null || container.nothingExists()) {
            return null;
        }
        for (PositionBounds each : container.bounds()) {
            if (each.term() instanceof NumericTerm.TakenOf taken
                    && taken.takenAs() instanceof TakenAs.HowManyItHolds) {
                return read.quantities().region().wholeRunOf(taken);
            }
        }
        return null;
    }

    private static boolean overlap(FilingCoordinate one, FilingCoordinate other) {
        return one.overlaps(other);
    }

    /** Whether two places are one, or one is inside the other. */
    private static boolean overlap(TermPath one, TermPath other) {
        return one.isAtOrUnder(other) || other.isAtOrUnder(one);
    }
}
