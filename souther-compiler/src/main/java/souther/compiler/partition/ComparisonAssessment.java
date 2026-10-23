package souther.compiler.partition;

import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.StatedComparison;
import souther.compiler.check.UnreadComparison;
import souther.compiler.core.Core;
import souther.compiler.coverage.Arrivals;
import souther.compiler.diag.Citation;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.EmptyInput;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.NumericTerms;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.FilingCoordinate;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.WhatARelationLeavesUndivided;
import souther.compiler.meaning.AuthoredPointMapping;
import souther.compiler.meaning.CasesOfALineAsked;
import souther.compiler.meaning.DecidingCase;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.WrittenLine;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.UnheldNumber;
import souther.compiler.observe.Figure;
import souther.compiler.reach.ComparisonArrival;
import souther.compiler.types.BindingId;
import souther.compiler.types.ExpansionLineage;

import java.util.ArrayList;
import java.util.Collections;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.SequencedMap;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.function.UnaryOperator;

/**
 * What one comparison comes to on the input space: one reading, and everything read off it.
 *
 * <p><b>One decision with several projections, and not several decisions about one comparison.</b>
 * What a comparison cuts is {@link Cutting}'s one answer, taken from the canonical form the
 * arithmetic reads. What the comparison is a rule <em>about</em> used to be worked out beside that,
 * from the operands as they were written — and the two disagreed. {@code a + 1 <= 10} cut position
 * {@code a} at nine and was classified as naming no position, so a border was drawn and no
 * obligation recorded against it; {@code a <= b - b + 9} cut the same position at the same value and
 * was classified as a rule about a pair, so the question raised was about a place that rule never
 * stopped. A rule was measured by one reading and reported by the other.
 *
 * <p>So the subject is derived here, from the same value the line is, and the disagreement has
 * nowhere to live. Which positions the quantity is over decides both what the rule is about and
 * where the border goes, because both come off {@link Cutting#dividedPosition()} and it is asked
 * once.
 *
 * <p><b>And what a read comparison owes is owed by having been read.</b> The rows at the value it
 * singles out, and the rows in the classes its line makes, are asked for by the reading that found
 * the line — there is no moment at which such a demand is outstanding. So they are the partition's
 * geometry and not a coverage question standing against an answer: carried as both, one decision
 * had two representations again, and the second had no reader once it could never go unanswered.
 *
 * <p><b>Eight ways a comparison leaves the positions nothing, and they are eight.</b> Read to the
 * end and cutting nothing, naming no position at all, reading the answer, reading what a dependency
 * answered, cutting where the quantity does not run, cutting where the rows that arrive stop short,
 * cutting where the statement it is a line of never turns, and not read — each is a different
 * sentence to whoever is told it, and only the last is about a limit of this compiler. Held as one, a tautology was owed a row where the relation changes and a
 * rule this could not read was described as naming no position.
 */
sealed interface ComparisonAssessment {

    /**
     * What a comparison does to the quantity it cuts.
     *
     * <p>Read off the canonical quantity together with the operator, and read once. The operator
     * alone does not answer it: {@code 2 * a == 8} names four and {@code 2 * a == 9} names no whole
     * number at all, under one operator and one shape of rule.
     */
    enum Places {

        /** An order across the line, so rows are owed either side of it and the two sides have
         *  roles. */
        ACROSS_THE_VALUE,

        /** One value singled out: on a position a class of its own, whose values either side are
         *  one class, and on a quantity over positions that counts, a line with the values either
         *  side of it. */
        AT_THE_VALUE,

        /** A value the quantity does not hold, which puts nothing in a class of its own. */
        AT_NO_VALUE
    }

    /**
     * The comparison cuts one position's own values.
     *
     * @param cutting  the line, which is what a threshold and a border are read off
     * @param position the position it divides
     * @param value    the value of the position the classes meet at, or null where the position
     *                 holds none there
     * @param authored how the line stands to the line of its author's it is a place of
     */
    record AtAPosition(Cutting cutting, NumericTerm.FromOnePosition position, Place value,
                       Places places, AuthoredPointMapping authored)
            implements ComparisonAssessment {

        public AtAPosition {
            if (cutting == null || position == null || places == null || authored == null) {
                throw new IllegalArgumentException("a line on a position names the position");
            }
        }
    }

    /**
     * The comparison cuts a form over more than one position, so it divides none of them on its
     * own.
     *
     * <p>A distance and a general form alike. What coverage asks of both is one question — no
     * position is divided by a class of its own, and the place is the comparison's to name — and
     * which of the two shapes the quantity is stays with the quantity.
     *
     * <p>That a value of one position never settles the comparison whatever the others hold is
     * shown only where another term reaches every value of it ({@link UndividedByARelation}):
     * {@code n == a.value}, with {@code a} declared at nought or above, is false wherever {@code n}
     * is below nought. Where it is shown instead that some values of a term settle it and every
     * other value leaves it either way, those values are a class of the term's own, parted from
     * the rest by lines on it, and the term is divided there by the relation.
     *
     * @param relation  what the line states, as a relation of its terms
     * @param left      what {@code relation} is shown to leave its places
     * @param settling  the lines on single positions that part the values settling the relation
     *                  from the rest, each no line of the author's
     * @param authored  how the line stands to the line of its author's it is a place of
     */
    record AcrossPositions(Cutting cutting, Citation at, Places places,
                           UndividedByARelation relation, UndividedByARelation.WhatItLeaves left,
                           List<AtAPosition> settling, AuthoredPointMapping authored)
            implements ComparisonAssessment {

        public AcrossPositions {
            if (cutting == null || at == null || places == null || relation == null
                    || left == null || settling == null || authored == null) {
                throw new IllegalArgumentException("a line over a form names the form");
            }
            settling = List.copyOf(settling);
        }

        /** The line, with what {@code relation} leaves its places over {@code left}. */
        static AcrossPositions leaving(Cutting cutting, Citation at, Places places,
                                       UndividedByARelation relation,
                                       UndividedByARelation.WhatItLeaves left,
                                       AuthoredPointMapping authored, InputReading reading,
                                       CountWitnesses.Lookup witnesses) {
            return new AcrossPositions(cutting, at, places, relation, left,
                    settlingLines(new DrawnBeside(cutting.of().behavior(), at, authored.line(),
                            Optional.of(authored.claims())), left.settled(), reading, witnesses),
                    authored);
        }

        /** The coordinates {@code relation} is shown to leave undivided. */
        Set<FilingCoordinate> undivided() {
            return left.undivided();
        }

        /** The same, with what it leaves its places over the rows that arrive along
         *  {@code ways}. The lines parting the settling values are drawn again only where the
         *  values settling it are not the ones already drawn. */
        AcrossPositions whereRowsArrive(InputReading reading,
                                        List<Reachability.Reaching> ways,
                                        CountWitnesses.Lookup witnesses) {
            UndividedByARelation.WhatItLeaves arriving =
                    relation.leftWhereRowsArrive(reading, ways, witnesses);
            return arriving.settled().equals(left.settled())
                    ? new AcrossPositions(cutting, at, places, relation, arriving, settling,
                            authored)
                    : leaving(cutting, at, places, relation, arriving, authored, reading,
                            witnesses);
        }

        /** The same, where every row arriving comes out on one side of it: it divides none of the
         *  positions it is filed at. */
        AcrossPositions decided() {
            return new AcrossPositions(cutting, at, places, relation,
                    new UndividedByARelation.WhatItLeaves(Set.copyOf(cutting.of().filedAt()),
                            Map.of()), List.of(), authored);
        }

        /** The places a line on one of them parts the values that settle the relation at. */
        Set<FilingCoordinate> dividedBySettling() {
            Set<FilingCoordinate> out = new LinkedHashSet<>();
            settling.forEach(line -> out.addAll(line.cutting().over()));
            return out;
        }
    }

    /**
     * What a line parting the values that settle a relation is drawn beside: the behavior it is a
     * line of, where the comparison stands, and the author's line it is no place of.
     */
    record DrawnBeside(String behavior, Citation at, WrittenLine line,
                       Optional<ComparisonClaim> claim) {

        public DrawnBeside {
            Objects.requireNonNull(behavior, "a line is some behavior's");
            Objects.requireNonNull(at, "drawn beside a comparison standing somewhere");
            Objects.requireNonNull(line, "and no place of some line of the author's");
            Objects.requireNonNull(claim, "the comparison's claim, or the line's own");
        }

        /** The line {@code drawn} said to be no place of the author's line: it claims what the
         *  comparison claimed, and where an application states the relation, what it claims
         *  itself. */
        AuthoredPointMapping noPlaceOfIt(Cutting drawn) {
            return new AuthoredPointMapping.NotAnAuthoredBoundary(line,
                    claim.orElse(drawn.claim()));
        }
    }

    /**
     * The lines on single positions that part the values of each term of {@code settled} that
     * settle the relation, each drawn as a comparison of the term against a number draws it and
     * said to be no place of the author's line — none for a term whose runs come to no such lines,
     * or one of whose lines is no line on its position.
     */
    private static List<AtAPosition> settlingLines(
            DrawnBeside beside,
            Map<NumericTerm, WhatARelationLeavesUndivided.Leaves.Settled> settled,
            InputReading reading, CountWitnesses.Lookup witnesses) {
        List<AtAPosition> out = new ArrayList<>();
        List<NumericTerm> terms = new ArrayList<>(settled.keySet());
        for (NumericTerm term : NumericTerms.inOrder(terms)) {
            // A line is drawn on a number a row can be written to stand at, and only where the
            // model draws it: one the orders' ends alone draw parts no class of the model's.
            if (term.atOnePosition() == null) {
                continue;
            }
            List<WhatARelationLeavesUndivided.Line> lines =
                    settled.get(term).linesOfTheModel();
            List<AtAPosition> here = new ArrayList<>();
            for (WhatARelationLeavesUndivided.Line each : lines) {
                Cutting drawn = Cutting.onOneTerm(beside.behavior(), term,
                        each.at(), each.relation(), reading.quantities());
                if (drawn == null || !(onTheQuantity(beside.at(), drawn, beside.noPlaceOfIt(drawn),
                        reading, false, witnesses) instanceof AtAPosition line)) {
                    here = null;
                    break;
                }
                here.add(line);
            }
            if (here != null) {
                out.addAll(here);
            }
        }
        return out;
    }

    /**
     * Read to the end, the comparison relates numbers of the input to a value no position holds
     * ({@link Cutting.Read.AgainstAnotherValue}).
     *
     * <p>Where some values of a number it relates are shown to settle it whatever the other value
     * holds, and every other value of the number to leave it either way, those values are a class
     * of the number's own, as they are of a relation between positions ({@link AcrossPositions}):
     * {@code l.discount > w}, with {@code w} the greatest a walk from nought has kept, is false
     * wherever the discount is at or below nought. They are parted from the rest by lines on the
     * number. Read as a part of a statement of several they are read in the cases where the
     * statement turns on the relation, and in no other; where no case is one a row can be asked
     * to be in, or a line is not shown to turn the statement in one, the number stays one the
     * other value is not shown to reach.
     *
     * @param filedAt   the coordinates of the input's numbers it relates
     * @param relations what it states, as the relations it is made of, for each reading of it
     * @param undivided those of {@code filedAt} some of {@code relations} are about and every one
     *                  of those is shown to leave undivided; at the others the other value is not
     *                  shown to reach every value there
     * @param settling  the lines on single positions that part the values settling it from the
     *                  rest, each no line of the author's
     * @param beside    what those lines are drawn beside, or empty where none is drawn
     * @param stoppedAt the figures a search for what would have shown more of {@code relations}
     *                  stopped at
     */
    record AgainstAnotherValue(List<FilingCoordinate> filedAt,
                               List<UndividedByARelation> relations,
                               Set<FilingCoordinate> undivided, List<AtAPosition> settling,
                               Optional<DrawnBeside> beside, Set<CompositionBudget> stoppedAt)
            implements ComparisonAssessment {

        public AgainstAnotherValue {
            filedAt = List.copyOf(filedAt);
            relations = List.copyOf(relations);
            undivided = Set.copyOf(undivided);
            stoppedAt = Set.copyOf(stoppedAt);
            settling = List.copyOf(settling);
            Objects.requireNonNull(beside, "drawn beside something, or nothing");
            if (beside.isEmpty() && !settling.isEmpty()) {
                throw new IllegalArgumentException("a line is drawn beside a comparison");
            }
        }

        /** {@code read}, with what it leaves undivided over what the declarations leave, and the
         *  lines parting what settles it drawn {@code beside}. */
        static AgainstAnotherValue of(Cutting.Read.AgainstAnotherValue read,
                                      InputReading reading, Optional<DrawnBeside> beside,
                                      CountWitnesses.Lookup witnesses) {
            return new AgainstAnotherValue(read.over(), read.relations(), Set.of(), List.of(),
                    beside, Set.of()).whereRowsArrive(reading, List.of(), witnesses);
        }

        /** The same, with what it leaves undivided over the rows that arrive along {@code ways}. */
        AgainstAnotherValue whereRowsArrive(InputReading reading,
                                            List<Reachability.Reaching> ways,
                                            CountWitnesses.Lookup witnesses) {
            List<Set<FilingCoordinate>> about = new ArrayList<>();
            List<UndividedByARelation.WhatItLeaves> leaves = new ArrayList<>();
            for (UndividedByARelation each : relations) {
                about.add(each.places());
                leaves.add(each.leftWhereRowsArrive(reading, ways, witnesses));
            }
            Set<FilingCoordinate> shown = new LinkedHashSet<>();
            for (FilingCoordinate at : filedAt) {
                boolean said = false;
                boolean everyOne = true;
                for (int i = 0; i < relations.size(); i++) {
                    if (about.get(i).contains(at)) {
                        said = true;
                        everyOne &= leaves.get(i).undivided().contains(at);
                    }
                }
                if (said && everyOne) {
                    shown.add(at);
                }
            }
            List<AtAPosition> lines = beside.map(drawn -> settlingLines(drawn,
                    settledByEvery(about, leaves), reading, witnesses)).orElse(List.of());
            Set<CompositionBudget> stopped = EnumSet.noneOf(CompositionBudget.class);
            leaves.forEach(each -> stopped.addAll(each.stoppedAt()));
            return new AgainstAnotherValue(filedAt, relations, shown, lines, beside, stopped);
        }

        /**
         * Each number some relation shows settled by some of its values where every relation
         * about its place shows it settled by the same ones: a reading of the comparison on
         * another application that shows its place nothing, or something else, leaves no class
         * of its own there.
         */
        private static Map<NumericTerm, WhatARelationLeavesUndivided.Leaves.Settled> settledByEvery(
                List<Set<FilingCoordinate>> about,
                List<UndividedByARelation.WhatItLeaves> leaves) {
            Map<NumericTerm, WhatARelationLeavesUndivided.Leaves.Settled> out =
                    new LinkedHashMap<>();
            for (UndividedByARelation.WhatItLeaves each : leaves) {
                each.settled().forEach((term, runs) -> {
                    FilingCoordinate at = FilingCoordinate.of(term);
                    boolean alike = true;
                    for (int i = 0; i < leaves.size(); i++) {
                        if (about.get(i).contains(at)) {
                            alike &= runs.equals(leaves.get(i).settled().get(term));
                        }
                    }
                    if (alike) {
                        out.putIfAbsent(term, runs);
                    }
                });
            }
            return out;
        }

        /** The places a line on one of them parts the values that settle the relation at. */
        Set<FilingCoordinate> dividedBySettling() {
            Set<FilingCoordinate> out = new LinkedHashSet<>();
            settling.forEach(line -> out.addAll(line.cutting().over()));
            return out;
        }

        /** The same relation with only {@code lines} parting what settles it. */
        AgainstAnotherValue partedBy(List<AtAPosition> lines) {
            return new AgainstAnotherValue(filedAt, relations, undivided, lines, beside,
                    stoppedAt);
        }
    }

    /** The comparison reads what the behavior answers. */
    record AnswerDependent() implements ComparisonAssessment {}

    /**
     * The comparison is a proposition over what a dependency answered, which the decision table
     * holds as a column ({@link WhatAnAnswerTakesUp}).
     *
     * <p>Not a reading that stopped. A row stands the dependency in rather than writing what it
     * answers, so there is no line on the input space for the comparison to be — and what it
     * distinguishes is still owed rows, on the side that reads it.
     */
    record OnADependencysAnswer() implements ComparisonAssessment {}

    /**
     * Read to the end, the comparison states which case, which truth or whether a value positions
     * of the input hold, and no relation of numbers ({@link Cutting.Read.StatesNoRelation}).
     *
     * <p>Not a reading that stopped, and no line: an application stating the same is no rule
     * lines are drawn on, and what the statement tells apart is owed rows by the decision table.
     */
    record StatesNoRelation() implements ComparisonAssessment {}

    /** The comparison names no position of the behavior's input. */
    record NoInput() implements ComparisonAssessment {}

    /**
     * Read to the end, and the quantity it cuts is nothing: the positions cancel.
     *
     * <p>{@code filedAt} is where the rule is said to have cut nothing, and it comes off the
     * reading rather than off a second walk over the operands. What is left of the quantity is not
     * what the rule is about — {@code a - a <= 0} is about {@code a} and cuts nothing — so the
     * coordinates are the numbers the reading named, whether or not they survived, and they are the
     * numbers rather than the places they sit at ({@link AffineReading#filedAt}).
     */
    record CutsNothing(List<FilingCoordinate> filedAt) implements ComparisonAssessment {

        public CutsNothing {
            filedAt = List.copyOf(filedAt);
        }
    }

    /**
     * Read to the end, and every run that reaches the comparison stops in an operation it is read
     * through ({@link Cutting.Read.AnswersNowhere}): a division by nought is worked out first.
     *
     * <p>Not a reading that stopped, and not {@link CutsNothing}, where a run gets past the
     * comparison and it comes out the same for every row. {@code filedAt} is where the rule is said
     * to answer nowhere, as it is for {@link CutsNothing}.
     */
    record AnswersNowhere(List<FilingCoordinate> filedAt) implements ComparisonAssessment {

        public AnswersNowhere {
            filedAt = List.copyOf(filedAt);
        }
    }

    /** Read in full, and the quantity does not run as far as the line the rule draws. */
    record OutsideTheDomain(Cutting cutting) implements ComparisonAssessment {

        public OutsideTheDomain {
            if (cutting == null) {
                throw new IllegalArgumentException("a line outside the domain is still a line");
            }
        }
    }

    /**
     * Read in full, the quantity runs as far as the line — and no row that arrives at the
     * comparison holds a value at it.
     *
     * <p>Its own answer and not {@link OutsideTheDomain}, which is a fact about the declarations
     * alone and holds wherever the comparison stands. This one is about the place: the guards above
     * the comparison rule the line's values out, so the classes it would make are classes of
     * nothing and the rows they would ask for are rows nothing can write. An author told the first
     * would look at the rule for a line their declarations refuse, and the line is fine — what
     * refuses it is on the way.
     *
     * <p>Only a proof lands here: the whole state at the comparison shown empty, or the region the
     * declarations, the way and what arrives leave together shown to hold no row at the line.
     */
    record NothingArrivesAtItsLine(Cutting cutting) implements ComparisonAssessment {

        public NothingArrivesAtItsLine {
            if (cutting == null) {
                throw new IllegalArgumentException(
                        "a line nothing arrives at is still a line somebody wrote");
            }
        }
    }

    /**
     * Read in full, one of several lines a statement holds together — and wherever a row arrives at
     * it, the statement comes out the same on both sides of it.
     *
     * <p>Its own answer beside {@link NothingArrivesAtItsLine}. Rows do arrive at this line; what
     * the rest of the statement leaves them is an outcome the line does not turn: {@code Int.max(a,
     * a + 1) > 5} turns where {@code a} passes four and never where it passes five, since wherever
     * {@code a} reaches five the other part already holds. An author told that the guards on the
     * way rule the line out would go looking above the rule for something that is in it.
     *
     * <p>Only a proof lands here, as there: the line with where it decides taken in, shown to hold
     * no row.
     */
    record TurnsNothing(Cutting cutting) implements ComparisonAssessment {

        public TurnsNothing {
            if (cutting == null) {
                throw new IllegalArgumentException(
                        "a line a statement never turns on is still a line of it");
            }
        }
    }

    /**
     * Read in full, a relation to another value — and no row that arrives at the comparison takes
     * the way to it.
     *
     * <p>{@link NothingArrivesAtItsLine} for a reading that has no line to be about: what refuses
     * the rows is what holds on the way, and a place told it was left without a line for want of
     * a proof would look for one that is not in the rule. Only a proof lands here.
     */
    record NothingArrivesAtItsRelation(List<FilingCoordinate> filedAt)
            implements ComparisonAssessment {

        public NothingArrivesAtItsRelation {
            filedAt = List.copyOf(filedAt);
        }
    }

    /**
     * Read in full, a relation to another value as a part of a statement of several — and no row
     * takes the way to any case where it decides.
     *
     * <p>{@link TurnsNothing} for a reading that has no line to be about. Rows do arrive at the
     * comparison; the cases the relation would turn the statement in are ones none of them is in.
     */
    record RelationTurnsNothing(List<FilingCoordinate> filedAt) implements ComparisonAssessment {

        public RelationTurnsNothing {
            filedAt = List.copyOf(filedAt);
        }
    }

    /**
     * Read in full, and several relations held together: one rule with a line for each, and where
     * each of them decides.
     *
     * <p>One answer for the comparison, because the comparison is one rule; what each line comes to
     * on the input space is that line's own, read the way a comparison of one line is. Where a line
     * decides is carried with it and never dropped: a row at the line where it decides nothing is a
     * row the statement answers the same way on both sides, so a line taken without it would be
     * owed rows that prove nothing about it.
     *
     * <p>Once a run's way is taken in, one line may be two parts: the line in the cases its cases
     * showed it turns in, and beside it, in the same place, the line not worked out for the cases
     * nobody worked out ({@link BlockReason.WhereALineDecidesNotWorkedOut}). The first is what a
     * row is asked to be at; the second is said at the line's places and asks no row of any case,
     * so neither speaks for the other.
     */
    record Several(List<Part> parts) implements ComparisonAssessment {

        public Several {
            parts = List.copyOf(parts);
            if (parts.isEmpty()) {
                throw new IllegalArgumentException("several lines are some lines");
            }
        }

        /**
         * One line of the statement.
         *
         * @param id    which of the author's lines it is a place of, and which place
         * @param line  what that line comes to, which is what a comparison of one line comes to and
         *              never several again
         * @param cases where the statement turns on it, as cases any one of which is enough: every
         *              case where it was read, and once the way to it is taken in, the cases a row
         *              arriving there can be in. None where {@code line} is no line on the input
         *              space ({@link #isALine}): a case is where a row at the line is asked to be,
         *              and where there is no line there is no row to ask it of. A relation to
         *              another value has them for the lines parting the values that settle it,
         *              which are the lines on the input space it draws ({@link #isReadInCases})
         */
        public record Part(PlaceOfALine id, ComparisonAssessment line,
                           List<DecidingCase> cases) {

            public Part {
                Objects.requireNonNull(id, "a line of a statement is one of its lines");
                cases = DecidingCase.eachByItsOwnCondition(cases);
                if (line == null || line instanceof Several) {
                    throw new IllegalArgumentException(
                            "a line of a statement is what one line comes to: " + line);
                }
                if (!isReadInCases(line) && !cases.isEmpty()) {
                    throw new IllegalArgumentException("what is no line is read in no case: "
                            + line);
                }
            }

            /**
             * {@code line} where it comes to a line, read in {@code cases}; and with no case where
             * it does not.
             */
            static Part ofCases(PlaceOfALine id, ComparisonAssessment line,
                                List<DecidingCase> cases) {
                return new Part(id, line, isReadInCases(line) ? cases : List.of());
            }

            /**
             * Whether {@code line} is read in the cases where the statement turns on it: a line on
             * the input space, or a relation to another value. What parts the values that settle
             * the relation depends on the rows that arrive in a case, so the cases are kept
             * whether or not a line is drawn over the declarations alone.
             */
            static boolean isReadInCases(ComparisonAssessment line) {
                return isALine(line) || line instanceof AgainstAnotherValue;
            }

            /**
             * Whether {@code line} is a line on the input space, which is what a row can be asked
             * to stand at, in a case or not: one on a position, or one on a form over several.
             * Every other answer is a line refused, outside what the declarations leave, one
             * nothing arrives at or the statement never turns on, or one nobody worked out.
             */
            static boolean isALine(ComparisonAssessment line) {
                return switch (line) {
                    case AtAPosition _, AcrossPositions _ -> true;
                    case AnswerDependent _, OnADependencysAnswer _, StatesNoRelation _, NoInput _,
                         CutsNothing _, AnswersNowhere _, AgainstAnotherValue _,
                         OutsideTheDomain _, NothingArrivesAtItsLine _, TurnsNothing _,
                         NoFeasibleInput _, Unread _, NothingArrivesAtItsRelation _,
                         RelationTurnsNothing _, Several _ -> false;
                };
            }

            /**
             * Each reading of the line, one for each case where it decides.
             *
             * <p>A line is looked for where it decides, and each case is somewhere a row can be
             * composed to be, so each is a reading of the line of its own — the way one comparison
             * a helper is called twice with is read once for each call. A row at any of them meets
             * the line, and the line is out of reach only where it is out of reach in all of them.
             */
            public List<WhereAPartDecides> readings() {
                // A relation that parts nothing has no line to read in a case.
                if (line instanceof AgainstAnotherValue against && against.settling().isEmpty()) {
                    return List.of();
                }
                return cases.stream().map(each -> new WhereAPartDecides(id, each.condition()))
                        .toList();
            }
        }

        /**
         * The same statement, for a reader that has nowhere to carry where each line decides.
         *
         * <p>Every line it drew is said not to be drawn, and why: a reader composing rows against a
         * line with nothing that holds them where the line decides would be owed rows the statement
         * answers alike on both sides. A line that was refused keeps its own reason.
         *
         * <p>Where every part was a line, the statement is a reading that stopped, at each place
         * one of them is at. A relation that was no line is no stop: it stays what it was, and the
         * statement stays its parts, each line said not drawn at its own places.
         */
        ComparisonAssessment withNoWayForItsParts() {
            List<Part> each = new ArrayList<>();
            SequencedMap<FilingCoordinate, BlockReason.RuleReadingStopped> why =
                    new LinkedHashMap<>();
            boolean allStopped = true;
            for (Part part : parts) {
                Unread stopped = notDrawn(part.line());
                if (stopped == null) {
                    allStopped = false;
                    // The lines parting what a relation settles are read in cases, which this
                    // reader has nowhere to carry.
                    each.add(part.line() instanceof AgainstAnotherValue against
                            ? new Part(part.id(), against.partedBy(List.of()), List.of()) : part);
                } else {
                    stopped.why().forEach(why::putIfAbsent);
                    each.add(new Part(part.id(), stopped, List.of()));
                }
            }
            return allStopped ? new Unread(why) : new Several(each);
        }

        /**
         * {@code line} said not drawn, or kept its own reason where it was refused — or null where
         * it is no line at all.
         */
        private static Unread notDrawn(ComparisonAssessment line) {
            return switch (line) {
                case Unread unread -> unread;
                case AtAPosition _, AcrossPositions _, OutsideTheDomain _,
                     NothingArrivesAtItsLine _, TurnsNothing _, NoFeasibleInput _ ->
                        new Unread(atEachOf(cuttingOf(line).over(),
                                new BlockReason.SeveralLinesInOneRule()));
                case AgainstAnotherValue _, AnswerDependent _, OnADependencysAnswer _,
                     StatesNoRelation _, NoInput _, CutsNothing _, AnswersNowhere _,
                     NothingArrivesAtItsRelation _, RelationTurnsNothing _ -> null;
                case Several _ -> throw new IllegalStateException(
                        "a line of a statement is what one line comes to: " + line);
            };
        }
    }

    /**
     * Read in full, and the rules leave no input for any line to be about.
     *
     * <p>Its own answer and not {@link OutsideTheDomain}, which says the quantity exists and does
     * not run as far as this rule's line. Here nothing runs anywhere: the declarations reaching this
     * input admit no value at all, so neither this line nor any other is outside anything. Said as
     * the first, an author is sent to look at one rule for a contradiction that is not in it — two
     * clauses each admitting values are empty together, and neither of them is the one that failed.
     *
     * <p>Whose emptiness it is is the input's and not this comparison's. A quantity is a function of
     * the input, so a quantity's values are empty exactly when the input's are — asked of the
     * quantity, this would be a second reader deciding what the rules admit, and the two would
     * disagree about a model wherever one of them read a rule the other did not.
     */
    record NoFeasibleInput(EmptyInput why, Cutting cutting)
            implements ComparisonAssessment {

        public NoFeasibleInput {
            if (why == null || cutting == null) {
                throw new IllegalArgumentException(
                        "an input the rules leave empty is still a line somebody wrote");
            }
        }
    }

    /**
     * The comparison names a position and the reading of it stopped.
     *
     * <p>Only a reason that says a reading stopped, which the type is what enforces. A rule read to
     * the end that divides no one position has its own arms here, and their reasons say nothing
     * fell short — handed to this one, a comparison whose carrier could not be read was described
     * as relating two positions, and a model short of a border came back complete.
     *
     * <p>One reason per place and not one for the comparison. Where a reading stopped there is no
     * quantity for the places to be one subject of, so each of them says what stopped it there — a
     * position met inside an expression this did not take apart is told nothing about what it
     * carries, and one asked about for itself is.
     *
     * @param why where the reading was looking and what it left there. The places are diagnostic
     *            positions and never the subject of a question: what such a rule is about is the
     *            part that was not read
     */
    record Unread(SequencedMap<FilingCoordinate, BlockReason.RuleReadingStopped> why)
            implements ComparisonAssessment {

        public Unread {
            if (why == null || why.isEmpty()) {
                throw new IllegalArgumentException("a reading that stopped says where and why");
            }
            why = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(why));
        }
    }

    /**
     * What {@code comparison} comes to, whoever wrote it.
     *
     * <p>The one way in. {@code applying} is the applications of the closures the comparison
     * stands inside, on each of which it is read. {@code answer} is the binding a clause calls what
     * the behavior answers, or
     * null where the comparison is written in a body and there is nothing to be the answer.
     * {@code writtenIn} is the copy of the body a comparison a body wrote stands in, which tells
     * the lines its author drew from the places a call put them; nothing for a clause.
     *
     * <p><b>The arithmetic answers before anything else is asked.</b> Which positions a rule is
     * about is what the quantity it cuts is over: every atom of a form is a number of a location
     * ({@link souther.compiler.inputs.InputNumber}), so a comparison that came to a line is about
     * the positions of that line and there is nothing left to look up. What the walk over the
     * expression says a side is made of is the answer for a rule that came to no line — where it is
     * the only account there is — and asked first it would be a second reading standing in front of
     * the first, able to veto it and never to add to it: two members of a written list holding one
     * form written two ways agree as arithmetic and are made of different things, so the rule they
     * state would come back as one about no input at all.
     */
    static ComparisonAssessment of(String behavior, StatedComparison comparison, Citation at,
                                   InputReading read, InputReads reads,
                                   ClosureApplications applying,
                                   BindingId answer, Arrivals answering,
                                   boolean drawnByAnInvariant, WhatConditionsState conditions,
                                   Optional<ExpansionLineage> writtenIn,
                                   CountWitnesses.Lookup witnesses) {
        // Asked first, and of the whole comparison. A rule that reads the answer anywhere in it is
        // one this reading does not put on the input space, whichever side the answer is on and
        // whatever else stands beside it: `value.n + query.offset <= 20` is about the answer and
        // about an input, and the input is no more measurable here for the input being named.
        if (readsAnswer(comparison.left(), answer) || readsAnswer(comparison.right(), answer)) {
            return new AnswerDependent();
        }
        Cutting.Read cut = Cutting.read(behavior, comparison, read, reads, applying, answering,
                conditions, writtenIn);
        return switch (cut) {
            case Cutting.Read.Cuts _, Cutting.Read.NoOrderToCountOn _,
                 Cutting.Read.NumberNoRatioHolds _ -> aLine(cut, at, read, drawnByAnInvariant,
                    () -> aboutNoPosition(comparison, reads, read.newtypes()), witnesses);
            // One rule and a line for each relation it holds, each line read as a comparison of
            // one line is and carrying where it decides.
            case Cutting.Read.Several several -> eachLineOf(behavior,
                    Optional.of(comparison.claim()), several, at, read, drawnByAnInvariant,
                    () -> aboutNoPosition(comparison, reads, read.newtypes()), witnesses);
            // Read to the end and cutting nothing, which is a fact about the rule and not a limit
            // of this compiler: `a <= a` holds of every row. Where the comparison names no position
            // either, there is no rule about a position to say it of — `2 > 1` is a comparison of
            // constants and states nothing anywhere.
            case Cutting.Read.CutsNothing over -> over.filedAt().isEmpty()
                    ? aboutNoPosition(comparison, reads, read.newtypes())
                    : new CutsNothing(over.filedAt());
            case Cutting.Read.AnswersNowhere over -> over.filedAt().isEmpty()
                    ? aboutNoPosition(comparison, reads, read.newtypes())
                    : new AnswersNowhere(over.filedAt());
            case Cutting.Read.StatesNoRelation _ -> new StatesNoRelation();
            // Where the reading stopped and the comparison is over what a dependency answered, it is
            // the decision table's. A number of an answer is no number of the input, so this reading
            // stops at it however the comparison was written, and the stop is about whose subject
            // the comparison is rather than about a form this compiler does not read. Asked of what
            // the comparison states, which is what the table makes its column of.
            case Cutting.Read.Stopped _, Cutting.Read.AgainstAnotherValue _
                    when WhatAnAnswerTakesUp.comparison(
                            conditions.comparison(comparison, reads, read).stated().proposition())
                    -> new OnADependencysAnswer();
            // A relation of the input to another value, read to the end, which the rule is and
            // nothing short of it.
            case Cutting.Read.AgainstAnotherValue against -> AgainstAnotherValue.of(against, read,
                    Optional.of(new DrawnBeside(behavior, at, WrittenLine.THE_COMPARISON,
                            Optional.of(comparison.claim()))), witnesses);
            // And where the reading stopped, its own answer for having stopped — decided where it
            // stopped rather than worked out again from the comparison afterwards — and where the
            // values a side holds came from, at each place it did not already answer. Here the walk
            // over the expression is the only account of what the rule is about, which is what it
            // is for.
            case Cutting.Read.Stopped stopped ->
                    besideWhereTheValuesCameFrom(stopped.why(), comparison, reads,
                            read.newtypes());
        };
    }

    /**
     * What one line comes to on the input space: the line, or the refusal to place it.
     *
     * <p>The one reading of a line, whether the comparison states one or a statement holds it
     * among several.
     */
    private static ComparisonAssessment aLine(Cutting.Read line, Citation at, InputReading read,
                                              boolean drawnByAnInvariant,
                                              Supplier<ComparisonAssessment> aboutNoPosition,
                                              CountWitnesses.Lookup witnesses) {
        return switch (line) {
            case Cutting.Read.Cuts cuts ->
                    onTheQuantity(at, cuts.cutting(), cuts.authored(), read, drawnByAnInvariant,
                            witnesses);
            // And where the quantity was read and stands on no order this counts, the carrier is
            // what a reader is owed — at the quantity's own coordinates, because the quantity is
            // what such a rule is about. The word is what the reading established and not what is
            // left when several answers were absent: it says the values here carry no order to
            // draw a line on, and that is exactly what was found.
            case Cutting.Read.NoOrderToCountOn over -> over.over().isEmpty()
                    ? aboutNoPosition.get()
                    : new Unread(atEachOf(over.over(),
                            new BlockReason.UnreadComparisonDomain()));
            // And where the quantity was read, counts, and draws a line that falls at a number no
            // exact ratio holds. The same coordinates as the case above and a reason of its own:
            // what stopped it is a constant the rule is written with, and not the order beneath.
            case Cutting.Read.NumberNoRatioHolds over -> over.over().isEmpty()
                    ? aboutNoPosition.get()
                    : new Unread(atEachOf(over.over(),
                            new BlockReason.LineAtANumberNoRatioHolds()));
            case Cutting.Read.CutsNothing _, Cutting.Read.AnswersNowhere _,
                 Cutting.Read.Stopped _, Cutting.Read.Several _,
                 Cutting.Read.AgainstAnotherValue _, Cutting.Read.StatesNoRelation _ ->
                    throw new IllegalArgumentException("one line is drawn or refused: " + line);
        };
    }

    /**
     * The same, for each line of a statement of several, carrying where each decides — and each of
     * its relations that is no line as what it is: one relating the input to another value, or a
     * line no row could be held to where it decides, said not to be drawn.
     */
    private static ComparisonAssessment eachLineOf(String behavior,
                                                   Optional<ComparisonClaim> claim,
                                                   Cutting.Read.Several lines, Citation at,
                                                   InputReading read, boolean drawnByAnInvariant,
                                                   Supplier<ComparisonAssessment> aboutNoPosition,
                                                   CountWitnesses.Lookup witnesses) {
        return new Several(lines.parts().stream()
                .map(part -> Several.Part.ofCases(part.id(), switch (part.line()) {
                    // Parted from the rest by lines only where the statement turns on the relation
                    // somewhere a row can be asked to be.
                    case Cutting.Read.AgainstAnotherValue against ->
                            AgainstAnotherValue.of(against, read, part.cases().isEmpty()
                                    ? Optional.empty()
                                    : Optional.of(new DrawnBeside(behavior, at,
                                            part.id().line().line(), claim)), witnesses);
                    case Cutting.Read.Stopped stopped -> new Unread(stopped.why());
                    case Cutting.Read.Cuts _, Cutting.Read.NoOrderToCountOn _,
                         Cutting.Read.NumberNoRatioHolds _, Cutting.Read.CutsNothing _,
                         Cutting.Read.AnswersNowhere _, Cutting.Read.Several _,
                         Cutting.Read.StatesNoRelation _ ->
                            aLine(part.line(), at, read, drawnByAnInvariant, aboutNoPosition,
                                    witnesses);
                }, part.cases()))
                .toList());
    }

    /**
     * What an application of an operation states comes to on the input space
     * ({@link Cutting#ofAnApplication}): its lines, or the values it relates.
     *
     * <p>Every line of it is over the input's numbers, so each is somewhere: a line on no position
     * is a comparison of constants, and an application's statement read to the end holds none.
     */
    static ComparisonAssessment ofAnApplication(String behavior, Cutting.Read answered,
                                                Citation at, InputReading read,
                                                CountWitnesses.Lookup witnesses) {
        return switch (answered) {
            case Cutting.Read.Several lines -> eachLineOf(behavior, Optional.empty(), lines, at,
                    read, false, () -> {
                        throw new IllegalStateException("a line an application states at " + at
                                + " is over the input's numbers");
                    }, witnesses);
            // The application states no claim of its own, so a line parting what settles the
            // relation claims what it draws.
            case Cutting.Read.AgainstAnotherValue related ->
                    AgainstAnotherValue.of(related, read, Optional.of(new DrawnBeside(behavior, at,
                            WrittenLine.THE_COMPARISON, Optional.empty())), witnesses);
            case Cutting.Read.Cuts _, Cutting.Read.CutsNothing _, Cutting.Read.AnswersNowhere _,
                 Cutting.Read.Stopped _, Cutting.Read.NoOrderToCountOn _,
                 Cutting.Read.NumberNoRatioHolds _, Cutting.Read.StatesNoRelation _ ->
                    throw new IllegalArgumentException(
                            "an application states lines or values it relates: " + answered);
        };
    }

    /**
     * The same reading, on the narrower domain the run leaves at the comparison's line.
     *
     * <p>The declarations first and the place second, because the two are different sentences and
     * the first holds wherever the comparison stands. What is asked here is the same predicate on
     * the narrower domain, not a second reading of the rule — so a line the declarations already
     * dropped is not asked about again, and what arrives cannot put one back.
     *
     * <p><b>Apart from the reading, because the two are read off different trees.</b> What the rule
     * states is read where the language's operations stand; what arrives at a place is read where
     * they are expanded, which is where a run has places at all. Asked inside the reading, the
     * reading would be one no tree could answer on its own.
     *
     * <p><b>One question, asked of everything that holds of a row there at once.</b> A row at the
     * line is in what the declarations leave, meets every condition the model states on the way,
     * and is among what arrives at the place it is watched at — so the line stands where a region
     * holding all three holds a row at it. Asked of each of them alone, a row the way holds a
     * position apart from would be one the arrival's range runs straight through, and a line
     * nothing reaches would stand.
     *
     * <p>The way is the model's and what arrives is each place's. The model states the conditions
     * once, on the tree an author wrote; the places are where the tree that runs holds the rule, and
     * what the walk of that tree established on the way to one of them is that place's alone.
     *
     * <p>Only a proof drops a line. An arrival nothing could project restricts nothing beyond what
     * the declarations and the way leave ({@link ComparisonArrival.NoProjection}) — and it is not
     * what a comparison the emitter numbered nothing for says, because that one is not asked this
     * at all.
     *
     * <p><b>A line of several is asked on the way and then in each case where it decides.</b> On
     * the way alone, a line nothing arrives at is that, as a line of one is. Then each case: the
     * ones no arriving row can be in are dropped, a case said for several is read in those of its
     * cases arriving rows divide and in no other, and a line rows arrive at where no case leaves
     * one is a line the statement never turns on, which is a fact about the statement and not
     * about the way ({@link TurnsNothing}).
     *
     * <p><b>And a relation is asked again of the rows that arrive.</b> What it leaves undivided
     * turns on what the other side reaches, and a way can narrow that: {@code n == x} under
     * {@code x >= 0} is false at every {@code n} below nought, though over what the declarations
     * leave {@code x} reaches every {@code n} ({@link UndividedByARelation}).
     *
     * @param way         what the model states on the way to the comparison, over what the
     *                    declarations leave
     * @param wayToACase  the same, with a case of where a line of a statement of several decides
     *                    taken in beside it: one it was read in, one of the cases a case said for
     *                    several stands for, or what choosing one has chosen so far
     *                    ({@link CasesOfALineAsked})
     * @param reading     the reading of the input the relation's terms are asked of
     */
    static ComparisonAssessment narrowedByWhatArrives(
            ComparisonAssessment read,
            Reachability way,
            WaysToACase wayToACase,
            List<ComparisonArrival> arrivals,
            boolean drawnByAnInvariant,
            InputReading reading,
            CountWitnesses.Lookup witnesses) {
        if (read instanceof Several several) {
            return new Several(several.parts().stream()
                    .flatMap(part -> aPartNarrowed(part, way, wayToACase, arrivals,
                            drawnByAnInvariant, reading, witnesses).stream())
                    .toList());
        }
        Cutting cutting = switch (read) {
            case AtAPosition at -> at.cutting();
            case AcrossPositions across -> across.cutting();
            // Every other reading is one the declarations settled without reaching a line, and
            // there is nothing for a narrower domain to settle differently.
            default -> null;
        };
        // A rule watched nowhere is not asked this. What the places are is
        // {@link souther.compiler.coverage.EmittedComparisonState.Instrumented}, which is never
        // empty, and a comparison the emitter numbered nothing for is the other arm of that and
        // never reaches here. Answered with none, "all of them proved nothing arrives" is true of
        // no place at all, and the line would go for want of a proof rather than by one.
        if (arrivals.isEmpty()) {
            throw new IllegalArgumentException(
                    "a rule watched at no place is not one to ask what arrives at: " + read);
        }
        if (cutting != null) {
            Arrived arrived = whatArrives(cutting, way, arrivals, drawnByAnInvariant,
                    read instanceof AcrossPositions);
            if (arrived == Arrived.NOTHING_AT_THE_LINE) {
                return new NothingArrivesAtItsLine(cutting);
            }
            // A relation whose rows all come out one way where they arrive is decided there: no
            // value of any position it relates comes out the other way, so it divides none of them,
            // and what the other side reaches is no question about it. The line is still the line
            // the rule draws, and its points still the ones no row can stand at.
            if (read instanceof AcrossPositions across && arrived != Arrived.ACROSS_THE_LINE) {
                return across.decided();
            }
        }
        // What a relation leaves undivided over the rows that arrive, asked only of a relation
        // that is still one here. With no way arriving it is what the declarations leave, which
        // the reading already holds.
        List<Reachability.Reaching> arriving = waysArrivedBy(way, arrivals);
        // A relation to another value has no line to drop, and is dropped the same way: by the
        // proof that no row takes the way to it, which is no case's.
        if (arriving.isEmpty() && read instanceof AgainstAnotherValue against) {
            return new NothingArrivesAtItsRelation(against.filedAt());
        }
        return arriving.isEmpty() ? read : switch (read) {
            case AcrossPositions across -> across.whereRowsArrive(reading, arriving, witnesses);
            case AgainstAnotherValue against -> against.whereRowsArrive(reading, arriving,
                    witnesses);
            default -> read;
        };
    }

    /**
     * The way a row reaches the rule by — none where the way is taken by no row, or no place the
     * rule is watched at is one a row arrives at.
     *
     * <p>What the model states on the way, and not what was seen to arrive at a place. The values
     * a place saw are of the whole comparison's quantity, which is no statement about any one term
     * of a line of it; what narrows what a term reaches is what the way and the case state of it.
     */
    private static List<Reachability.Reaching> waysArrivedBy(Reachability way,
                                                            List<ComparisonArrival> arrivals) {
        if (!(way instanceof Reachability.Reaching reaching)
                || arrivals.stream().allMatch(ComparisonArrival.NothingArrives.class::isInstance)) {
            return List.of();
        }
        return List.of(reaching);
    }

    /**
     * Whether {@code way} is not shown to leave no row at the rule: it is not one the declarations
     * and the conditions on it rule out, the places it is watched at do not all prove that nothing
     * arrives, and some region the way leaves is not shown to hold nothing.
     *
     * <p>No proof that a row arrives. The reading of the way is an inclusion, and a way it cannot
     * take in leaves the region as wide as the declarations do, so this is true of a way it could
     * not settle as much as of one a row takes.
     */
    static boolean someRowArrives(Reachability way, List<ComparisonArrival> arrivals) {
        return waysArrivedBy(way, arrivals).stream().anyMatch(reaching ->
                reaching.holdingEveryRow().stream()
                        .anyMatch(region -> region.emptiness().isEmpty()));
    }

    /** How far the rows arriving at a line get: none to it, to it, or to both sides of it. */
    enum Arrived { NOTHING_AT_THE_LINE, AT_THE_LINE, ACROSS_THE_LINE }

    /**
     * Whether the rows arriving at some place the rule is watched at hold a value at the line, and
     * — where {@code crossing} asks it — whether at some place they stand on both sides of it.
     *
     * <p>Asked of the regions that between them hold every row past the way
     * ({@link Reachability.Reaching#holdingEveryRow}). A way through a choice between runs of one
     * number is a row in one run or another: a line between the runs is reached by neither, and a
     * row in one run and a row in the other differ in a line as two rows in one run do. So whether
     * a row holds a value at the line is asked of each region, and whether rows stand on both sides
     * of it is asked of all of a place's regions, one side in one region and the other in another
     * ({@link Cutting.Sides}). The region that spans them holds the values between the runs, which
     * are no row's, and is asked neither.
     *
     * <p>A way no row takes is one no row arrives at the line by, wherever the tree that runs holds
     * the rule. Otherwise every place the rule is watched at, and the answer is no only where all of
     * them proved it. One rule may be written into the tree that runs more than once, and a run
     * through any of the copies is a run through the rule — so a proof about one of them is a proof
     * about that copy, and the line is what the model states about all of them.
     *
     * <p>Which is why one place that could not be projected leaves the question to the declarations
     * and the way: what a walk did not settle is not a proof that nothing arrives, and a line has to
     * be dropped by a proof rather than by the absence of one.
     *
     * <p>A region is narrowed to a place and read once for both questions, and none is read once
     * both are answered.
     *
     * @param crossing whether to ask if rows stand on both sides of it, which a line of a relation
     *                 is asked as well
     */
    private static Arrived whatArrives(Cutting cutting, Reachability way,
                                       List<ComparisonArrival> arrivals,
                                       boolean drawnByAnInvariant, boolean crossing) {
        if (!(way instanceof Reachability.Reaching taken)) {
            return Arrived.NOTHING_AT_THE_LINE;
        }
        List<SearchRegion> past = taken.holdingEveryRow();
        boolean reached = false;
        boolean crossed = false;
        for (ComparisonArrival arrival : arrivals) {
            if (arrival instanceof ComparisonArrival.NothingArrives) {
                continue;
            }
            Cutting.Sides sides = new Cutting.Sides(cutting);
            for (SearchRegion region : past) {
                Border.Values values = valuesAt(cutting, region, arrival);
                reached = reached || cutting.reachedBy(values, drawnByAnInvariant);
                crossed = crossed || (crossing && sides.add(values));
                if (reached && (crossed || !crossing)) {
                    return crossed ? Arrived.ACROSS_THE_LINE : Arrived.AT_THE_LINE;
                }
            }
        }
        return reached ? Arrived.AT_THE_LINE : Arrived.NOTHING_AT_THE_LINE;
    }

    /**
     * Whether the rows arriving at some place the rule is watched at, in the case {@code keptTo}
     * keeps a region's values to ({@link Cutting#keptTo}), stand on both sides of the line —
     * asked of the regions {@link #whatArrives} asks, a region at a time.
     */
    private static boolean crossedAtSomePlace(Cutting cutting, Reachability way,
                                              List<ComparisonArrival> arrivals,
                                              UnaryOperator<Border.Values> keptTo) {
        if (!(way instanceof Reachability.Reaching taken)) {
            return false;
        }
        List<SearchRegion> past = taken.holdingEveryRow();
        for (ComparisonArrival arrival : arrivals) {
            if (arrival instanceof ComparisonArrival.NothingArrives) {
                continue;
            }
            Cutting.Sides sides = new Cutting.Sides(cutting);
            for (SearchRegion region : past) {
                if (sides.add(keptTo.apply(valuesAt(cutting, region, arrival)))) {
                    return true;
                }
            }
        }
        return false;
    }

    /** What {@code region} leaves the line's quantity for the rows arriving at a place. */
    private static Border.Values valuesAt(Cutting cutting, SearchRegion region,
                                          ComparisonArrival arrival) {
        return cutting.valuesIn(switch (arrival) {
            case ComparisonArrival.Values arriving -> cutting.narrowedBy(arriving, region);
            case ComparisonArrival.NoProjection _, ComparisonArrival.NothingArrives _ -> region;
        });
    }

    /**
     * One line of a statement of several, on the way and then in each case where it decides: the
     * line, and beside it the same line again for the cases of it nobody worked out, where there
     * are any.
     */
    private static List<Several.Part> aPartNarrowed(Several.Part part, Reachability way,
                                                    WaysToACase wayToACase,
                                                    List<ComparisonArrival> arrivals,
                                                    boolean drawnByAnInvariant,
                                                    InputReading reading,
                                                    CountWitnesses.Lookup witnesses) {
        ComparisonAssessment arrived = narrowedByWhatArrives(part.line(), way, wayToACase,
                arrivals, drawnByAnInvariant, reading, witnesses);
        // A relation to another value has no line of its own, and the lines parting the values
        // that settle it are read where the statement turns on it, as a line is.
        if (arrived instanceof AgainstAnotherValue against) {
            return aRelationPartNarrowed(part, against, wayToACase, arrivals, reading, witnesses);
        }
        // Only where it is a line at all: a line refused, outside what the declarations leave, or
        // one nothing arrives at, is that whatever the cases are, and is read in none of them.
        if (!Several.Part.isALine(arrived)) {
            return List.of(new Several.Part(part.id(), arrived, List.of()));
        }
        Cutting cutting = cuttingOf(arrived);
        CasesReached found = casesTurnedOn(cutting, part.cases(), wayToACase, arrivals, reading);
        List<DecidingCase> reached = found.reached();
        List<Reachability.Reaching> deciding = found.deciding();
        Set<CompositionBudget> stoppedAt = found.stoppedAt();
        // The cases nobody worked out are neither ones the line turns in, owed rows where it may
        // decide nothing, nor ones dropped for a proof nobody finished: they are the line not
        // worked out there, naming every figure any of them stopped at, beside whatever the other
        // cases showed. Said at the line's places and read in no case: no row is asked to be at a
        // line nobody worked out, so which cases those were is not something a reader is told.
        List<Several.Part> out = new ArrayList<>();
        if (!reached.isEmpty()) {
            out.add(new Several.Part(part.id(), arrived instanceof AcrossPositions across
                    && !deciding.isEmpty() ? across.whereRowsArrive(reading, deciding, witnesses)
                    : arrived,
                    DecidingCase.saidInAsFewAsMay(reached)));
        }
        if (!stoppedAt.isEmpty()) {
            out.add(new Several.Part(part.id(), new Unread(atEachOf(cutting.over(),
                    new BlockReason.WhereALineDecidesNotWorkedOut(stoppedAt.stream()
                            .map(CompositionBudget::figure).toList()))),
                    List.of()));
        }
        if (out.isEmpty()) {
            out.add(new Several.Part(part.id(), new TurnsNothing(cutting), List.of()));
        }
        return List.copyOf(out);
    }

    /**
     * The cases {@code line} turns the statement in, the ways rows reach it by there, and the
     * figures the cases nobody worked out stopped at.
     */
    record CasesReached(List<DecidingCase> reached, List<Reachability.Reaching> deciding,
                        Set<CompositionBudget> stoppedAt) {}

    /**
     * Each of {@code cases} where a row on each side of {@code cutting} can stand in it. Rows on
     * the two sides in one case differ in this line alone, so the statement turns between them; a
     * case only one side has rows in is a case crossing the line leaves, and turns nothing there.
     *
     * <p>What a relation leaves undivided is asked again over the ways returned, which is where
     * its values are what the case leaves them. A case said for several is asked of the cases it
     * stands for, one at a time: rows on the two sides of its condition may be in two of them, and
     * the line turns nothing between those ({@link CasesOfALineAsked}). The line is then read in
     * the ones that divide rows and in no other, so that a row in one it turns nothing in is not
     * counted at its points. Counted for each such case on its own, so that what one case spent
     * decides nothing about another.
     */
    private static CasesReached casesTurnedOn(Cutting cutting, List<DecidingCase> cases,
                                              WaysToACase wayToACase,
                                              List<ComparisonArrival> arrivals,
                                              InputReading reading) {
        List<DecidingCase> reached = new ArrayList<>();
        List<Reachability.Reaching> deciding = new ArrayList<>();
        Set<CompositionBudget> stoppedAt = EnumSet.noneOf(CompositionBudget.class);
        for (DecidingCase each : cases) {
            if (each.saidAlone()) {
                Reachability toIt = wayToACase.apply(each.condition());
                if (wayToACase.crossed(cutting, each.condition(), () ->
                        crossedAtSomePlace(cutting, toIt, arrivals,
                                cutting.keptTo(each.condition(), reading)))) {
                    reached.add(each);
                    deciding.addAll(waysArrivedBy(toIt, arrivals));
                }
                continue;
            }
            CasesOfALineAsked.Found found = CasesOfALineAsked.casesOf(each, condition ->
                    wayToACase.crossed(cutting, condition, () ->
                            crossedAtSomePlace(cutting, wayToACase.apply(condition), arrivals,
                                    cutting.keptTo(condition, reading))));
            for (DecidingCase one : found.decidesIn()) {
                reached.add(one);
                deciding.addAll(waysArrivedBy(wayToACase.apply(one.condition()), arrivals));
            }
            stoppedAt.addAll(found.notWorkedOut());
        }
        return new CasesReached(reached, deciding, stoppedAt);
    }

    /**
     * What a relation to another value parts in one case: the lines that turn the statement in it,
     * and whether any row takes the way to it.
     */
    record InACase(boolean reachable, List<AtAPosition> lines) {

        public InACase {
            lines = List.copyOf(lines);
        }
    }

    /**
     * A relation to another value as a part of a statement of several, on the way and then in each
     * case where it decides: each line parting the values that settle it, read in the cases it
     * turns the statement in.
     *
     * <p>Which values settle the relation is a question about the rows that arrive, so it is
     * asked again in each case, over the rows that arrive there, which are no more than the
     * declarations leave. A line is then read in a case only where rows stand on both sides of
     * it, as a line is.
     *
     * <p>The relation itself, with no line, stays beside them where some case has no line that
     * turns the statement in it, or none was worked out there: a place is left without its
     * reason only where a line was drawn for it in the cases that line turns in. The figures the
     * cases nobody worked out stopped at are said as they are for a line.
     */
    private static List<Several.Part> aRelationPartNarrowed(
            Several.Part part, AgainstAnotherValue against,
            WaysToACase wayToACase, List<ComparisonArrival> arrivals,
            InputReading reading, CountWitnesses.Lookup witnesses) {
        // What a condition says of the way to it and of the lines it parts is the condition's
        // and not the case's, and a case said for several is asked of each condition in turn.
        Map<Proposition, InACase> asked = new HashMap<>();
        Function<Proposition, InACase> inCase = condition ->
                asked.computeIfAbsent(condition, _ -> {
                    Reachability toIt = wayToACase.apply(condition);
                    return new InACase(toIt instanceof Reachability.Reaching,
                            against.whereRowsArrive(reading, waysArrivedBy(toIt, arrivals),
                                            witnesses)
                                    .settling().stream()
                                    .filter(line -> crossedAtSomePlace(line.cutting(), toIt,
                                            arrivals, line.cutting().keptTo(condition, reading)))
                                    .toList());
                });
        return partsOfARelation(part, against, inCase);
    }

    /**
     * The parts a relation to another value comes to, given what it parts in each case:
     * {@code inCase} is asked of every condition a case is taken apart into.
     */
    static List<Several.Part> partsOfARelation(Several.Part part, AgainstAnotherValue against,
                                               Function<Proposition, InACase> inCase) {
        // Each case is taken apart to the end and asked by itself: the lines of a narrower case
        // are not the lines of a wider one, so no case is given up or said for several before
        // its own lines are known. Cases are said for several only past that, where they part the
        // values by the same lines.
        Map<List<AtAPosition>, List<DecidingCase>> casesByLines = new LinkedHashMap<>();
        Set<CompositionBudget> stoppedAt = EnumSet.noneOf(CompositionBudget.class);
        boolean someCaseLeftUndrawn = part.cases().isEmpty();
        for (DecidingCase each : part.cases()) {
            CasesOfALineAsked.Atoms<InACase> atoms = CasesOfALineAsked.atomsOf(each, inCase);
            stoppedAt.addAll(atoms.notWorkedOut());
            for (CasesOfALineAsked.Atom<InACase> atom : atoms.each()) {
                // A case no row takes is no case of the statement.
                if (!atom.answer().reachable()) {
                    continue;
                }
                List<AtAPosition> lines = atom.answer().lines();
                if (lines.isEmpty()) {
                    someCaseLeftUndrawn = true;
                    continue;
                }
                casesByLines.computeIfAbsent(lines, _ -> new ArrayList<>())
                        .add(DecidingCase.alone(atom.condition()));
            }
        }
        // Cases that were all worked out and none of them reached: the relation turns the
        // statement nowhere a row is, which is not a relation left without a line.
        if (casesByLines.isEmpty() && !someCaseLeftUndrawn && stoppedAt.isEmpty()) {
            return List.of(new Several.Part(part.id(),
                    new RelationTurnsNothing(against.filedAt()), List.of()));
        }
        someCaseLeftUndrawn |= casesByLines.isEmpty();
        List<Several.Part> out = new ArrayList<>();
        casesByLines.forEach((lines, cases) -> out.add(new Several.Part(part.id(),
                against.partedBy(lines), DecidingCase.saidInAsFewAsMay(cases))));
        if (someCaseLeftUndrawn || !stoppedAt.isEmpty()) {
            out.add(new Several.Part(part.id(), against.partedBy(List.of()), List.of()));
        }
        if (!stoppedAt.isEmpty()) {
            out.add(new Several.Part(part.id(), new Unread(atEachOf(against.filedAt(),
                    new BlockReason.WhereALineDecidesNotWorkedOut(stoppedAt.stream()
                            .map(CompositionBudget::figure).toList()))), List.of()));
        }
        return List.copyOf(out);
    }

    /**
     * The line {@code line} is about, where it is one line's answer and is about one.
     */
    private static Cutting cuttingOf(ComparisonAssessment line) {
        return switch (line) {
            case AtAPosition at -> at.cutting();
            case AcrossPositions across -> across.cutting();
            case OutsideTheDomain outside -> outside.cutting();
            case NothingArrivesAtItsLine unarrived -> unarrived.cutting();
            case TurnsNothing turns -> turns.cutting();
            case NoFeasibleInput none -> none.cutting();
            case AnswerDependent _, OnADependencysAnswer _, StatesNoRelation _, NoInput _,
                 CutsNothing _, AnswersNowhere _, Unread _, AgainstAnotherValue _, Several _,
                 NothingArrivesAtItsRelation _, RelationTurnsNothing _ ->
                    throw new IllegalArgumentException(
                         "a reading that drew no line is about none: " + line);
        };
    }

    /**
     * One answer at every one of {@code places}, kept in the order they were given.
     *
     * <p>Sound where the places are one subject: the coordinates of one quantity, or the places a
     * statement nothing read at all names. A reading that stopped has no such subject, and its
     * places are answered one at a time where it stopped.
     */
    static <R extends BlockReason.RuleWithoutLineReason> SequencedMap<FilingCoordinate, R>
            atEachOf(List<FilingCoordinate> places, R why) {
        SequencedMap<FilingCoordinate, R> out = new LinkedHashMap<>();
        places.forEach(each -> out.putIfAbsent(each, why));
        return out;
    }

    /**
     * What a comparison naming no position of the input comes to.
     *
     * <p>Two answers and not one. A comparison of constants is about nowhere, and there is nothing
     * for a sentence about a position to be about. A comparison over values an operation answered
     * is about somewhere — the position those values came from — and what the rule says about the
     * values <em>there</em> is what would take inverting whatever the operation did. Held alike,
     * the second went out as a rule about nothing, and the position it plainly concerns came back
     * as one the model states nothing about.
     */
    private static ComparisonAssessment aboutNoPosition(StatedComparison comparison,
                                                        InputReads reads,
                                                        DeclarationNewtypes newtypes) {
        return besideWhereTheValuesCameFrom(new LinkedHashMap<>(), comparison, reads, newtypes);
    }

    /**
     * What a reading that stopped comes to: what it left at each place it was filed at, and at each
     * place the values a side holds came from that it was not.
     *
     * <p>Two facts about two places, and neither is asked to say the other. In
     * {@code c >= atLeast} with {@code c} an element of {@code Set.map(x -> x + 1, cs)}, the
     * reading is filed at {@code atLeast}, whose own values the rule is about, and what that place
     * is left with is that place's
     * ({@link souther.compiler.check.UnreadComparison#whereItStopped}). That the rule is about a
     * value made from {@code cs} is a fact about {@code cs}, and asked only where the comparison is
     * filed nowhere, it would be said of no place at all.
     *
     * <p>A place already answered keeps its answer: there is one word for a place, and the reading
     * that stopped there is what decided it.
     */
    private static ComparisonAssessment besideWhereTheValuesCameFrom(
            SequencedMap<FilingCoordinate, BlockReason.RuleReadingStopped> filed,
            StatedComparison comparison, InputReads reads, DeclarationNewtypes newtypes) {
        SequencedMap<FilingCoordinate, BlockReason.RuleReadingStopped> why =
                new LinkedHashMap<>(filed);
        GuardThresholds.cameFrom(comparison, reads, newtypes, why);
        return why.isEmpty() ? new NoInput() : new Unread(why);
    }

    /**
     * What a line comes to on the input space, from the quantity it is on.
     *
     * @param authored  how the line stands to the line of its author's it is a place of, carried
     *                  to whatever reads where a row on it would go
     * @param witnesses where a count the line's relation reads is shown to take every value
     *                  beside how many its container holds, at a row getting to the line
     */
    private static ComparisonAssessment onTheQuantity(
            Citation at, Cutting cutting, AuthoredPointMapping authored, InputReading read,
            boolean drawnByAnInvariant, CountWitnesses.Lookup witnesses) {
        Quantities quantities = read.quantities();
        // Whether there is an input at all, before anything is asked about where its values run.
        // A quantity is a function of the input, so where the rules admit no input they admit no
        // value of any quantity — and every question below is about one quantity's values against
        // one rule's line, which is a question about a model that has some.
        Optional<EmptyInput> empty = quantities.emptiness();
        if (empty.isPresent()) {
            return new NoFeasibleInput(empty.get(), cutting);
        }
        // The line is placed, and what stands beside it is asked here, once. A rule that could not
        // be told where the values part is neither a rule drawing nowhere nor one drawing
        // somewhere: it is one whose sides were not worked out, and it is said so at the position
        // rather than read as less. Every place the line parts the values is asked, which is two
        // for a rule naming a value, and every reader of the line below holds the seams this
        // asked for.
        if (cutting.seams() instanceof ExactAnswer.Unheld<List<Seam>> unheld) {
            return sideNotWorkedOut(cutting, unheld.why());
        }
        // The line and not one of its points. A rule drawing where the quantity never reaches
        // divides the position into nothing, and a reader told that the rule went unread would go
        // looking for a limit of this compiler that is not there.
        if (!cutting.reachedIn(quantities.region(), drawnByAnInvariant)) {
            return new OutsideTheDomain(cutting);
        }
        ExactAnswer<Places> places = places(cutting);
        if (places instanceof ExactAnswer.Unheld<Places> unheld) {
            return sideNotWorkedOut(cutting, unheld.why());
        }
        Places kind = ((ExactAnswer.Held<Places>) places).value();
        NumericTerm.FromOnePosition divided = cutting.dividedPosition();
        if (divided == null) {
            // Named by the comparison that drew it, which is the one thing about such a place this
            // compiler can always say exactly. It is on no position, and writing it out would be as
            // much of it as a pretty-printer got.
            UndividedByARelation relation = relationOf(cutting);
            return AcrossPositions.leaving(cutting, at, kind, relation,
                    relation.left(read, witnesses), authored, read, witnesses);
        }
        // Read off the one place its value is read at, which is not taken as held: an answer that
        // was not is what the position is told, as for every other side that was not worked out.
        ExactAnswer<Optional<Place>> value = cutting.seam().flatMap(seam -> cutting.singles()
                ? cutting.singledValue(seam) : ExactAnswer.held(cutting.dividedValue(seam)));
        return switch (value) {
            case ExactAnswer.Unheld<Optional<Place>> unheld ->
                    sideNotWorkedOut(cutting, unheld.why());
            case ExactAnswer.Held<Optional<Place>> held ->
                    new AtAPosition(cutting, divided, held.value().orElse(null), kind, authored);
        };
    }

    /** What a line over several positions states, as a relation of their numbers: the quantity's
     *  answer ({@link BorderQuantity#relationAt}). */
    private static UndividedByARelation relationOf(Cutting cutting) {
        return cutting.of().relationAt(cutting.at(), cutting.claim().statedRelation());
    }

    /** A rule whose line is placed and whose sides were not worked out, said at every place the
     *  quantity is filed at. */
    private static ComparisonAssessment sideNotWorkedOut(Cutting cutting, UnheldNumber why) {
        return new Unread(atEachOf(cutting.over(), new BlockReason.LineSideNotWorkedOut(why)));
    }

    /**
     * What the rule does to the quantity, from the canonical quantity and the operator together.
     *
     * <p>Not from the operator alone. {@code 2 * a == 8} names four and {@code 2 * a == 9} names no
     * whole number at all, under one operator: whether the value the rule wrote is one the quantity
     * holds is the quantity's answer, and it is asked of the quantity.
     *
     * <p>Asked of whether a value of a <em>position</em> could be written instead, a form over
     * several positions has none at all — so {@code a + b == 10}, which takes ten, came back naming
     * no value the quantity holds, alongside {@code 2 * a + 2 * b == 9}, which does not.
     */
    private static ExactAnswer<Places> places(Cutting cutting) {
        if (!cutting.singles()) {
            return ExactAnswer.held(Places.ACROSS_THE_VALUE);
        }
        return cutting.takesTheValueItNames().map(takes ->
                takes ? Places.AT_THE_VALUE : Places.AT_NO_VALUE);
    }

    /**
     * Where a reader is sent for what this leaves the positions with, or empty where it leaves them
     * nothing.
     *
     * <p><b>Whose answer it is turns on whether the quantity was reached.</b> A rule that was read
     * is about its quantity, so the positions it is filed at are the quantity's — {@code a + b - b
     * + c <= 10} is {@code a + c <= 10}, and a note at {@code b} would say the rule relates a
     * position it does not mention. A reading that stopped has no quantity to be about, so the
     * positions the walk met are the whole of what can be said, and nothing here may be read as
     * what the rule is about.
     *
     * <p>A quantity that came out empty is the third: there are no coordinates to file at, and the
     * positions the comparison names are what makes {@code a <= a} worth saying at all — the model
     * names a position there and cuts nothing.
     *
     * <p>Answered here so that no caller chooses. Chosen at the two producers, one of them reached
     * for the walk's positions because that was the helper in hand, and a rule read from end to end
     * was filed at a position its arithmetic had cancelled.
     *
     * <p>Asked of nothing. Each case was filed where it was read and holds where; a comparison, an
     * environment and the module's names are what it takes to work that out, and working it out is
     * not what happens here.
     */
    default List<FilingCoordinate> filedAt() {
        return switch (this) {
            case AcrossPositions over -> over.cutting().over();
            case OutsideTheDomain outside -> outside.cutting().over();
            case NothingArrivesAtItsLine unarrived -> unarrived.cutting().over();
            case TurnsNothing turns -> turns.cutting().over();
            // The positions its quantity is over, as every read rule's are. That the rules leave
            // the input empty says nothing about which positions this rule is about.
            case NoFeasibleInput none -> none.cutting().over();
            case Unread unread -> List.copyOf(unread.why().keySet());
            case CutsNothing cuts -> cuts.filedAt();
            case AnswersNowhere nowhere -> nowhere.filedAt();
            case NothingArrivesAtItsRelation unarrived -> unarrived.filedAt();
            case RelationTurnsNothing turns -> turns.filedAt();
            case AgainstAnotherValue against -> against.filedAt();
            // Where each of its lines is filed, each place once: one rule, and its lines are what
            // it is about.
            case Several several -> several.parts().stream()
                    .flatMap(part -> part.line().filedAt().stream())
                    .distinct()
                    .toList();
            case AtAPosition _, AnswerDependent _, OnADependencysAnswer _, StatesNoRelation _,
                 NoInput _ -> List.of();
        };
    }

    /**
     * What the reading of lines leaves at each place this comparison is filed at, and empty where
     * it leaves nothing.
     *
     * <p><b>Named for the reading it is the answer of, and not for the assessment it is read
     * off.</b> What a comparison comes to is one decision; what a reading makes of it is that
     * reading's own, and the two do not agree even about one comparison — a rule relating two
     * positions is read here from end to end and places no line, and the reading that turns clauses
     * into sets of values gets nothing it can hold from the same rule. A name saying only that a
     * reason was read off an assessment would be reached for by that reader too, and the answer it
     * would take is the one that says nothing fell short.
     *
     * <p><b>Per place, and the same at every place only where the places are one subject.</b> A
     * comparison whose arithmetic reached a quantity is about that quantity, so its places are the
     * quantity's coordinates and one answer holds at all of them. A reading that stopped has no
     * quantity to be about, and each place it was left at says what stopped it there — handed one
     * answer, a position met inside an expression this did not take apart was told what another
     * position's carrier carries.
     *
     * <p>Answered once, here. Both producers of this evidence — a clause of an {@code ensures} and a
     * {@code guard}'s comparison — worked the same table out separately, so a case added to
     * {@link ComparisonAssessment} had to be answered twice and the two could disagree about one
     * comparison. That is the shape this whole type was made to have none of.
     *
     * <p><b>Once per place for a comparison of one line, and once per line for a statement of
     * several.</b> Each line of {@code Int.max(a, a + b) > 5} is its own: the one on the sum relates
     * two positions, and the one on {@code a} is never turned on — two things about one place, and
     * a place told only the first would hide a line of the rule.
     *
     * <p>Empty rather than null, and no {@code default} on the switch. A comparison that drew a
     * line, one about no position of the input, and one about what the behavior answers each leave
     * nothing for a reader to be told, and saying so with an absent value made the absence a
     * sentinel one caller had to remember to test for. An arm added is a compile error in this
     * method and in the value reading's own beside it, which is the point of neither having a
     * default.
     */
    default List<LeftAt> whatEachPlaceIsLeftWith() {
        return switch (this) {
            // Which of the two a form that divides nothing is: a line over a run is one number and
            // one line with no position under it, and a line over several positions is a relation
            // between them. Answered from what the quantity is over rather than by the count of its
            // terms, since a form of one term is either.
            // A place the values settling it are parted at by a line is divided, and is left
            // nothing here.
            case AcrossPositions across -> {
                if (!(across.cutting().of().whyItDividesNoPosition()
                        instanceof BlockReason.ComparisonRelatingTwoValues)) {
                    yield sameAtEachPlace(across.cutting().of().whyItDividesNoPosition());
                }
                Set<FilingCoordinate> divided = across.dividedBySettling();
                yield relatingAt(filedAt().stream()
                        .filter(place -> !divided.contains(place)).toList(), across.undivided(),
                        across.left().stoppedAt());
            }
            // Another value is no position, and what the rule says is the same thing it says
            // against one: where the value here stands against it. A place a line parts the
            // values settling it at is divided, and is left nothing here.
            case AgainstAnotherValue against -> {
                Set<FilingCoordinate> divided = against.dividedBySettling();
                yield relatingAt(against.filedAt().stream()
                        .filter(place -> !divided.contains(place)).toList(), against.undivided(),
                        against.stoppedAt());
            }
            case CutsNothing _ -> sameAtEachPlace(new BlockReason.ComparisonCuttingNothing());
            case AnswersNowhere _ -> sameAtEachPlace(new BlockReason.ComparisonAnswersNowhere());
            case OutsideTheDomain _ -> sameAtEachPlace(UnreadComparison.outsideWhatTheQuantityHolds());
            // Not the reason above: there the declarations never run as far as the line, and here
            // they do — what stops short of it is the values that arrive at the comparison, ruled
            // out by the guards on the way. An author reading the first would look at one rule for
            // a contradiction with their declarations that is not in it.
            case NothingArrivesAtItsLine _ ->
                    sameAtEachPlace(new BlockReason.ComparisonNothingArrivesAtItsLine());
            // Nor that one: rows arrive at this line, and the statement it is a line of comes out
            // the same either side of it wherever they do.
            case TurnsNothing _ ->
                    sameAtEachPlace(new BlockReason.ComparisonLineTurningNothing());
            case NothingArrivesAtItsRelation _ ->
                    sameAtEachPlace(new BlockReason.ComparisonRelationNothingArrivesAt());
            // A relation the statement turns on in no case a row is in tells no values apart and
            // owes no rows, and has no line to name a reason for: it leaves its places nothing.
            case RelationTurnsNothing _ -> List.of();
            // What each of its lines leaves, each in its own words — and, of what a line read to
            // the end leaves, nothing at a position another of its lines divides, since the rule
            // divides it. A line whose reading stopped is said wherever it is: it may divide the
            // position further, so the line that does divide it does not settle its classes.
            case Several several -> {
                List<FilingCoordinate> divided = several.parts().stream()
                        .filter(part -> part.line() instanceof AtAPosition)
                        .flatMap(part -> cuttingOf(part.line()).over().stream())
                        .toList();
                yield several.parts().stream()
                        .flatMap(part -> part.line().whatEachPlaceIsLeftWith().stream())
                        .filter(left -> left.why() instanceof BlockReason.RuleReadingStopped
                                || !divided.contains(left.at()))
                        .distinct()
                        .toList();
            }
            // Its own answer for having stopped, decided where it stopped and at each place it was
            // left at. Worked out again from the comparison afterwards, one whose carrier stopped
            // the reading came back as a rule that relates two positions — a sentence saying no
            // measure is short of anything, over a model missing a border.
            case Unread unread -> unread.why().entrySet().stream()
                    .map(each -> new LeftAt(each.getKey(), each.getValue()))
                    .toList();
            // Nothing about this rule fell short, and nothing about this rule is what happened. The
            // rules of the input admit no value between them, which is one fact about the behavior
            // and not one per rule at each position it names — said here, a model with two clauses
            // and four positions would be told eight times, and each time about a rule that is not
            // the one at fault.
            case NoFeasibleInput _, AtAPosition _, NoInput _, AnswerDependent _ -> List.of();
            // Read by the decision table, which owes the rows it distinguishes. Left here as a
            // place, it would be a rule that reading named reported as one nobody read.
            case OnADependencysAnswer _, StatesNoRelation _ -> List.of();
        };
    }

    /**
     * One place a comparison is filed at, and what the reading of lines leaves there.
     *
     * @param at  the place
     * @param why what is left there, in the words of the line that left it
     */
    record LeftAt(FilingCoordinate at, BlockReason.RuleWithoutLineReason why) {

        public LeftAt {
            Objects.requireNonNull(at, "something is left somewhere");
            Objects.requireNonNull(why, "something left somewhere is left for a reason");
        }
    }

    /** The same answer at every place this is filed at, which are one quantity's coordinates. */
    private List<LeftAt> sameAtEachPlace(BlockReason.RuleWithoutLineReason why) {
        return leftAtEachOf(filedAt(), why);
    }

    /**
     * A relation's word at each of {@code places}: that it relates the value there to another
     * value and divides none of them, where it is shown to leave the place undivided, and that the
     * other value is not shown to reach every value there, where it is not.
     *
     * <p>Undivided is where the relation draws no line, the ends of a type read as a relation
     * reads them ({@link WhatARelationLeavesUndivided.Leaves}), and that is all it is read as here.
     * It is not that every value the type holds has a row on each side the run can hold, and a
     * reader wanting that asks it of the rows.
     *
     * <p>Where a search for what would have shown more stopped at some of {@code stoppedAt}, a
     * place nothing is shown of says so, with the figures.
     */
    static List<LeftAt> relatingAt(List<FilingCoordinate> places,
                                   Set<FilingCoordinate> undivided,
                                   Set<CompositionBudget> stoppedAt) {
        BlockReason.RuleWithoutLineReason notShown = stoppedAt.isEmpty()
                ? new BlockReason.RelationNotShownToReachEveryValue()
                : new BlockReason.RelationNotShownWhereTheSearchStopped(Figure.inOrder(
                        stoppedAt.stream().map(CompositionBudget::figure).toList()));
        return places.stream().distinct().map(at -> new LeftAt(at, undivided.contains(at)
                ? new BlockReason.ComparisonRelatingTwoValues() : notShown)).toList();
    }

    /** {@code why} at every one of {@code places}, each once, in the order they were given. */
    static List<LeftAt> leftAtEachOf(List<FilingCoordinate> places,
                                     BlockReason.RuleWithoutLineReason why) {
        return places.stream().distinct().map(at -> new LeftAt(at, why)).toList();
    }

    /**
     * Whether this line is one a border is built on.
     *
     * <p>On a position, only where the rule orders the values around it. A value of a position
     * singled out is a class of its own there, and the values either side of it are one class, so
     * there is nothing for a border to owe a row away from.
     *
     * <p>On a quantity over positions, a value singled out as well, where the quantity has values
     * beside it ({@link BorderQuantity#singlesWithSides}). No position holds it as a class, so the
     * line is the only place the rule is measured at: the rows where the quantity comes to the
     * value, and the nearest ones where it comes to the values either side of it. A rule that names
     * a value the quantity does not hold names no place at all, on either.
     */
    default boolean drawsABorder() {
        return switch (this) {
            case AtAPosition at -> at.places() == Places.ACROSS_THE_VALUE;
            case AcrossPositions over -> over.places() == Places.ACROSS_THE_VALUE
                    || (over.places() == Places.AT_THE_VALUE
                            && over.cutting().of().singlesWithSides());
            case Several several -> several.parts().stream()
                    .anyMatch(part -> part.line().drawsABorder());
            case AnswerDependent _, OnADependencysAnswer _, StatesNoRelation _, NoInput _,
                 CutsNothing _, AnswersNowhere _, AgainstAnotherValue _, OutsideTheDomain _,
                 TurnsNothing _, NothingArrivesAtItsLine _, NoFeasibleInput _, Unread _,
                 NothingArrivesAtItsRelation _, RelationTurnsNothing _ -> false;
        };
    }

    /**
     * Whether anything in {@code e} reads the binding a rule calls the answer.
     *
     * <p>A mechanical predicate over the tree, and it classifies nothing by itself. Two readers ask
     * it and reach different conclusions: {@link #of} answers that the comparison raises no
     * input-coverage obligation, and {@link EnsuresThresholds} answers that a rule about the answer
     * is not one this compiler failed to read. Written twice, the two came apart — the second had
     * the predicate and the first did not — so it is written once and neither reader owns what the
     * other makes of it.
     *
     * <p>Syntactic. {@code value.n - value.n + query.limit.value <= 20} does not depend on the
     * answer once the arithmetic is read, and this answers that it does. The atoms of the canonical
     * form are the input's positions, so the arithmetic cannot see through a read of the answer at
     * all; a predicate that quietly did some of the cancelling would be a second reading of the
     * comparison, which is the shape this whole assessment is written against.
     *
     * <p>False where there is no answer to read, which is every comparison written in a body.
     */
    static boolean readsAnswer(Core e, BindingId answer) {
        if (answer == null) {
            return false;
        }
        if (e instanceof Core.Read read && answer.equals(read.binding())) {
            return true;
        }
        boolean[] found = {false};
        Core.forEachChild(e, child -> found[0] |= readsAnswer(child, answer));
        return found[0];
    }
}
