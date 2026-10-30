package souther.compiler.query;

import souther.compiler.check.CoverageObligation;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.ModelOccurrences;
import souther.compiler.coverage.ComparisonEmissionIndex;
import souther.compiler.meaning.Quantity;
import souther.compiler.partition.CountWitnesses;
import souther.compiler.diag.Citation;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.ReadingPolicy;
import souther.compiler.inputs.FilingCoordinate;
import souther.compiler.inputs.InputQuestion;
import souther.compiler.inputs.InputUses;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.RulesWithNoLine;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.StandingQuestion;
import souther.compiler.partition.LinesWhereTheyFall;
import souther.compiler.partition.RuleReachNumbering;
import souther.compiler.publish.CanonicalSelection;
import souther.compiler.publish.PublicationOrders;
import souther.compiler.ast.Hir;
import souther.compiler.check.PathReachability;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Place;
import souther.compiler.partition.LinearQuantity;
import souther.compiler.partition.OrderedAffineBoundary;
import souther.compiler.core.Core;
import souther.compiler.coverage.ConditionOutcomeSite;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.coverage.SiteNumbering;
import souther.compiler.observe.Classification;
import souther.compiler.observe.Figure;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.RowOutcome;
import souther.compiler.observe.WorkFigure;
import souther.compiler.partition.MeasuredInput;
import souther.compiler.partition.ObservedInputs;
import souther.compiler.partition.Axis;
import souther.compiler.partition.AxisId;
import souther.compiler.partition.BodyDistinction;
import souther.compiler.partition.BodyInputReading;
import souther.compiler.partition.Border;
import souther.compiler.partition.DrawnBoundary;
import souther.compiler.partition.InputUse;
import souther.compiler.partition.ClassCoexistence;
import souther.compiler.partition.Criterion;
import souther.compiler.partition.DerivedValue;
import souther.compiler.partition.ReachingCuts;
import souther.compiler.partition.Demand;
import souther.compiler.partition.DomainPoint;
import souther.compiler.partition.BorderQuantity;
import souther.compiler.partition.StandingAtAPoint;
import souther.compiler.partition.ThresholdOfADerivedValue;
import souther.compiler.partition.LevelRealizer;
import souther.compiler.partition.PointSearchGoal;
import souther.compiler.partition.Realization;
import souther.compiler.partition.RealizationTarget;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.CompositionCapacity;
import souther.compiler.partition.CompositionRepertoire;
import souther.compiler.partition.ValuesTried;
import souther.compiler.partition.EnsuresThresholds;
import souther.compiler.partition.GuardThresholds;
import souther.compiler.partition.BoundaryLine;
import souther.compiler.partition.PartitionClass;
import souther.compiler.partition.Partitions;
import souther.compiler.partition.QuantityKey;
import souther.compiler.partition.ReadTogether;
import souther.compiler.partition.InputClassifications;
import souther.compiler.partition.Generator;
import souther.compiler.partition.Reachability;
import souther.compiler.partition.SaidOnTheWay;
import souther.compiler.partition.WayToTheBorder;
import souther.compiler.partition.WhyKept;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.LinkedHashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.SequencedMap;
import java.util.SequencedSet;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.function.Supplier;
import java.util.function.UnaryOperator;

/**
 * Measuring one behavior's rows against the distinctions its model draws.
 *
 * <p>Each position is measured on its own. A row that could not be read at one position still says
 * what it says at the others, so an unreadable value leaves that axis undecided and nothing else.
 */
final class Coverages {

    /**
     * What the model divides one behavior into, and the reading of its declarations that produced
     * it.
     *
     * <p>Two things and not one, because only the first is what the model says. The reading holds a
     * way of asking the declarations reaching an input a further question, so it belongs to whoever
     * is doing the asking and compares by which of them built it — kept inside the geometry, it made
     * the geometry a thing no answer could hold.
     *
     * <p>Handed over together because they are produced together and reading is what costs: every
     * rule of every parameter is read to arrive at either, and a caller that wanted both and asked
     * twice would read them twice.
     */
    record Partitioned(Partitions.Partitioning geometry,
                       souther.compiler.inputs.Quantities reading,
                       java.util.Map<souther.compiler.partition.ConditionOccurrence,
                               souther.compiler.diag.Citation> conditionsMet,
                       Map<Integer, Citation> rulesReachedAt) {}

    /** A row showing {@code count} takes every value beside how many its container holds, at a
     *  run recorded at one of {@code reaching} ({@link Adequacy.WitnessOfACount}). */
    interface WitnessesOfACount {
        CountWitnesses.Sought of(Quantity.HowManyMeet count,
                                            Set<ConditionOutcomeSite> reaching);
    }

    /**
     * The witnesses of each comparison of {@code body}: those at a run recorded where the
     * comparison is, by the places the module's emission numbered for it — none for a comparison
     * nothing records a run at, which no run is shown to get to.
     */
    private static CountWitnesses.AtComparisons atTheComparisonsOf(Core body,
                                                                    CoverageSites.Plan plan,
                                                                    WitnessesOfACount found) {
        ComparisonEmissionIndex[] index = {null};
        return comparison -> {
            if (index[0] == null) {
                index[0] = ComparisonEmissionIndex.ofBody(body, plan);
            }
            Set<ConditionOutcomeSite> reaching = new LinkedHashSet<>();
            ModelOccurrence.statedAt(comparison).map(index[0]::madeFor).orElse(List.of())
                    .forEach(each -> each.site().ifPresent(reaching::add));
            return reaching.isEmpty() ? CountWitnesses.Lookup.NONE
                    : count -> found.of(count, reaching);
        };
    }

    /**
     * The positions one behavior is measured at, with what its own comparisons divide them into.
     *
     * <p>Asked here rather than worked out again wherever it is needed. What a report says is not
     * covered and what a generator writes a row for have to be the same positions and the same classes,
     * and two derivations of them would be two chances to disagree.
     *
     * <p><b>Measured against the reading it is handed.</b> Which positions the input has and what
     * its rules leave the numbers at them are the reading's to say, and the names and the policy
     * both were read against come with it. Taken apart and handed over as a domain beside the names
     * to read it under, the measurement would be free to be made against one reading and the
     * behavior's rows walked by another.
     *
     * @param witnesses a row showing a count takes every value beside how many its container
     *                  holds, at a run recorded at one of a comparison's places — asked where a row
     *                  is run, and handed in
     */
    static Partitioned partitioningOf(Hir.SpecBehavior behavior,
                                      souther.compiler.inputs.InputReading read,
                                      souther.compiler.partition.BodyReading reading,
                                      CoverageSites.Plan plan,
                                      PathReachability.Arrivals arrives,
                                      souther.compiler.check.StatedContract stated,
                                      souther.compiler.values.Allowance<
                                              souther.compiler.inputs.NumericTerm.FromOnePosition>
                                              distinctions,
                                      WitnessesOfACount witnesses) {
        // Which of the three this elaboration holds, settled before anything reads a body. A tree
        // and a `null` are two facts under one shape, and every reader below would tell them apart
        // again or stop telling them apart at all.
        Core body = reading instanceof souther.compiler.partition.BodyReading.Read it
                ? it.emitted() : null;
        souther.compiler.check.AnalysisBody analysis =
                reading instanceof souther.compiler.partition.BodyReading.Read it
                        ? it.analysis() : null;
        ReadingPolicy policy = read.domain().policy();
        // The one world the rules of this behavior's declarations are read in, which is the reading
        // this input already made of them.
        RuleReadingContext ruleReading = RuleReadingContext.of(read.rules(), policy,
                read.domain().machines(), read.domain().today());
        souther.compiler.inputs.Quantities quantities = read.quantities();
        Partitions.Partitioning partitioning =
                Partitions.of(behavior.name(), read, policy);
        // What the behavior states about its own answer, which is read whether or not anything
        // implements it: a clause is written against the declaration, so an injected behavior draws
        // its lines like any other and there is no body for them to have come out of.
        EnsuresThresholds.Clauses clauses = EnsuresThresholds.of(stated, read);
        // What the analysis tree binds to the elements of what, built once for both readers of it.
        // The bindings an expansion wrote are the bindings of the tree it expanded: the two
        // representations of one body are two expansions with two sets of them, so `elements` —
        // which is the emitted tree's — is about bindings neither reader below has.
        ElementBindings standing = analysis == null
                ? ElementBindings.NONE
                : ElementBindings.of(analysis, read.rules().newtypes());
        // Whether there is a tree to read is the reading's own answer, so a body with no analysis
        // representation is handed over and comes back with nothing rather than being checked for
        // here as well.
        // Where this reading writes down the places it met rules nothing this compilation holds
        // wrote. One numbering for every reader of this body, because an address means a place only
        // under something that says which addresses were being handed out — numbered apiece, one
        // number would name a place per reader and nothing downstream could tell them apart.
        RuleReachNumbering reaches =
                new RuleReachNumbering(read.symbols().module(), behavior.name());
        GuardThresholds.Guards guards = body == null ? GuardThresholds.Guards.NONE
                : GuardThresholds.of(behavior.name(), analysis, body, plan, read, standing, arrives,
                        reaches, atTheComparisonsOf(body, plan, witnesses));
        // And what the declarations state between two of this input's positions. Such a rule places
        // no end at either of them, so the reading of ends has nothing to draw it from; read here,
        // it is a line like the two above and is arranged with them.
        // And what the behavior states about the strings at its positions, in its body and in its
        // own clauses alike. Read off the tree that has those rules in it: the emitted body has
        // each of them expanded into what it does, so a reading of it holds none — which is why
        // this is the other body and not the one above. Both go to one reader, because a term
        // written about in both places is one term with one set of classes, and two readers would
        // be two measures of it, each told nothing of the other's.
        souther.compiler.partition.BehaviorSetStatements.Read sets =
                souther.compiler.partition.BehaviorSetStatements.of(behavior.name(), analysis, stated, read,
                        read.domain().parameterReads(), standing, distinctions, guards.forks(),
                        reaches, guards.partnered());
        List<souther.compiler.partition.LineDrawn> declared =
                souther.compiler.partition.DeclaredThresholds.between(behavior.name(), read);
        // Every producer of one kind of line, put together before the position is divided. Two
        // rules at one value are one cut and stay separate obligations, which is what the merge
        // below does — applied one producer at a time, a clause and a guard naming one number would
        // divide the position twice.
        // And each of them at the positions the name it was drawn on reaches, before anything is
        // matched against an axis. A field every case of a sum spreads is named at the sum and
        // written under a case, so one line there is one line per case — on the same number and from
        // the same rule.
        // And which computations of a value derived from several positions are cut at several
        // places, which is whether their positions are divided by the lines that settle one of the
        // comparisons. Decided here, once, over every line every reader drew: the classes dropped
        // and the weights owed in their place are the one answer, carried to whoever measures the
        // weights.
        List<souther.compiler.partition.LineDrawn> drawnBetween =
                both(declared, both(clauses.between(), guards.between()));
        souther.compiler.partition.DerivedValues.Decided derived =
                souther.compiler.partition.DerivedValues.decide(
                        both(clauses.throughADerivedValue(), guards.throughADerivedValue()),
                        drawnBetween);
        souther.compiler.partition.LinesWhereTheyFall.Filed filed =
                souther.compiler.partition.LinesWhereTheyFall.of(read,
                        both(both(clauses.evidence(), guards.evidence()), derived.evidence()),
                        sets.statements(), sets.blocked(),
                        both(drawnBetween, derived.between()));
        return new Partitioned(Partitions.withEvidence(partitioning, quantities,
                filed.evidence(), filed.blocked(), distinctions, ruleReading,
                // And the lines this had nowhere to put, which are findings of the same kind: a rule
                // of the model that came to no line at a position it is about.
                everyRuleWithNoLine(clauses, guards, filed, sets),
                filed.between(),
                // What a row had to satisfy to arrive at each comparison, from the walk that
                // assumed it. A clause of a declaration is not written at a place in a body and has
                // nothing on the way to it, so only the guards have any of this.
                guards.reaching(),
                // Classified above and projected here onto the one question a conclusion turns on.
                switch (reading) {
                    case souther.compiler.partition.BodyReading.Read _,
                         souther.compiler.partition.BodyReading.NoBody _ ->
                            new souther.compiler.partition.MeasureClosure
                                    .Drawing.FromTheReading();
                    case souther.compiler.partition.BodyReading.NotInElaboration _ ->
                            new souther.compiler.partition.MeasureClosure
                                    .Drawing.NoneWasMade(behavior.name());
                },
                // And the case each arm of a `match` is, which positions what decides a fork may
                // turn on, and which forks are within one application of the closures around
                // them, which the walk of the comparisons reads where the reading of the runs may
                // not.
                guards.operationsStanding(), derived.replaced()), quantities,
                // Where this reading met each condition it places itself, beside the geometry and
                // not inside it. A report points at a condition and an answer says which condition
                // it is, and the two are kept apart so that moving one leaves the other alone.
                guards.conditionsMet(),
                // And the same for the rules it places itself, which is every rule written where
                // this compilation holds no file to open.
                reaches.reachedAt());
    }

    /**
     * Every rule that came to no line, from all three readers, sorted the one way.
     *
     * <p>Which of them found a rule is not part of what any of them found: a clause of a
     * declaration, a body's comparison and a line nothing could place are three producers of one
     * kind of evidence, and a reader downstream is told the same thing about any of them.
     */
    private static RulesWithNoLine everyRuleWithNoLine(
            EnsuresThresholds.Clauses clauses, GuardThresholds.Guards guards,
            LinesWhereTheyFall.Filed filed,
            souther.compiler.partition.BehaviorSetStatements.Read sets) {
        // Every producer's answer in one gathering. Left out of it, a rule an author wrote would
        // reach the measure, come to nothing, and be shown to nobody — while the position it names
        // came back as one the model says nothing about.
        souther.compiler.inputs.RulesWithNoLine.Gathered found =
                new souther.compiler.inputs.RulesWithNoLine.Gathered();
        // The lines that had nowhere to fall, as the findings whoever could not place them made.
        filed.blocked().forEach(each -> found.add(each.reported()));
        // And the rules about the strings whose subject this reading could not place at a position.
        // A question each and no finding: what a report is owed about such a rule is that nothing
        // worked out what it states there, which the question says, and a measure that closed over
        // it would be closing over a reading that stopped.
        sets.nothingClassifies().forEach(found::asked);
        // And the forks whose condition no reader took in. A question for each and no finding: what
        // a report is owed about such a rule is that nothing worked out what it states, which the
        // question says, and where it says it is what the reading got to rather than what the fork
        // is about.
        sets.forks().forEach(each ->
                each.filed().forEach((at, why) ->
                        found.unclassified(each.cited(), ModelOccurrences.NONE, at, why)));
        return clauses.noLine().and(guards.noLine()).and(filed.noLine()).and(found.found());
    }

    /** The two producers' lines, in one list. */
    private static <T> List<T> both(List<T> declared, List<T> compared) {
        if (declared.isEmpty()) {
            return compared;
        }
        List<T> all = new ArrayList<>(declared);
        all.addAll(compared);
        return List.copyOf(all);
    }

    /**
     * What the classes measure comes to for one behavior.
     *
     * <p>What the model divides this behavior into is made once by
     * {@link souther.compiler.query.Adequacy.Divided} and read off {@code subject} here. Worked out
     * again on the way in, this and the boundaries beside it would be two derivations of one thing
     * and two chances to disagree about it. The lines those rules drew are not part of it: what a
     * behavior is owed at them is the module's one relation projected to it
     * ({@link souther.compiler.query.Adequacy.BodyBorders}), and the classes measure reads none of
     * it.
     *
     * <p>{@code uses} is whether anything the behavior states reads each position, which decides
     * what each position is owed and nothing about what it holds or what the rows reached.
     */
    static PartitionEvidence of(souther.compiler.partition.MeasuredInput subject,
                                souther.compiler.query.Adequacy.RowReading observed,
                                souther.compiler.partition.AdequacyPolicy.OfTheMeasures budget,
                                BodyInputReading body, InputUses uses) {
        List<RowOutcome> rows = observed.rowsSeen();
        Partitions.Partitioning partitioning = subject.partitioning();

        List<PartitionEvidence.AxisCoverage> axes = new ArrayList<>();

        // The measures that divide their number, which are the ones a row is placed at. Handed
        // every measure, this asks a classifier about numbers there are no classes to place a value
        // in, and the count it comes back with is over a set no answer here is about.
        Readings readings = Readings.of(rows, subject,
                observed.gaps().stream()
                        .filter(gap -> gap.fact().code().leftNoRowRead()).toList());
        // Walked as the reading holds it: a location at a time, and each measure beside the
        // location it sits at. What one of its measures is owed to say includes what the reading of
        // the position left unread, which is the position's answer — asked of the entry the walk is
        // at rather than of whichever measure happens to be in hand.
        for (Readings.AtPosition at : readings.positions()) {
            for (Readings.AxisReading reading : at.axes()) {
                axes.add(coverageOf(at, reading, readings, partitioning, observed.rowsWereRead(),
                        toldApartAt(body.distinctions(), reading.axis()),
                        uses.at(reading.axis().path())));
            }
        }
        // Each measure asked its own closure, and neither told from the length of what came back.
        // What one of them is short of says nothing about the other: a rule whose line nothing
        // could read leaves the border measure short while the classes either side of it were read
        // in full, and the enumeration above is the same case the other way round.
        return new PartitionEvidence(
                PartitionDerivation.of(axes, partitioning.partitionClosure(),
                        partitioning.inputIsEmpty()),
                pairsOf(subject.behavior(), readings, observed.rowsWereRead(), budget, body),
                partitioning.undivided(), partitioning.rulesWithoutALine(),
                partitioning.rulesWhereARunMayStop(), partitioning.blocked(),
                // What the model asked and nothing answered, taken whole and not gathered as the
                // axes are walked. The questions are the model's; whether a position could be
                // measured is the separate answer `undivided` beside them carries, and a position
                // no axis came back for still has whatever was written about it.
                partitioning.notSeparated(), unansweredIn(partitioning),
                readings.whyUnclassified());
    }

    /**
     * What every row said at every position, read once.
     *
     * <p>The measures below were putting the same question to the rows — which class is this row in,
     * here — and answering the follow-up differently. The single-position coverage counted the rows
     * that could not say and reported them as undecided; the combinations left those rows out and
     * reported what remained as untried. One reading, so that a row nothing could place is the same
     * fact wherever it is read.
     *
     * @param unseen rows that were never observed at all, which no reading can show — each as the
     *               reason it was not observed, so that a measure weakened by one of them says which
     */
    record Readings(List<AtPosition> positions, List<WhereARowSat> byRow,
                    List<Incompleteness.Met> unseen) {

        /**
         * What the rows came to at every measure of one location.
         *
         * <p>The unit a reader of a location answers in: the location's own account, and beside it
         * what the rows said at each number measured there. Which measure belongs to which location
         * is settled while this is built and is never worked out again from a measure in hand.
         */
        record AtPosition(souther.compiler.partition.MeasuredInput.MeasuredPosition position,
                          List<AxisReading> axes) {}

        /**
         * What the rows came to at one measure.
         *
         * <p>The classes they reached, how many could not say where they were, and one reason per
         * kind for those that could not. Read once as the rows are walked: a caller that asked
         * again with a measure in hand would be putting a question to this reading about something
         * it holds, which is what an axis from another measurement gets a wrong answer out of.
         */
        record AxisReading(Axis axis, int at, Map<String, RowWitnesses> covered, int couldNotSay,
                           List<Incompleteness> stopped) {}

        /** Where one row was placed at each measure, in the order the measures are walked, and what
         *  the row is as a witness of the classes it was placed in. Null at a measure the row is not
         *  placed by, which is one the model only bounds. */
        record WhereARowSat(List<Classification> at, RowWitnesses by) {}

        static Readings of(List<RowOutcome> rows,
                           souther.compiler.partition.MeasuredInput subject,
                           List<Incompleteness.Met> unseen) {
            // The measures a row is placed at, in the measurement's own order, and what each row
            // came to at each of them — asked for in that order and answered in it, so nothing
            // here looks a measure up in what it was just handed.
            souther.compiler.partition.MeasuredInput.MeasuredAxes walked = subject.partitionAxes();
            List<WhereARowSat> read = new ArrayList<>(rows.size());
            for (RowOutcome row : rows) {
                read.add(new WhereARowSat(InputClassifications.placedAt(row.inputs(), walked),
                        RowWitnesses.of(row)));
            }
            // And the same run of measures cut where the locations cut it, which is what the walk
            // above is the flattening of.
            List<AtPosition> out = new ArrayList<>();
            int index = 0;
            for (souther.compiler.partition.MeasuredInput.MeasuredPosition at
                    : subject.measurements()) {
                List<AxisReading> here = new ArrayList<>();
                for (Axis axis : at.partitionAxes().axes()) {
                    here.add(readingOf(axis, index++, read));
                }
                out.add(new AtPosition(at, List.copyOf(here)));
            }
            return new Readings(List.copyOf(out), List.copyOf(read), List.copyOf(unseen));
        }

        /**
         * What the rows came to at the measure the walk has reached.
         *
         * <p>A row that could not read a value here is counted among those that could not say,
         * whatever else it placed; one that read every value and put none in a class is not, since
         * it was read and says so. One reason per kind, which is what a hundred rows too large at
         * one position are — how many there were is the count beside it.
         */
        static AxisReading readingOf(Axis axis, int at, List<WhereARowSat> rows) {
            Map<String, RowWitnesses.Gathering> covering = new LinkedHashMap<>();
            Map<Object, Incompleteness> byKind = new LinkedHashMap<>();
            int couldNotSay = 0;
            for (WhereARowSat row : rows) {
                Classification said = row.at().get(at);
                if (said instanceof Classification.Classified in) {
                    for (String id : in.classIds()) {
                        covering.computeIfAbsent(id, _ -> new RowWitnesses.Gathering())
                                .add(row.by());
                    }
                }
                if (said != null && said.stopped() != null) {
                    couldNotSay++;
                    byKind.putIfAbsent(said.stopped().identity(), said.stopped());
                }
            }
            return new AxisReading(axis, at, RowWitnesses.Gathering.done(covering), couldNotSay,
                    List.copyOf(byKind.values()));
        }

        boolean someRowsUnseen() {
            return !unseen.isEmpty();
        }

        boolean noRows() {
            return byRow.isEmpty();
        }

        /** Every measure a row is placed at, in the order they were walked. The flattening of the
         *  locations above and not a second list beside them. */
        List<AxisReading> everyAxis() {
            List<AxisReading> out = new ArrayList<>();
            positions.forEach(at -> out.addAll(at.axes()));
            return List.copyOf(out);
        }

        /**
         * Whether every row said where it was at {@code read}.
         *
         * <p>Only then does a class or a combination nothing sits in mean nothing reaches it. One
         * row that could not be placed at one of the positions leaves every class of that position,
         * and every combination it takes part in, undecided rather than untried.
         */
        WeakeningSet weakening(List<AxisReading> read) {
            Set<Weakening> out = new LinkedHashSet<>();
            for (Incompleteness.Met gap : unseen) {
                out.add(new Weakening.ObservationIncomplete(gap));
            }
            // Every reading's, whatever else met the same thing. What makes two of these one fact
            // and what happens to the places they were met at is the account's, asked once there
            // rather than settled again by whichever reading this walk reached first.
            for (AxisReading each : read) {
                each.stopped().forEach(gap -> out.add(Weakening.ObservationIncomplete.of(gap)));
            }
            return WeakeningSet.ofAll(out);
        }

        /**
         * Why the rows that could not be placed could not be placed — one reason per kind, in the
         * order the measures were walked.
         *
         * <p>Walked in that order rather than in a row's own map, which is built with
         * {@code Map.copyOf} and so iterates in an order that changes between runs. A report that
         * changes between runs cannot be compared between runs.
         */
        List<Incompleteness> whyUnclassified() {
            return reasonsIn(everyAxis());
        }

        /** The same over any run of measures the walk produced. */
        static List<Incompleteness> reasonsIn(List<AxisReading> read) {
            Map<Object, Incompleteness> byKind = new LinkedHashMap<>();
            for (AxisReading each : read) {
                each.stopped().forEach(gap -> byKind.putIfAbsent(gap.identity(), gap));
            }
            return List.copyOf(byKind.values());
        }
    }

    /**
     * The two-class combinations the rows reach.
     *
     * <p>A combination a row sits in is <em>proven reachable</em>, and the row is the proof. One no row
     * sits in has not been shown unreachable — nothing has tried to build a value for it — so it is
     * unknown rather than missing. The difference matters: calling it unreachable flatters the number,
     * and calling it missing sends the author after a row that may not exist.
     *
     * <p>Pairs, rather than the full product, for the reason pairwise testing exists: most rules that
     * two inputs are involved in are decided by those two, and the product of every input is more rows
     * than anyone writes. A behavior with one divided position has no pairs at all, which is why the
     * single-position coverage is measured on its own and not derived from this.
     */
    private static PartitionEvidence.PairSpace pairsOf(String behavior,
                                                      Readings readings, boolean asked,
                                                      souther.compiler.partition.AdequacyPolicy
                                                              .OfTheMeasures budget,
                                                      BodyInputReading body) {
        // Every measure a row is placed at, which is the locations above flattened rather than a
        // list somebody gathered beside them. A pair is between two positions, so this question is
        // the one that reads across them.
        List<Readings.AxisReading> read = readings.everyAxis();
        List<Axis> axes = read.stream().map(Readings.AxisReading::axis).toList();
        // The product of what a row can be written at, not of what the types declare. A case the
        // rules refuse is not a class of its position at all, so the slice of the product it would
        // have taken part in is not here to be counted — which is a different thing from a pair
        // whose two classes each have rows but never together.
        //
        // And a pair no value is in is not one either. A position under one case of a sum and a
        // position under another are not in one value, so their classes make no combination: counted
        // as the product, the measure of a behavior taking a sum would fall by however many
        // combinations the model does not have.
        //
        // Kept as the pairs they were worked out between, rather than added up here. Which two
        // positions a combination is between is what the walk knows at the moment it counts, and a
        // sum is the one projection of that from which no reader can get it back.
        // Over the positions the body says something about ({@link
        // BodyDistinction#makesCombinations}). A position nothing in the body is about answers the
        // same however the other one moves, so the product of it with anything asks for a row that
        // shows nothing the two rows apart do not.
        //
        // And of those, only the classes some run reads together ({@link ReadTogether}). Two
        // positions read on ways no run takes both of are told apart by the body each, and a row
        // combining them shows nothing the rows apart do not either.
        boolean[] combining = new boolean[axes.size()];
        for (int i = 0; i < axes.size(); i++) {
            combining[i] = toldApartAt(body.distinctions(), axes.get(i)).makesCombinations();
        }
        // Listed while there are no more of them than this compilation counts off the rows, and
        // counted past that: the number is exact either way, and a list nobody walks is not kept.
        List<OwedBetween> owed = new ArrayList<>();
        ClassCoexistence among = ClassCoexistence.among(axes);
        long total = 0;
        for (int i = 0; i < axes.size(); i++) {
            if (!combining[i]) {
                continue;
            }
            for (int j = i + 1; j < axes.size(); j++) {
                if (!combining[j]) {
                    continue;
                }
                OwedBetween between = owedBetween(among, body.together(), axes, i, j,
                        budget.pairSpace() - total);
                total += between.count();
                if (between.count() > 0) {
                    owed.add(between);
                }
            }
        }
        if (owed.isEmpty()) {
            return PartitionEvidence.PairSpace.NONE;
        }
        boolean listed = total <= budget.pairSpace();
        List<PartitionEvidence.PairSpace.AxisPair> space = new ArrayList<>();
        for (OwedBetween each : owed) {
            space.add(new PartitionEvidence.PairSpace.AxisPair(each.between(), listed
                    ? new PartitionEvidence.PairSpace.Owed.Listed(List.copyOf(each.cells()),
                            each.kept())
                    : new PartitionEvidence.PairSpace.Owed.Counted(each.count())));
        }
        // Before anything about the rows, because there are none to be about: a build that asked for
        // no measurement read no row, and what the model holds stays what the model says it is.
        if (!asked) {
            return PartitionEvidence.PairSpace.notAsked(space);
        }
        // Before the size of the space is worth mentioning. A combination nothing tried to sit in is
        // not a combination left untried by anybody, and how many of them there are says nothing
        // about a behavior no row names.
        if (readings.noRows() && !readings.someRowsUnseen()) {
            return PartitionEvidence.PairSpace.noRows(space);
        }
        if (!listed) {
            return PartitionEvidence.PairSpace.truncated(behavior, space, total,
                    WorkFigure.PAIRS_OF_CLASSES_COUNTED.at(budget.pairSpace()));
        }
        // One set of combinations per relation, in the order the relations were worked out. What is
        // counted is the same as it was; where the count goes is what changed.
        SequencedMap<PartitionEvidence.PairSpace.Between,
                Map<PartitionEvidence.PairSpace.Cell, RowWitnesses.Gathering>> reached =
                new LinkedHashMap<>();
        space.forEach(pair -> reached.put(pair.between(), new LinkedHashMap<>()));
        // Which relation each pair of positions is, worked out once. Which two positions they are
        // does not turn on the row, and made inside the walk over the rows it is a name built and
        // thrown away for every row the behavior has.
        Map<Long, ReachedBetween> byPositions = new LinkedHashMap<>();
        for (OwedBetween each : owed) {
            byPositions.put((long) each.one() * axes.size() + each.other(), new ReachedBetween(
                    each.between(), each.cells(), reached.get(each.between())));
        }
        for (Readings.WhereARowSat where : readings.byRow()) {
            for (int i = 0; i < axes.size(); i++) {
                for (int j = i + 1; j < axes.size(); j++) {
                    ReachedBetween at = byPositions.get((long) i * axes.size() + j);
                    if (at == null) {
                        continue;
                    }
                    // Every pairing the row reaches, and only those. A row whose list holds
                    // elements either side of a line stands in both classes there, and which of
                    // them went with what the position beside it holds is settled by which element
                    // each came from — taken as every combination, a row is evidence for a pair
                    // none of its elements is in.
                    for (Map.Entry<String, String> pair : Classification.pairsOf(
                            where.at().get(i), where.at().get(j))) {
                        // Which classes, within the relation that holds them. The relation is the
                        // key above and a class id is unique within its axis, so what is written
                        // here needs to tell two combinations of these two positions apart and no
                        // more. Counted only where it is owed: a row in a combination no run
                        // reads together reached nothing anybody asked for.
                        PartitionEvidence.PairSpace.Cell cell =
                                new PartitionEvidence.PairSpace.Cell(
                                        at.between(), pair.getKey(), pair.getValue());
                        if (at.owed().contains(cell)) {
                            at.cells().computeIfAbsent(cell, _ -> new RowWitnesses.Gathering())
                                    .add(where.by());
                        }
                    }
                }
            }
        }
        SequencedMap<PartitionEvidence.PairSpace.Between,
                Map<PartitionEvidence.PairSpace.Cell, RowWitnesses>> found = new LinkedHashMap<>();
        reached.forEach((between, cells) -> found.put(between, RowWitnesses.Gathering.done(cells)));
        PartitionEvidence.PairSpace.CoveredBetween made =
                new PartitionEvidence.PairSpace.CoveredBetween(found);
        WeakeningSet by = readings.weakening(read);
        return new PartitionEvidence.PairSpace(space, by.isEmpty()
                ? new Measurement.Complete<>(made) : new Measurement.Partial<>(made, by));
    }

    /**
     * What the body tells apart at {@code axis}, which every measure handed to this was read for.
     *
     * <p>Refused rather than taken as unknown where it is missing. The answer was read off the same
     * axes this walks, so a measure it has nothing for is one this was handed from somewhere else.
     */
    private static BodyDistinction toldApartAt(Map<AxisId, BodyDistinction> toldApart,
                                               Axis axis) {
        BodyDistinction at = toldApart.get(axis.id());
        if (at == null) {
            throw new IllegalArgumentException("`" + axis.id() + "` is a measure nothing read"
                    + " what the body tells apart at");
        }
        return at;
    }

    /**
     * The combinations two positions' classes owe a row for: those some run reads together, of
     * classes that can be in one value.
     *
     * <p>Which two classes can be in one value is {@link ClassCoexistence}'s answer and which a run
     * reads together is {@link ReadTogether}'s, both asked here once. The list made here is what
     * the space holds, and the count, what the rows reached and what is left are all read off it —
     * so what is counted and what a row is asked for come from one reading rather than from two
     * that agree until a case is added.
     *
     * @param room how many may be listed; past that they are counted and not listed
     */
    private static OwedBetween owedBetween(ClassCoexistence among, ReadTogether together,
                                           List<Axis> axes, int one, int other, long room) {
        Axis ones = axes.get(one);
        Axis others = axes.get(other);
        PartitionEvidence.PairSpace.Between between =
                new PartitionEvidence.PairSpace.Between(ones.id(), others.id());
        SequencedSet<PartitionEvidence.PairSpace.Cell> cells = new LinkedHashSet<>();
        List<String> oneClasses = ones.classes().stream().map(PartitionClass::id).toList();
        List<String> otherClasses = others.classes().stream().map(PartitionClass::id).toList();
        // A class of the first at a time, so that what is made to answer is one row of the
        // combinations and not all of them.
        ReadTogether.Between read = together.between(ones.id(), oneClasses, others.id(),
                otherClasses);
        Map<PartitionEvidence.PairSpace.Cell, List<WhyKept>> kept = new LinkedHashMap<>();
        long count = 0;
        for (int here = 0; here < oneClasses.size(); here++) {
            BitSet readWith = read.readWith(here);
            // Asked once for the row, where one of it is listed.
            Map<Integer, Set<WhyKept>> keptWith = null;
            for (int there = readWith.nextSetBit(0); there >= 0;
                    there = readWith.nextSetBit(there + 1)) {
                if (!among.canHoldTogether(one, here, other, there)) {
                    continue;
                }
                String oneClass = oneClasses.get(here);
                String otherClass = otherClasses.get(there);
                count++;
                if (count <= room) {
                    PartitionEvidence.PairSpace.Cell cell =
                            new PartitionEvidence.PairSpace.Cell(between, oneClass, otherClass);
                    cells.add(cell);
                    if (keptWith == null) {
                        keptWith = read.keptWith(here);
                    }
                    Set<WhyKept> why = keptWith.get(there);
                    if (why != null) {
                        kept.put(cell, List.copyOf(why));
                    }
                }
            }
        }
        return count <= room
                ? new OwedBetween(one, other, between, count, cells, kept)
                : new OwedBetween(one, other, between, count, new LinkedHashSet<>(), Map.of());
    }

    /**
     * The combinations of one relation a row is owed for, and how many there are.
     *
     * @param one   which of the positions walked the relation's first is
     * @param other which its second is
     * @param cells each of them, where there are no more than could be listed; empty past that
     * @param kept  what kept each of {@code cells} that no way of the body read whole reads
     */
    private record OwedBetween(int one, int other, PartitionEvidence.PairSpace.Between between,
                               long count, SequencedSet<PartitionEvidence.PairSpace.Cell> cells,
                               Map<PartitionEvidence.PairSpace.Cell, List<WhyKept>> kept) {
    }

    /**
     * One relation of two positions, beside the combinations of it owed and those the rows have
     * reached.
     *
     * <p>Together because the walk over the rows wants them at once, and which relation a position
     * and the one beside it make does not turn on the row. Looked up separately, the relation is
     * fetched again for every combination every row is in.
     */
    private record ReachedBetween(PartitionEvidence.PairSpace.Between between,
                                  Set<PartitionEvidence.PairSpace.Cell> owed,
                                  Map<PartitionEvidence.PairSpace.Cell,
                                          RowWitnesses.Gathering> cells) {
    }

    /**
     * The questions the rules of this behavior's inputs raise that nothing answered, as a document
     * says them.
     *
     * <p>Once, off the partitioning, and not once per axis. The model raises them and an axis is
     * one reader of them: a position no axis came back for still has whatever was written about it,
     * and an axis is re-pointed at another number as a body's rules are read, so a question found
     * beside one is not thereby a question about the number that axis ended up measuring.
     */
    private static List<PartitionEvidence.Unanswered> unansweredIn(
            souther.compiler.partition.Partitions.Partitioning partitioning) {
        return partitioning.unanswered().stream()
                .map(PartitionEvidence.Unanswered::new)
                .toList();
    }

    /**
     * Whether one standing question is one this axis is a reader of.
     *
     * <p>Applicability and not ownership. Both sides name what they are about in the same
     * vocabulary and the comparison is between those two names — which is a different thing from
     * recovering the question's subject from what the axis happens to be measured at.
     */
    private static boolean appliesTo(StandingQuestion asked, Axis axis) {
        return switch (asked) {
            case StandingQuestion.Exact one -> switch (one.asks()) {
                case InputQuestion.AboutAPosition it -> it.path().equals(axis.path());
                case InputQuestion.AboutANumber it -> it.about().equals(axis.subject());
            };
            // Where the reader was sent, which is what such a question has instead of a subject.
            // A measure of the place a rule was filed at is a reader of it: nothing worked out what
            // the rule states there, so what this axis says about the place rests on it.
            case StandingQuestion.Unclassified one -> switch (one.at()) {
                case FilingCoordinate.AtPosition it -> it.path().equals(axis.path());
                case FilingCoordinate.OfTerm it -> it.term().equals(axis.term());
            };
        };
    }



    private static PartitionEvidence.AxisCoverage coverageOf(Readings.AtPosition where,
            Readings.AxisReading reading, Readings readings,
            souther.compiler.partition.Partitions.Partitioning partitioning,
            boolean asked, BodyDistinction toldApart, InputUse use) {
        Axis axis = reading.axis();
        souther.compiler.partition.PositionAccount at = where.position().position();
        List<String> classes = axis.classes().stream().map(PartitionClass::id).toList();
        // Which of this position's rules nothing accounted for, each named. Read off the position
        // rather than worked out here, and in the questions' own words: the vocabulary beside it
        // says why a division could not be derived, which is a different question, and borrowing it
        // left a reader with a sentence that named neither.
        PartitionEvidence.AxisCoverage.Reading read = new PartitionEvidence.AxisCoverage.Reading(
                at.residue().rulesLeftUnread().isEmpty()
                        ? PartitionEvidence.AxisCoverage.Reach.EVERY_RULE
                        : PartitionEvidence.AxisCoverage.Reach.SOME_OUT_OF_SIGHT,
                // Of the questions standing at this position, the ones this measure is the reader
                // of. What classes are made of is which values may stand somewhere; where the line
                // falls is the border measure's question, and counting it here would put a number
                // #869 separated back together. The questions themselves are beside the measures
                // and are said there once.
                partitioning.unanswered().stream()
                        .filter(each -> appliesTo(each, axis))
                        .noneMatch(each -> each.holdsOpen(
                                CoverageObligation.Measure.PARTITION)));
        // Nothing a body claims is in scope here. What a row is owed at is counted first and on its
        // own, and what was declared about those positions is put beside it afterwards
        // ({@link ClaimReport}) — which is what keeps a claim from narrowing a denominator by being
        // in reach of the code that counts one.
        // Which classes there are is the model's answer and is above; what the rows reach of them is
        // below, and a build that asked for no measurement read no row.
        if (!asked) {
            return PartitionEvidence.AxisCoverage.notAsked(axis.id(),
                    axis.term().toString(), classes, axis.divides(), toldApart, use, read);
        }
        if (readings.noRows() && !readings.someRowsUnseen()) {
            return PartitionEvidence.AxisCoverage.noRows(axis.id(),
                    axis.term().toString(), classes, axis.divides(), toldApart, use, read);
        }
        PartitionEvidence.AxisCoverage.Reached reached =
                new PartitionEvidence.AxisCoverage.Reached(reading.covered(),
                        reading.couldNotSay());
        WeakeningSet by = readings.weakening(List.of(reading));
        return new PartitionEvidence.AxisCoverage(axis.id(), axis.term().toString(),
                classes, axis.divides(), toldApart, use, read, by.isEmpty()
                        ? new Measurement.Complete<>(reached)
                        : new Measurement.Partial<>(reached, by));
    }

    /**
     * A way to find out whether a value can be built at a boundary, or nothing where there is nothing
     * to build against.
     *
     * <p>The decoder a row's own fixture goes through, reached through the generator. It is the only
     * thing in the compiler that can answer the question — an invariant relating two fields refuses a
     * pair each field would have accepted alone — and it answers it one way: what it builds is a
     * witness, and what it refuses is a refusal of the candidates it tried.
     */
    interface Probe {

        /**
         * What building a row for {@code label} came to, with each position of the item fixed
         * where {@code fixing} puts it and the rest of the row built to reach the border, and
         * empty where the attempt could not be made at all — which leaves the point unknown rather
         * than refused.
         *
         * <p><b>One attempt per way of standing the dependencies in.</b> A behavior whose union
         * answer the demands leave open has a value of each case to be stood up with, and which of
         * them a row carries decides where the row goes — so whether a row reaches this item is
         * whether any of them does. Which of the ones that reach it is offered is the caller's, and
         * is a choice between rows that each answer what was asked.
         *
         * <p>One method, whatever the border was drawn on. What the row is for is the coverage item
         * and what is fixed to build it is a placement that stands for it; a side of a border is met
         * by a row anywhere in it, so a row labelled by the places a search happened to compose
         * would name a witness as though it were the item.
         *
         * <p>What each position's number is measured on is not among the arguments. That is the
         * reading the row is composed against, which the generator holds; passed in, a caller would
         * be answering a question about where a term stands from wherever it found the term.
         *
         * @param reaching what the row has to be to arrive at the border at all. Handed in beside
         *                 the placement rather than left out: the placement is about the positions
         *                 the item names and a condition above the line is about the others, and a
         *                 row is one row
         * @param asking   what the item leaves each of the numbers {@code fixing} names one of,
         *                 which is what a search coming back empty-handed said something about.
         *                 Beside the places and not read off them: a place is what this search
         *                 settled on, and the item it was taken out of holds every number the rules
         *                 leave beside it
         * @param demands  what the thing being searched for asks of the dependencies the behavior
         *                 requires. Part of the request and not of the probe, because it is what
         *                 differs between the things one behavior is searched for: a point of a
         *                 line asks nothing of them, and a rule of the decision asks what the body
         *                 read. Held by the probe, a search would compose its row under whatever
         *                 the behavior answers generally and be run under what it actually needs
         */
        default java.util.List<souther.compiler.partition.Generator.BoundaryAttempt> attempt(
                String label,
                Map<souther.compiler.partition.RealizationTarget, Place> fixing,
                souther.compiler.partition.NumbersAskedFor asking,
                souther.compiler.partition.Reachability.Reaching reaching,
                souther.compiler.partition.AnswersDemanded demands) {
            return attempt(label, fixing, asking, reaching, demands, java.util.Optional.empty());
        }

        /**
         * The same, with each row composed held to {@code judge} besides the way, inside the walk
         * that composes it. For what a way cannot say and only a run does, such as a case a search
         * draws inside itself: a row the judge refuses is passed over and the walk goes on to the
         * next, so what comes back is a row the judge accepted or none.
         */
        java.util.List<souther.compiler.partition.Generator.BoundaryAttempt> attempt(
                String label,
                Map<souther.compiler.partition.RealizationTarget, Place> fixing,
                souther.compiler.partition.NumbersAskedFor asking,
                souther.compiler.partition.Reachability.Reaching reaching,
                souther.compiler.partition.AnswersDemanded demands,
                java.util.Optional<souther.compiler.partition.Generator.RowJudge> judge);

        /**
         * A composed row built and run, so that what it turned out to be can be asked.
         *
         * <p>The same reading a written row goes through ({@link RowAsRead}). A candidate is a row
         * nobody has been handed yet and is otherwise a row like any other, so what it stands at is
         * read by the walk that reads the file's rows and never by a second account written where
         * the candidate was composed.
         */
        RowAsRead read(souther.compiler.partition.RowToRun row);

        /** What the rows built and run here are written against: their parameters and the
         *  decoder every value put in a row besides the ones a search composed is held to. */
        souther.compiler.partition.RowWriting rowWriting();
    }

    /**
     * Everything known about each line one position's rules drew.
     *
     * <p>The one place either question about a boundary is answered. Whether a row sits at it is read
     * off this compilation's rows; whether a row could sit at it is settled by the projection where
     * that read every rule, and by building a value where it did not. Both used to be worked out twice
     * — once for the report and once for the rows the generator offers — under rules that did not
     * quite agree, so a line the report called undecided was one the generator handed to an author
     * anyway.
     *
     * <p>An invariant's bound is met by writing the value: outside it nothing can be constructed, so
     * the value is the whole of what there is to reach. A guard's is not — the comparison has to have
     * been evaluated, and a row can carry the exact value and never reach the guard that cares about
     * it because an earlier branch went the other way. Nothing measures that until the arms are
     * instrumented, so a guard's boundary is unmeasured rather than met or missed.
     *
     * <p>Whether the build asked for the arms at all and whether the run then managed to read them
     * are two questions, and {@code observed} answers the second — the two fail differently, and a
     * measure that took one answer for both could not say which had happened.
     *
     * <p>What a row had already satisfied when each comparison ran is threaded here as well as into
     * {@link #assessBetween}, because which shape of quantity a rule cuts says nothing about where a
     * row for it may be written — and a region put into one of the two paths would leave the other
     * searching over everything its position could ever hold. No model was found where it moves an
     * answer down this path, and no test holds it: the points of a line at one position all sit
     * beside the line, and every line tried that the region excludes turned out to be one
     * {@link souther.compiler.check.PathReachability} had already taken the obligation away for.
     * Whether those two always coincide is not established here — they are different readings — so
     * what this says is that a path is not left short of what it is owed, and not that the region is
     * idle here.
     */
    static List<ReadingOfALine> assess(
            List<Border> lines, souther.compiler.partition.MeasuredInput subject,
            souther.compiler.query.Adequacy.RowReading observed,
            Function<Border, ItemAssessment.WritabilityProjection> projection,
            RowsPutToTheLines put, ReachingCuts reaching) {
        // One entry per reading and not per line. A guard inside a non-recursive helper is read once
        // per call of that helper, and the rows do not owe the same border twice for having been
        // offered it twice — but each reading is reached under its caller's own conditions, so what
        // a row for it may be composed out of is the reading's and is settled while the readings are
        // still apart. What the lines beside it are is asked of every reading of it at once
        // ({@link #besideEachLine}), and the readings are brought together by {@link #merged}.
        List<ReadingOfALine> out = new ArrayList<>();
        MeasuredInput.Lines read = subject.lines();
        for (Border each : lines) {
            out.add(assessed(each, reading(read.at(each), projection.apply(each),
                            elsewhere(lines, each),
                            wayTo(each, reaching), subject.quantities().region()),
                    observed, put));
        }
        return List.copyOf(out);
    }

    /**
     * The behavior's other lines, read as the inequalities they are.
     *
     * <p>For naming an input worth writing a row at. Where the model's other rules leave a row is
     * where this line is what settles the answer, so an input the others keep is one an author can
     * see the difference at — and one they refuse is a row two lines part company at and the
     * behavior answers the same way either side of.
     *
     * <p>A preference and never a condition. Which rules a path actually consults is the decision's
     * question and is measured there; what this does with the answer is choose between inputs that
     * are each already an input the two lines part company at.
     */
    private static List<souther.compiler.partition.OrderedAffineBoundary> elsewhere(
            List<Border> lines, Border but) {
        List<souther.compiler.partition.OrderedAffineBoundary> out = new ArrayList<>();
        for (Border each : lines) {
            if (each.sameReadingAs(but)) {
                continue;
            }
            // A rule that names a value orders nothing, and a line whose values beside it were not
            // worked out has no inequality to offer: either leaves this list a line shorter, which
            // is the preference it is. Each of the two lines is told what it lacked by its own
            // border, so nothing is said here.
            ExactAnswer<Optional<OrderedAffineBoundary>> drawn = OrderedAffineBoundary.of(each);
            if (drawn instanceof ExactAnswer.Held<Optional<OrderedAffineBoundary>> held) {
                held.value().ifPresent(out::add);
            }
        }
        return out;
    }

    /**
     * The same lines, with what building a value at each point that is worth one came to.
     *
     * <p>Takes what was measured rather than measuring again. A search is evidence added to an
     * assessment and never a second one: the border, what it demands, whether a row is at it and
     * whether the rules prove it writable are all carried through untouched, and the only thing this
     * puts in is the attempt at the points the measurement itself says are worth an attempt.
     *
     * <p>Which is what makes composing later safe to do. What shows a point writable is read off the
     * evidence, and nothing a search finds is evidence against a point — so this can add a ground and
     * can never take one away, whenever it is run and however many points it is run over.
     */
    static LineReadings searched(LineReadings measured,
                                 souther.compiler.partition.MeasuredInput input,
                                 Probe probe, ReachingCuts reaching) {
        LevelRealizer realizer = new LevelRealizer();
        List<BorderAssessment> out = new ArrayList<>();
        MeasuredInput.Lines lines = input.lines();
        for (BorderAssessment border : measured.each()) {
            MeasuredInput.BorderReading read = lines.at(border.border());
            WayToTheBorder way = wayTo(border.border(), reaching);
            OneSearchOfABorder search = searching(border.border(), read, input, probe,
                    realizer, way, false);
            // The way a class the line cuts is looked for along where the walk to the case the
            // line decides in has no value to stand at: the class runs over the whole of the
            // quantity, and the case is only where the line is read. Worked out at the first point
            // that asks, so that a border none of whose points come to that pays for one walk.
            OneSearchOfABorder inTheClasses = null;
            java.util.Map<DomainPoint, ItemAssessment> items = new java.util.LinkedHashMap<>();
            for (DomainPoint point : border.items().keySet()) {
                ItemAssessment item = border.at(point);
                // Each search with the copies the reading it was made for was read at, said here
                // because this is the last place one reading's searches are that reading's alone:
                // the readings of one line are put together next, searches and copies both, and a
                // search stopped at one call would come out stopped at every call of the line.
                if (item instanceof ItemAssessment.Owed owed && owed.worthSearching()) {
                    String label = border.border().label(point);
                    SearchOutcomes outcomes = search.search(owed.criterion(), label);
                    if (!point.againstTheLine() && outcomes.provesInfeasible()) {
                        if (inTheClasses == null) {
                            WayToTheBorder wayToTheClasses =
                                    reaching.wayToTheClassesOf(border.border().origin());
                            inTheClasses = wayToTheClasses.equals(way) ? search
                                    : searching(border.border(), read, input, probe, realizer,
                                            wayToTheClasses, true);
                        }
                        if (inTheClasses != search) {
                            outcomes = inTheClasses.search(owed.criterion(), label);
                        }
                    }
                    items.put(point, owed.settledBy(outcomes.readAt(border.readAt())));
                } else {
                    items.put(point, item);
                }
            }
            // And who put on the way what the search went along, which is what says at which calls
            // of a helper a reader meets what the search went without.
            // What this reading's own search showed arriving is said of this reading, before its
            // readings are put together: the row that rules a line out was composed along this
            // reading's way and is read back at this reading's positions.
            ARowTellingTheLinesApart toldApart =
                    settled(border.border(), tellingApart(border, search), read);
            out.add(new BorderAssessment(border.border(), items,
                    shownArriving(border.beside(), toldApart), toldApart,
                    border.readAt(), reaching.saidOnTheWayTo(border.border().origin())));
        }
        return new LineReadings(out, measured.tilts());
    }

    /**
     * The same searches, each with a row it composed that was seen run to the rule and, read back,
     * rules its line out ({@link WhatARowRulesOut}), where one did
     * ({@link ARowTellingTheLinesApart.AtOneReading#settledBy}).
     */
    private static ARowTellingTheLinesApart settled(Border reading,
                                                    ARowTellingTheLinesApart toldApart,
                                                    MeasuredInput.BorderReading read) {
        // The line drawn and put to rows once for the border, and only where a search saw a row
        // run there: every search here is one of this reading's.
        boolean drawnYet = false;
        DrawnBoundary drawn = null;
        StandingAtAPoint.AtALine toRows = null;
        List<ARowTellingTheLinesApart.AtOneReading> out = new ArrayList<>();
        for (ARowTellingTheLinesApart.AtOneReading one : toldApart.each()) {
            if (!one.reading().equals(reading)) {
                throw new IllegalStateException("a search of one reading made at another: "
                        + one.reading() + " and " + reading);
            }
            if (one.seenThere().isEmpty()) {
                out.add(one);
                continue;
            }
            if (!drawnYet) {
                drawnYet = true;
                Optional<DrawnBoundary> held = DrawnBoundary.of(reading).orNull();
                if (held != null && held.isPresent()) {
                    drawn = held.get();
                    toRows = StandingAtAPoint.putToRows(read,
                            reading.origin().recordedAt());
                }
            }
            if (drawn == null) {
                out.add(one);
                continue;
            }
            DrawnBoundary line = drawn;
            StandingAtAPoint.AtALine put = toRows;
            out.add(one.settledBy(seen -> {
                WhatARowRulesOut.Said said =
                        WhatARowRulesOut.of(put, line, one.line(), seen.readBack());
                return said.said().settles() ? Optional.of(said.at()) : Optional.empty();
            }));
        }
        return new ARowTellingTheLinesApart(out);
    }

    /**
     * {@code beside} with each line nothing showed an input arriving at put where the rows leave
     * it, where this reading's search composed a row that settles it ({@link #settled}): an input
     * that arrives and tells the two apart, which is the row as it was read back. A row composed
     * and not seen there, or one that arrives and does not rule the line out, leaves the line where
     * it was.
     */
    private static AnotherLineTheRowsAllow shownArriving(
            AnotherLineTheRowsAllow beside, ARowTellingTheLinesApart toldApart) {
        if (!(beside instanceof AnotherLineTheRowsAllow.ByDirection lines)) {
            return beside;
        }
        Map<QuantityKey, Map<NumericTerm, Place>> arriving = new LinkedHashMap<>();
        for (ARowTellingTheLinesApart.AtOneReading one : toldApart.each()) {
            if (one.settling() != null) {
                arriving.putIfAbsent(one.direction(), one.settling().at());
            }
        }
        return arriving.isEmpty() ? beside : lines.shownArriving(arriving);
    }

    /**
     * What looking for a row that rules out each line the rows leave standing beside this one came
     * to, or that nobody asked where none is standing.
     *
     * <p><b>Both sides of the model's line.</b> A row rules a line of the family out where the model
     * refuses it and the line, drawn anywhere the rows allow, keeps it — or where the model keeps it
     * and the line, drawn anywhere the rows allow, refuses it ({@link
     * AnotherLineTheRowsAllow.Stands}). Held to the first, a border whose earlier rules leave
     * nothing on that side would be searched where nothing is, and a search of an unbounded region
     * cannot show that: it would run to its budgets while the input that settles the line stands on
     * the other side.
     *
     * <p>Each side searched on its own and each search kept. What a composed row settles is said
     * once it is read back, where every offered row is weighed, and that is also where a row another
     * one already answers for is dropped.
     *
     * <p><b>The run beside this line, and not one point of it.</b> Read as the point
     * <em>against</em> the line instead, two things went wrong at once: a quantity whose order names
     * no value beside the line has no such point and was never searched, and a level the rules
     * leave nothing at came back as a proof that the model leaves nowhere to write — a proof about
     * one level, published as a proof about every input that settles the line.
     *
     * <p>The run and not the half-space. Where a run beside a line stops is settled by the lines
     * this position's other rules draw, so what this looks through is the values between this line
     * and the next one along — a row past that is decided by a rule that has already decided, and is
     * no row at this border.
     *
     * <p>Asked whether or not a row already stands in there. A row at a point shows the line has
     * not moved and says nothing about which way it runs, which is what raised this question: the
     * points being met is what makes the question due rather than what answers it.
     *
     * <p>And for each line the rows leave where nothing showed an input arriving
     * ({@link AnotherLineTheRowsAllow.ByDirection#lookedFor}): a row composed there and run is what
     * may show one.
     */
    private static ARowTellingTheLinesApart tellingApart(BorderAssessment border,
                                                         OneSearchOfABorder search) {
        if (!(border.beside() instanceof AnotherLineTheRowsAllow.ByDirection lines)
                || lines.lookedFor().isEmpty()) {
            return ARowTellingTheLinesApart.notAsked();
        }
        Criterion refused = runBeside(border.border(), false);
        Criterion kept = runBeside(border.border(), true);
        String label = border.border().label();
        // Each line searched for on its own. Which lines a row composed here settles is the row's
        // to say once it is read back, and that is asked where every offered row is weighed, in
        // Settlements — which also drops a row another one already answers for.
        List<ARowTellingTheLinesApart.AtOneReading> out = new ArrayList<>();
        for (AnotherLineTheRowsAllow.Stands line : lines.lookedFor()) {
            // Both sides, whatever the first came to. A row composed on one side is a candidate and
            // not yet evidence — it may come back unread, or arrive somewhere that settles nothing
            // — so it is no reason to leave the other side unlooked at; which of the two the block
            // keeps is the offering's to say.
            //
            // Beside a value singled out, the side the value is singled out for is the value
            // itself, which has no run beside the line: a row there is a row at the line.
            Criterion refusedHere = refused == null && line.atOneValue()
                    ? atTheLine(border.border(), false) : refused;
            Criterion keptHere = kept == null && line.atOneValue()
                    ? atTheLine(border.border(), true) : kept;
            //
            // And each region a side names on its own: off a value is below it or above it, and a
            // way that leaves rows on one of the two is looked along that one.
            if (refusedHere != null) {
                for (UnaryOperator<SearchRegion> region : line.onTheRefusedSide()) {
                    out.add(search.tellingApart(refusedHere, label, line, region));
                }
            }
            if (keptHere != null) {
                for (UnaryOperator<SearchRegion> region : line.onTheKeptSide()) {
                    out.add(search.tellingApart(keptHere, label, line, region));
                }
            }
        }
        return new ARowTellingTheLinesApart(out);
    }

    /**
     * The values beside {@code border} on the side the model keeps or on the side it refuses, as
     * one run, or null where the rules leave none there.
     *
     * <p>Asked of the point that is in that run rather than worked out here. Where a run beside a
     * line stops is settled by every other rule reaching this position, and a second derivation of
     * it would be free to stop somewhere else — which is the one thing a search may not be wrong
     * about, because a walk of the whole of it is what proves there is nowhere to write.
     *
     * <p>The value against the line goes back in. The point out there names the run less that
     * value, because a row there is what that point is for and the value against the line is what
     * the point beside it is for; a line of the family is not divided that way, and a search that
     * left it out would pass over the nearest input that settles it.
     */
    private static Criterion runBeside(Border border, boolean kept) {
        for (DomainPoint point : border.answers().keySet()) {
            if (point.againstTheLine() || border.roleOf(point).inside() != kept) {
                continue;   // on the line, or on the other side of it
            }
            if (border.demand(point) instanceof Demand.Owed owed
                    && owed.criterion() instanceof Criterion.Within in) {
                return new Criterion.Within(in.band(), null, in.away());
            }
        }
        return null;
    }

    /** What a row at {@code border}'s line on the side {@code kept} says is owed, or null where no
     *  point at the line on that side is owed one. */
    private static Criterion atTheLine(Border border, boolean kept) {
        for (DomainPoint point : border.answers().keySet()) {
            if (point.againstTheLine() && border.roleOf(point).inside() == kept
                    && border.demand(point) instanceof Demand.Owed owed) {
                return owed.criterion();
            }
        }
        return null;
    }

    /**
     * How a row for one border came to be looked for where it is.
     *
     * <p>Beside the border and not part of it. What a border is is what the rows are owed at, and it
     * is the same border wherever a row for it is looked for — put inside, two readings of one line
     * reached under different conditions would be two obligations, and a count of what an author
     * owes would move with how much of a body this compiler managed to read.
     *
     * <p>Nothing on the way, for a line a declaration draws. An invariant is about the values and
     * holds wherever one stands, so there is nowhere for a row to have come from; a guard is at a
     * place in a body, and a row that never arrives there is no row at its line whatever it holds.
     * Read off which kind of rule it is rather than off whether anything was collected: a guard
     * nothing narrows and a clause then say the same thing for the same stated reason, and each says
     * it in its own account rather than by coming back with nothing.
     */
    private static WayToTheBorder wayTo(Border border, ReachingCuts reaching) {
        return reaching.wayTo(border.origin());
    }

    /**
     * What differs between the two shapes of border when a point of one is assessed.
     *
     * <p>Three answers and no more. How a row is read is one — at a position's own term, or at both
     * terms of a line between two — what a search does is another, and whether the rules alone prove
     * a row can be written at this border is the third. Everything else about a point is the same
     * either way, and writing it out per shape is what let one shape acquire a rule the other had:
     * the gates before a search were asked twice and a third search went in beside them without
     * them.
     */
    private interface OneShapeOfBorder {

        /** Whether one of {@code rows} meets {@code criterion}, and whether that could be told. */
        StandingAtAPoint.Met met(Criterion criterion, List<ObservedInputs> rows);

        /** What the lines beside this one are asked of at this reading: those same rows, read
         *  through the same walk over them, and the way they took here. */
        AnotherLineTheRowsAllow.Reading beside(List<ObservedInputs> rows);

        /** What the readings of {@code rows} that stand at {@code criterion}'s point read as. */
        StandingAtAPoint.RowsRead valuesAt(Criterion criterion, List<ObservedInputs> rows);

        /** What reading the rules this reading took in established about a row being writable at
         *  this border. Three answers rather than two: a shape whose rules were never put the
         *  question is not one whose rules failed to answer it. */
        ItemAssessment.WritabilityProjection projection();
    }

    /** What building a row at one point of a border comes to. Its own interface beside the reading
     *  above, because searching is not measuring: one is what this compilation already established
     *  and the other is work somebody asked for. */
    private interface OneSearchOfABorder {

        /**
         * What building a row at it came to, asked only where one is worth building.
         *
         * <p>What each way of standing the dependencies in came to, and not one of them. A way that
         * leaves the case of a union answer open is several rows, each going where the case it
         * carries takes it, and what they came to is as many pieces of news as there are of them:
         * one held back by a figure of this compiler's and one that composed nothing are not each
         * other's representatives ({@link SearchOutcomes}). Answered with one, the point would
         * carry whichever way was tried first.
         */
        SearchOutcomes search(Criterion criterion, String label);

        /**
         * What looking for a row that rules out {@code direction} on one side of this line came to.
         *
         * <p>{@code criterion} is the run on that side, and {@code narrowing} is where on it a row
         * rules the line out ({@link AnotherLineTheRowsAllow.Stands}) — so nothing here has to be
         * told which places the rows already stand at: a row in the file is outside that region by
         * the same arithmetic that left the line standing.
         */
        ARowTellingTheLinesApart.AtOneReading tellingApart(Criterion criterion, String label,
                                                           AnotherLineTheRowsAllow.Stands line,
                                                           UnaryOperator<SearchRegion> narrowing);
    }

    /**
     * One behavior's rows as every line of it is put to them, read once for all of its lines.
     *
     * <p>What a row holds and what running it recorded do not turn on the line, so reading them
     * again for each line was the same work once per line the behavior has. The rows that are not
     * ones that do not hold are set apart here too, since a point is first asked of them alone
     * wherever there are any of the others.
     *
     * @param all        every row, in the order the reading holds them
     * @param notHolding the rows among them that do not hold
     * @param others     the values of every other row, which is {@code all}'s where there are none
     */
    record RowsPutToTheLines(List<ObservedInputs> all, List<WitnessedRow> notHolding,
                             List<ObservedInputs> others) {

        static RowsPutToTheLines of(Adequacy.RowReading observed,
                                    Optional<SiteNumbering> numbering) {
            List<ObservedInputs> all = new ArrayList<>();
            List<WitnessedRow> notHolding = new ArrayList<>();
            List<ObservedInputs> others = new ArrayList<>();
            for (RowOutcome row : observed.rowsSeen()) {
                WitnessedRow read = WitnessedRow.of(row, numbering);
                all.add(read.observed());
                if (read.by().anotherRow()) {
                    others.add(read.observed());
                } else {
                    notHolding.add(read);
                }
            }
            return new RowsPutToTheLines(List.copyOf(all), List.copyOf(notHolding),
                    notHolding.isEmpty() ? List.copyOf(all) : List.copyOf(others));
        }
    }

    /**
     * What each of one border's four points came to.
     *
     * <p>Every role, and the ones nobody is owed a row in carry the border's own reason rather than
     * being left out. What a row has to do is the criterion's ({@link Criterion}); what it has to do
     * <em>beyond</em> that is the border's — a line a fork of a body drew is met by getting the
     * comparison to answer as well as by writing the value, and that holds of all four of its points.
     * Read off the role instead, an {@code IN} point of a guard would be met by a row that never
     * reached the guard.
     *
     * <p>One place, for both shapes of border. Which of the four a build is told about, whether a
     * point is worth building a candidate for, and what a point that owes no row carries are rules
     * about a point and not about a shape, so a shape added later inherits them rather than being
     * trusted to repeat them.
     */
    private static ReadingOfALine assessed(Border border, OneShapeOfBorder shape,
                                           souther.compiler.query.Adequacy.RowReading observed,
                                           RowsPutToTheLines put) {
        // Whether meeting this border takes the comparison having run, asked of the rule rather than
        // read off which kind it is, and asked once for the border rather than once per point. A
        // guard's line is about a place in a body and is reached or not; an invariant's and a
        // clause's are about the values — one refuses everything outside its bound, the other states
        // a relation — so for both of those writing the value is the whole of what there is to reach.
        boolean guard = border.origin().comparisonAt().isPresent();
        Measurement<ItemAssessment.Coverage> absent =
                whyNothingWasReadAgainstTheLine(guard, observed);

        // The rows as the values they hold and what running them recorded, which is the whole of
        // what a point is met by. Read once for every line of the behavior.
        List<ObservedInputs> rows = put.all();

        java.util.Map<DomainPoint, ItemAssessment> items = new java.util.LinkedHashMap<>();
        for (DomainPoint point : border.answers().keySet()) {
            items.put(point, switch (border.demand(point)) {
                case Demand.NotOwed not -> new ItemAssessment.NotOwed(not.reason());
                case Demand.NotWorkedOut not -> new ItemAssessment.NotWorkedOut(not.why());
                case Demand.Owed owed -> {
                    Measurement<ItemAssessment.Coverage> coverage = absent != null ? absent
                            : standingAt(shape, owed.criterion(), put, guard, border, observed);
                    // No search. Nothing was searched for here, and that is said by there being no
                    // search rather than by a search saying nobody asked: whether a value was
                    // composed is a fact about who asked for one, and a measurement that carried it
                    // was answering a question it had not been put.
                    yield new ItemAssessment.Owed(owed.criterion(), coverage,
                            shape.projection(), SearchOutcomes.none());
                }
            });
        }
        // And what the lines beside it are asked of here: the same rows and the same reading of the
        // line as the points above. A row at each of the four shows the line has not moved, and
        // nothing about the four shows it has not turned.
        // The weights of a derived value are fixed by the rows read against it, so a reading
        // nothing was read against says nothing of them.
        return new ReadingOfALine(border, items, absent, shape.beside(rows),
                // Only the rows that hold: one whose answer is not the model's says nothing of the
                // model, and a weight is not fixed by what is not evidence of it.
                absent == null ? tiltReading(border, items, shape, put.others())
                        : Optional.empty());
    }

    /**
     * The border as the rows are put to it for the weights of the value it cuts, or none where it
     * cuts no value derived from several positions.
     *
     * <p>A row is on the border where it meets the point a row is owed at to show where the line
     * falls, which the border says as it says it for every other reader of that point. Whether
     * some row does is already the answer the points above came to, so a border no row is on is
     * not put to the rows again: only a border some row is on is asked which.
     */
    private static Optional<TiltOfADerivedValue.Reading> tiltReading(
            Border border, Map<DomainPoint, ItemAssessment> items, OneShapeOfBorder shape,
            List<ObservedInputs> rows) {
        Optional<LinearQuantity> form = border.cut().of().derivedFromSeveralPositions();
        if (form.isEmpty()) {
            return Optional.empty();
        }
        List<Criterion> near = new ArrayList<>();
        boolean someRowIsOn = false;
        boolean pointsRead = true;
        boolean allWorkedOut = true;
        // What the points nearest the line went without, as their own measurements say it. The
        // owner of that is the point's assessment, so it is asked of it on every way out of here
        // and not rebuilt from the flags below, which keep whether and lose why.
        WeakeningSet pointsWentWithout = WeakeningSet.none();
        for (DomainPoint point : border.answers().keySet()) {
            // The values nearest the line on each side, which is where a row shows the line has not
            // moved; a run away from it shows nothing of that.
            if (!border.roleOf(point).againstTheLine()) {
                continue;
            }
            pointsWentWithout = pointsWentWithout.union(items.get(point).weakening(border));
            switch (border.demand(point)) {
                case Demand.Owed owed -> {
                    near.add(owed.criterion());
                    ItemAssessment.Owed measured = (ItemAssessment.Owed) items.get(point);
                    someRowIsOn |= measured.coverage().made()
                            .filter(ItemAssessment.Coverage.Hit.class::isInstance).isPresent();
                    // That no row is at the point is the whole of what there is to say only where
                    // the rows were all read, which the point's own measurement says.
                    pointsRead &= measured.coverage() instanceof Measurement.Complete;
                }
                // A point that could not be worked out may have rows nobody can name.
                case Demand.NotWorkedOut _ -> {
                    pointsRead = false;
                    allWorkedOut = false;
                }
                case Demand.NotOwed _ -> { }
            }
        }
        boolean rowsAreOn = someRowIsOn;
        boolean noRowIsOnAndTheyWereRead = pointsRead;
        boolean pointsWorkedOut = allWorkedOut;
        WeakeningSet nearWentWithout = pointsWentWithout;
        // The rule is the border's own and is read against the model's weights in the quantity's own
        // units, which is the family E1938 holds a border against. A border that reads as no rule
        // of that kind has no rule to put a changed computation to, and says so by being incomplete.
        Optional<OrderedAffineBoundary> boundary = OrderedAffineBoundary.of(border).orNull();
        if (boundary == null || boundary.isEmpty()) {
            return Optional.of(new TiltOfADerivedValue.Reading(border,
                    () -> TiltOfADerivedValue.RowsOnABorder.unread(nearWentWithout)));
        }
        OrderedAffineBoundary rule = boundary.get();
        Map<NumericTerm, ExactRatio> weights = rule.direction().direction();
        // A reading that holds no number at one of the weighed positions says nothing of the rule.
        TiltOfADerivedValue.Rule weighed = (changed, values) -> values.keySet()
                .containsAll(changed.keySet())
                ? Optional.ofNullable(rule.satisfiesWeighing(changed, values).orNull())
                : Optional.empty();
        return Optional.of(new TiltOfADerivedValue.Reading(border, () -> evidenceOn(weights, weighed,
                rowsAreOn ? readAt(border, near, shape, rows)
                        : StandingsRead.ofNoRow(noRowIsOnAndTheyWereRead),
                nearWentWithout, pointsWorkedOut)));
    }

    /**
     * What the rows on one border say of the weights, made in one place for every way the rows
     * were or were not read.
     *
     * <p>Whether a border was read in full and why it was not are one fact, and a flag per way out
     * of reading it keeps the first and loses the second. So what the points nearest the line went
     * without is joined here, to what reading the rows at them went without, whichever of the two
     * ways the rows came by.
     *
     * @param nearWentWithout what the points nearest the line went without, by their own
     *                        assessments
     */
    static TiltOfADerivedValue.RowsOnABorder evidenceOn(
            Map<NumericTerm, ExactRatio> weights, TiltOfADerivedValue.Rule rule,
            StandingsRead read, WeakeningSet nearWentWithout, boolean pointsWorkedOut) {
        return new TiltOfADerivedValue.RowsOnABorder(weights, rule, read.readings(),
                pointsWorkedOut && read.complete(), read.wentWithout().union(nearWentWithout),
                read.unwatched());
    }

    /**
     * The readings of the rows that stand at the points {@code at}, whether they are all, and what
     * reading them went without in the words the border's own reading says it in.
     */
    record StandingsRead(List<Map<NumericTerm, Place>> readings, boolean complete,
                         WeakeningSet wentWithout, boolean unwatched) {

        /** No row stands at the line, and whether the rows were all read is {@code complete}. */
        static StandingsRead ofNoRow(boolean complete) {
            return new StandingsRead(List.of(), complete, WeakeningSet.none(), false);
        }
    }

    /**
     * The readings of the rows that stand at a point, asked of the walk that says whether a row
     * does, and no others: a reading of the same row away from the point holds numbers that are
     * not at it.
     */
    private static StandingsRead readAt(Border border, List<Criterion> at, OneShapeOfBorder shape,
                                        List<ObservedInputs> rows) {
        List<Map<NumericTerm, Place>> each = new ArrayList<>();
        boolean complete = true;
        boolean unwatched = false;
        WeakeningSet wentWithout = WeakeningSet.none();
        for (Criterion criterion : at) {
            StandingAtAPoint.RowsRead read = shape.valuesAt(criterion, rows);
            each.addAll(read.each());
            complete &= read.everyOne();
            unwatched |= read.unwatched();
            wentWithout = wentWithout.union(
                    BorderAssessment.rowsIncomplete(border,
                            ReadingReasons.of(read.why(), read.tried())));
        }
        return new StandingsRead(each, complete, wentWithout, unwatched);
    }

    /**
     * One reading of a line, with what its rows came to at each point, before the line's other
     * readings are in.
     *
     * @param border the line as this reading met it
     * @param items  what each point came to at this reading
     * @param absent why nothing was read against the line, or null where the rows were
     * @param beside what the lines beside it are asked of at this reading
     */
    record ReadingOfALine(Border border, Map<DomainPoint, ItemAssessment> items,
                          Measurement<ItemAssessment.Coverage> absent,
                          AnotherLineTheRowsAllow.Reading beside,
                          Optional<TiltOfADerivedValue.Reading> tilt) {}

    /**
     * Every reading, with the lines beside its line answered once for the line.
     *
     * <p>Which lines the rows leave standing beside a line is a question about the line, and every
     * reading's rows answer it together ({@link AnotherLineTheRowsAllow#of}); so it is asked once
     * per line, of all its readings, and each reading carries that one answer. What stays a
     * reading's own is its points and its way, which the search made per reading next is made
     * along. Whether the points are met is the line's too: a point is met where a row is at it at
     * any reading ({@link #together}), which is what the readings put together say of it.
     */
    static LineReadings besideEachLine(List<ReadingOfALine> readings,
                                       List<DerivedValue.Replaced> replaced) {
        SequencedMap<BoundaryLine, List<ReadingOfALine>> byLine = new LinkedHashMap<>();
        for (ReadingOfALine each : readings) {
            byLine.computeIfAbsent(BoundaryLine.of(each.border()), _ -> new ArrayList<>())
                    .add(each);
        }
        Map<BoundaryLine, AnotherLineTheRowsAllow> beside = new LinkedHashMap<>();
        byLine.forEach((line, ofOneLine) -> beside.put(line, besideOneLine(ofOneLine)));
        List<BorderAssessment> out = new ArrayList<>();
        for (ReadingOfALine each : readings) {
            out.add(new BorderAssessment(each.border(), each.items(),
                    beside.get(BoundaryLine.of(each.border()))));
        }
        return new LineReadings(out, tiltsOfEachComputation(readings, replaced));
    }

    /**
     * What the rows fix of the weights of each computation the partition left owing them, put to
     * every border that computation is cut by.
     *
     * <p>Asked of the computations the partition decided and of no others, so that a position
     * whose classes were not drawn is owed a weight and one whose classes were is not. A
     * computation none of whose borders was read says so, and no more: the classes are not drawn
     * for it either, and what is owed is still owed.
     */
    private static List<TiltOfADerivedValue> tiltsOfEachComputation(
            List<ReadingOfALine> readings, List<DerivedValue.Replaced> replaced) {
        List<TiltOfADerivedValue> out = new ArrayList<>();
        for (DerivedValue.Replaced each : replaced) {
            Map<ModelOccurrence, List<TiltOfADerivedValue.RowsOnABorder>> byCall = new LinkedHashMap<>();
            for (ModelOccurrence copy : each.value().copies()) {
                List<TiltOfADerivedValue.RowsOnABorder> ofOneCall = new ArrayList<>();
                for (ReadingOfALine reading : readings) {
                    if (each.value().isCutBy(reading.border(), copy)) {
                        // A border nothing was read against says nothing, and is not left out of
                        // the call: the call's weights are fixed by the rows on every border of it,
                        // and not by the ones that happened to be read.
                        // What nothing was read against it is the border's own measurement to
                        // say, and it is carried as that measurement says it.
                        ofOneCall.add(reading.tilt().map(tilt -> tilt.evidence().get())
                                .orElseGet(() -> TiltOfADerivedValue.RowsOnABorder.unread(
                                        reading.absent() == null ? WeakeningSet.none()
                                                : reading.absent().weakening())));
                    }
                }
                byCall.put(copy, ofOneCall);
            }
            out.add(TiltOfADerivedValue.of(each, byCall));
        }
        return out;
    }

    /** What every reading of one line says about the lines beside it, said once. */
    private static AnotherLineTheRowsAllow besideOneLine(List<ReadingOfALine> ofOneLine) {
        // A threshold of a computation cut at several places was decided once, where the partition
        // placed it. The weights of that computation are owed once for it, so this border is asked
        // nothing about them, and that comes before whether the rows were read: what is owed
        // elsewhere cannot be left unsettled here.
        if (ofOneLine.getFirst().border().threshold()
                .filter(ThresholdOfADerivedValue::isOfAComputation)
                .isPresent()) {
            return new AnotherLineTheRowsAllow.OwedByTheComputation();
        }
        // Nothing was read against the line, which is the line's and not one reading's: what says
        // so is whether the comparison's runs were watched, and the readings share the comparison.
        for (ReadingOfALine each : ofOneLine) {
            if (each.absent() != null) {
                return new AnotherLineTheRowsAllow.CouldNotTell(
                        new AnotherLineTheRowsAllow.Unsettled.TheRowsWereNotRead(each.absent()));
            }
        }
        Map<DomainPoint, ItemAssessment> met = new LinkedHashMap<>(ofOneLine.getFirst().items());
        for (ReadingOfALine next : ofOneLine.subList(1, ofOneLine.size())) {
            met.replaceAll((point, item) -> together(item, next.items().get(point)));
        }
        return AnotherLineTheRowsAllow.of(
                ofOneLine.stream().map(ReadingOfALine::beside).toList(), everyPointMet(met));
    }

    /**
     * What the rows come to at one point, with which rows stand there as far as whether they are
     * all rows that do not hold.
     *
     * <p>Asked of the same walk every time, put to fewer rows. Meeting a point is one row standing
     * there, so where some row does not hold the point is asked of the other rows first: one of them
     * standing there is the point met by another row, and the walk over every row is not made at
     * all. Only where none of them does is every row put to it, and where that meets it, each row
     * that does not hold alone, to say which it rests on. A behavior none of whose rows fails is
     * asked the one question it always was.
     */
    private static Measurement<ItemAssessment.Coverage> standingAt(
            OneShapeOfBorder shape, Criterion criterion, RowsPutToTheLines put, boolean guard,
            Border border, Adequacy.RowReading observed) {
        if (put.notHolding().isEmpty()) {
            return verdictOf(shape.met(criterion, put.all()), () -> RowWitnesses.ANOTHER_ROW,
                    guard, border, observed);
        }
        StandingAtAPoint.Met byOthers = shape.met(criterion, put.others());
        if (byOthers instanceof StandingAtAPoint.Met.Reached) {
            return verdictOf(byOthers, () -> RowWitnesses.ANOTHER_ROW, guard, border, observed);
        }
        return verdictOf(shape.met(criterion, put.all()),
                () -> onlyRowsThatDoNotHoldAt(shape, criterion, put.notHolding()),
                guard, border, observed);
    }

    /** Which of {@code notHolding} stand at a point every row was found to meet and no other row
     *  does. */
    private static RowWitnesses onlyRowsThatDoNotHoldAt(OneShapeOfBorder shape,
                                                        Criterion criterion,
                                                        List<WitnessedRow> notHolding) {
        RowWitnesses.Gathering found = new RowWitnesses.Gathering();
        boolean any = false;
        for (WitnessedRow row : notHolding) {
            if (shape.met(criterion, List.of(row.observed()))
                    instanceof StandingAtAPoint.Met.Reached) {
                found.add(row.by());
                any = true;
            }
        }
        if (!any) {
            throw new IllegalStateException("a point the rows meet is met by one of them, and none"
                    + " of them meets it on its own");
        }
        return found.done();
    }

    /**
     * Whether a row is at every point the border owes one at, and it owes at least one.
     *
     * <p>What says the question about the lines beside it is due. A border short of a row at one of
     * its points is short of the rows that show where it falls, and one the rules leave no value at
     * any point of is owed no row at all — so neither is a border the rows can be asked what else
     * they leave standing at.
     */
    private static boolean everyPointMet(java.util.Map<DomainPoint, ItemAssessment> items) {
        boolean owesOne = false;
        for (ItemAssessment item : items.values()) {
            if (!(item instanceof ItemAssessment.Owed owed)) {
                continue;
            }
            owesOne = true;
            if (!(owed.coverage() instanceof Measurement.Complete<ItemAssessment.Coverage>(
                    ItemAssessment.Coverage.Hit _))) {
                return false;
            }
        }
        return owesOne;
    }

    /**
     * One border, read on whatever it was drawn on.
     *
     * <p>The one reading. Whether a row sits at an item is the quantity's answer ({@link
     * BorderQuantity#standsAt}), where a row would have to stand is the quantity's too
     * ({@link BorderQuantity#searchGoalAt}) and finding one there is the realizer's — so nothing here
     * asks which kind of line this is. Two readings written apart is what left a criterion about one
     * place reaching the reader of a pair as an {@code IllegalStateException}.
     */
    private static OneShapeOfBorder reading(
            souther.compiler.partition.MeasuredInput.BorderReading line,
            ItemAssessment.WritabilityProjection projection,
            List<souther.compiler.partition.OrderedAffineBoundary> elsewhere,
            souther.compiler.partition.WayToTheBorder way, SearchRegion declarations) {
        List<ConditionOutcomeSite> site =
                line.border().origin().recordedAt();
        Predicate<Map<NumericTerm, Place>> refusedByTheDeclarations =
                new DeclarationsRefuse(way, declarations);
        // Put to rows once for every point and row asked of it.
        StandingAtAPoint.AtALine toRows = StandingAtAPoint.putToRows(line, site);
        return new OneShapeOfBorder() {

            @Override
            public StandingAtAPoint.Met met(Criterion criterion, List<ObservedInputs> rows) {
                return toRows.met(rows, criterion);
            }

            @Override
            public StandingAtAPoint.RowsRead valuesAt(Criterion criterion,
                                                      List<ObservedInputs> rows) {
                return toRows.valuesAt(rows, criterion);
            }

            @Override
            public AnotherLineTheRowsAllow.Reading beside(List<ObservedInputs> rows) {
                return new AnotherLineTheRowsAllow.Reading(line.border(),
                        () -> toRows.valuesOf(rows), elsewhere, way, refusedByTheDeclarations);
            }

            // What the position's rules prove answers this border's points only where a row reaches
            // the border whatever it holds. Behind a condition the point asks whether a row arriving
            // here can hold the value, and the position's rules were never put that: `n > 10` and
            // then `n == 11` admits a ten at the position and none at the inner line. So the
            // question is left unput, and what settles the point is what a search over the way finds.
            @Override
            public ItemAssessment.WritabilityProjection projection() {
                return way.asksNothingOfARow() ? projection
                        : ItemAssessment.WritabilityProjection.NOT_COMPUTED;
            }
        };
    }

    /**
     * Whether the declarations of the positions are shown to leave nothing at an input, under the
     * way to one border.
     *
     * <p>The region is an over-approximation of what the declarations allow, so what this says is
     * the one direction it can: {@code true} is a proof, and {@code false} is no claim that a row
     * can be written at the input. A way no value takes leaves nothing anywhere.
     *
     * <p>Made when the way and the declarations are known and read when an input is asked about:
     * most borders have no line beside them and never ask, and what is asked more than once is asked
     * of one region.
     */
    private static final class DeclarationsRefuse implements Predicate<Map<NumericTerm, Place>> {

        private final WayToTheBorder way;
        private final SearchRegion declarations;
        private Reachability reaching;

        DeclarationsRefuse(WayToTheBorder way, SearchRegion declarations) {
            this.way = way;
            this.declarations = declarations;
        }

        @Override
        public boolean test(Map<NumericTerm, Place> input) {
            if (reaching == null) {
                reaching = Reachability.of(way, declarations);
            }
            return !(reaching instanceof Reachability.Reaching able)
                    || able.region().given(input).emptiness().isPresent();
        }
    }

    /**
     * The readings of one behavior's lines, one entry per line.
     *
     * <p>What each reading saw, kept whole: a point one reading found a row at is found, and no
     * other reading of the line takes that back.
     *
     * <p><b>After everything that is a reading's own.</b> Which conditions a row has to satisfy to
     * reach the comparison is one of those, so a search is made per reading and the searches are
     * put together here rather than one being made against whichever reading came first. Put
     * together first, the region a row is composed in is one reading's, chosen by the order a walk
     * took.
     *
     * <p><b>And never across two debts.</b> A line holds the authored line and where it was read;
     * a debt holds the authored line and the value it is at — so two readings under one line are one
     * debt by construction, and a pair that is not says the two identities have come apart.
     */
    static List<BorderAssessment> merged(LineReadings readings) {
        SequencedMap<BoundaryLine, List<BorderAssessment>> byLine = new LinkedHashMap<>();
        for (BorderAssessment each : readings.each()) {
            byLine.computeIfAbsent(BoundaryLine.of(each.border()), _ -> new ArrayList<>())
                    .add(each);
        }
        List<BorderAssessment> out = new ArrayList<>();
        for (List<BorderAssessment> ofOneLine : byLine.values()) {
            out.add(asOneLine(ofOneLine));
        }
        return List.copyOf(out);
    }

    /**
     * Every reading of one line, as the one line they are readings of: two at a time, in the order
     * they were read, and what put things on each one's way at once ({@link SaidOnTheWay#allOf}).
     */
    private static BorderAssessment asOneLine(List<BorderAssessment> ofOneLine) {
        BorderAssessment kept = ofOneLine.getFirst();
        if (ofOneLine.size() == 1) {
            return kept;
        }
        for (BorderAssessment next : ofOneLine.subList(1, ofOneLine.size())) {
            kept = asOneLine(kept, next);
        }
        return new BorderAssessment(kept.border(), kept.items(), kept.beside(), kept.toldApart(),
                kept.readAt(), SaidOnTheWay.allOf(
                        ofOneLine.stream().map(BorderAssessment::saidOnTheWay).toList()));
    }

    /**
     * How a row is looked for at one border, on whatever it was drawn on.
     *
     * <p>Beside {@link #reading} rather than inside it. Both are about one border and neither is the
     * other: what the rows already established is read whatever anybody asked for, and building a
     * value is work somebody asked for and pays for.
     *
     * @param inTheRegion whether a row is put to the points as one of a class the line cuts, which
     *                    asks nothing of it that is only where the line decides
     *                    ({@link StandingAtAPoint.AtALine#inTheRegion})
     */
    private static OneSearchOfABorder searching(Border border, MeasuredInput.BorderReading line,
                                                MeasuredInput input,
                                                Probe probe, LevelRealizer realizer,
                                                souther.compiler.partition.WayToTheBorder within,
                                                boolean inTheRegion) {
        souther.compiler.inputs.Quantities rules = input.quantities();
        BorderQuantity quantity = line.quantity();
        List<ConditionOutcomeSite> site =
                border.origin().recordedAt();
        // Put to rows once for every row a point is searched with.
        StandingAtAPoint.AtALine toRows = inTheRegion
                ? StandingAtAPoint.putToRows(line, site).inTheRegion()
                : StandingAtAPoint.putToRows(line, site);
        // Built here and gone when the search is. What a row has to be to arrive is a way of asking
        // about values rather than something that says what it is, so it is what the walk runs
        // against and never what the answer keeps; the account it was built from is what travels.
        souther.compiler.partition.Reachability reaching =
                souther.compiler.partition.Reachability.of(within, rules.region());
        // Where the reading's numbers are written, which is the same at every point of it.
        List<RealizationTarget.OfANumber> read = quantity.numbers().stream()
                .map(RealizationTarget::of).toList();
        // Once for the border rather than once for each of its points. What the positions of this
        // input admit is the same answer at every point of it, and working it out where it is spent
        // walks every position of the input at every point a row is searched for.
        souther.compiler.partition.WitnessSearch looking = input.witnessSearch();
        return new OneSearchOfABorder() {

            @Override
            public SearchOutcomes search(Criterion criterion, String label) {
                return looked(criterion, label, UnaryOperator.identity()).outcomes();
            }

            @Override
            public ARowTellingTheLinesApart.AtOneReading tellingApart(
                    Criterion criterion, String label, AnotherLineTheRowsAllow.Stands line,
                    UnaryOperator<SearchRegion> narrowing) {
                Looked looked = looked(criterion, label, narrowing);
                return ARowTellingTheLinesApart.of(border, line, looked.composed(),
                        looked.outcomes());
            }

            /**
             * What looking for a row at {@code criterion} came to, inside the region {@code
             * narrowing} leaves.
             *
             * <p>One walk for both questions. A point of the line and an input that tells the line
             * from the one beside it are looked for the same way — a place the criterion accepts,
             * a row built there, and the row read back — and what differs is the region. Written
             * twice, the second would be the first without whatever the first learned since.
             */
            private Looked looked(Criterion criterion, String label,
                                  UnaryOperator<SearchRegion> narrowing) {
                // Nothing to build against. Told apart from nobody having asked, which is not a
                // state anything here can be in: this runs because somebody asked.
                if (probe == null) {
                    return new Looked(SearchOutcomes.of(new ItemAssessment.Attempt.Unavailable(
                            ItemAssessment.Attempt.Reason.NO_CLASSES)), null, Optional.empty());
                }
                // A way no value takes: one position would have to take two of its cases, or a
                // condition on it comes out the other way for every row. Said in that word and not
                // in the one for a walk that tried what the rules leave and reached nothing:
                // nothing was walked here, and what settles it is the model.
                Reachability.Reaching able;
                switch (reaching) {
                    case Reachability.Reaching way -> able = way;
                    case Reachability.NothingReaches _ -> {
                        return noRowTakes(label, within,
                                Generator.UnresolvedCombination.Reason.ONE_POSITION_CANNOT_BE_BOTH);
                    }
                    case Reachability.NothingComesOutThatWay _ -> {
                        return noRowTakes(label, within, Generator.UnresolvedCombination.Reason
                                .A_CONDITION_NEVER_COMES_OUT_THAT_WAY);
                    }
                    case Reachability.NumbersLeaveNone _ -> {
                        return noRowTakes(label, within,
                                Generator.UnresolvedCombination.Reason.NO_VALUE_CAN_STAND_THERE);
                    }
                }
                // Where a condition on the way came out one of several ways, a row is looked for
                // along each of them first, each narrower than the way whole. A row standing along
                // one is a row of the way. Where none stands, what the point came to is what the
                // way whole came to: one of them coming to nothing says nothing of the others, and
                // the way whole is the account every one of them is inside.
                if (able.along().isEmpty()) {
                    return lookedAlong(criterion, label, narrowing, able);
                }
                // Past the figure the way whole is looked along first where a condition it was not
                // split at is composed against whole there — a statement the elements of one
                // container meet, every way of it at once — since the ways the figure let through
                // are each one of those ways. Anywhere else the way whole is composed against less
                // than they are, and is looked along after them.
                Looked whole = null;
                if (able.ways() instanceof Reachability.Ways.Whole past
                        && past.composedAgainstWhole(line.quantity().behavior())) {
                    whole = lookedAlong(criterion, label, narrowing, able);
                    if (whole.witness().isPresent()) {
                        return whole;
                    }
                }
                SearchOutcomes alongEach = SearchOutcomes.none();
                for (Reachability.Reaching along : able.along()) {
                    Looked one = lookedAlong(criterion, label, narrowing, along);
                    if (one.witness().isPresent()) {
                        return one;
                    }
                    alongEach = alongEach.plus(one.outcomes());
                }
                // Split into every way a row takes, and along each of them the rules leave no
                // value at the point: no row past the way stands there. The way whole spans the
                // values between the ways and would offer one, and a row built there turns back
                // before the point.
                if (able.ways() instanceof Reachability.Ways.Each
                        && alongEach.provesInfeasible()) {
                    return new Looked(alongEach, null, Optional.empty());
                }
                return whole != null ? whole : lookedAlong(criterion, label, narrowing, able);
            }

            /** What looking for a row at {@code criterion} along {@code able} came to. */
            private Looked lookedAlong(Criterion criterion, String label,
                                       UnaryOperator<SearchRegion> narrowing,
                                       Reachability.Reaching able) {
                // A reading of the line under a case this way does not take. A line at a name the
                // cases of a sum share is read under each case, and a way split at the cases a
                // narrowing leaves is looked along each of them, so no row along this one is the
                // case the reading's numbers stand under. The model settles that before any value
                // is put to the point, and the values are not spent finding it out.
                if (able.writing(read) instanceof Reachability.Written.OffTheWay) {
                    return noRowTakes(label, within,
                            Generator.UnresolvedCombination.Reason.ONE_POSITION_CANNOT_BE_BOTH);
                }
                SearchRegion region = narrowing.apply(able.region());
                // Where a row would have to stand is asked of the quantity, and finding one there of
                // the realizer. What it composes is a candidate and no part of the item: another row
                // in the same side is at the point as much as this one would be, so what the row is
                // offered for goes in beside it rather than being read back off it.
                //
                // And a candidate is put to the point before the next one is asked for. What the
                // realizer hands over is a place the region admits, which is less than the question:
                // a row built there may turn back above the line and never arrive, and the value
                // beside it arrive perfectly well. Stopping at the first place the region admits,
                // the search answered a point it had one more value for.
                ValuesTried tried = ValuesTried.NONE;
                SearchOutcomes last = null;
                Realization.Found first = null;
                // As many askings as the way the row is found says, which is said where what is
                // asked is ({@link PointSearchGoal#askedAtMost}) — and the first whatever it says,
                // since the first is the point's answer: a goal with nothing to try is asked, and
                // answers that.
                int askings = quantity.searchGoalAt(criterion).askedAtMost();
                int value = 0;
                do {
                    Searching came = searchingWith(criterion, label, able, region, tried);
                    if (came.witness().isPresent()) {
                        return new Looked(came.outcomes(), came.realized(), came.witness());
                    }
                    // Nothing was composed this time round. On the first asking that is the point's
                    // answer; on a later one it is the answer to a question this narrowed by
                    // leaving a value out, and what the point came to is what the value that was
                    // composed came to — said with whatever of this compiler's ended the asking.
                    if (came.realized() == null) {
                        return new Looked(last == null ? came.outcomes()
                                : endedBy(last, came.came()), first, Optional.empty());
                    }
                    // The row a reader is offered is the first one composed. Every asking after it
                    // is put a narrower question — the values already tried are not there to be
                    // found again — so a row from a later one is a row built with values kept from
                    // it for a reason of this search's rather than of the model's.
                    if (last == null) {
                        last = came.outcomes();
                        first = came.realized();
                    }
                    // Short of a population at this value that it is short of at every value: the
                    // next value is written as short, builds no row, and ends the asking with the
                    // word this one did, so it is not asked for.
                    if (came.outcomes().shortWhateverTheValue()) {
                        return new Looked(last, first, Optional.empty());
                    }
                    // Every way of standing the dependencies in was built and none of them stood,
                    // so this is the value that did not answer and not one of the rows it was built
                    // into. Charged here for that reason: a point with more ways to stand its
                    // dependencies in would otherwise be allowed fewer values than one with fewer.
                    tried = tried.and(came.realized().fixing());
                } while (++value < askings);
                // The count ran out, and whether that is what ended the asking is the realizer's to
                // say. Asked once more and for nothing else: a figure reported where the values
                // themselves had run out is a number an author raises to be told the same thing,
                // and a search that stopped where a figure of this compiler's is the only thing
                // between the point and another value has to say so.
                //
                // Nothing is put to the point here, so no value is tried and none is charged for.
                return new Looked(endedBy(last, realized(criterion, able, region, tried)), first,
                        Optional.empty());
            }

            /**
             * Where a row at {@code criterion} along {@code able} would stand, or why none is
             * offered: solved for where the quantity says what the input has to be, and looked
             * for by running candidates where only a run works it out ({@link PointSearchGoal}).
             */
            private Realization realized(Criterion criterion,
                                         souther.compiler.partition.Reachability.Reaching able,
                                         SearchRegion region, ValuesTried tried) {
                return realizer.realize(quantity.searchGoalAt(criterion).alongTheWay(able),
                        region, looking, tried);
            }

            /**
             * One value put to the point.
             *
             * <p>{@code came} is what the realizer answered, whatever that was; {@code realized} is
             * the same answer where it was a value with rows built from it, which is the one case
             * there is another value to ask for. Both, because what ended the asking is read off
             * the first and what to do next off the second. {@code witness} is a row built from it
             * that ran and stood at the point, where one did.
             */
            private record Searching(Realization came, Realization.Found realized,
                                     SearchOutcomes outcomes,
                                     Optional<ItemAssessment.Attempt.Certified> witness) {}

            /**
             * What a walk over one region came to, and the assignment the row it composed was
             * built from.
             *
             * <p>The two together, because a caller shown one place and handed a row built at
             * another has been shown two answers about one search. {@code composed} is the
             * realization the row in {@code outcomes} was built from, and is null exactly where no
             * row was built.
             *
             * <p>{@code witness} is the row that ran and stood at the point, and is held as that row
             * and not as a flag beside {@code composed}: a realization is where the search placed
             * the demands, which a row built there may run past, so nothing here says a point was
             * reached except a run that reached it.
             */
            private record Looked(SearchOutcomes outcomes, Realization.Found composed,
                                  Optional<ItemAssessment.Attempt.Certified> witness) {}

            /** A way no value takes, said in the word for what the model settled it by. */
            private static Looked noRowTakes(String label, WayToTheBorder within,
                                             Generator.UnresolvedCombination.Reason why) {
                return new Looked(SearchOutcomes.of(new ItemAssessment.Attempt.Unresolved(
                        new Generator.UnresolvedCombination(List.of(label), why), within)), null,
                        Optional.empty());
            }

            /**
             * What the values came to, said with whatever of this compiler's ended the asking.
             *
             * <p><b>Read off what the realizer answered last and never off the loop.</b> A point
             * put every value it had and a point this compiler stopped putting values to are
             * different news — only the second has a number somebody could raise — and the count of
             * askings says nothing about which of them this was. A figure named from the count
             * alone is one reported where a point had exactly as many values as this tries, which
             * is a number an author raises to be told the same thing.
             *
             * <p>And the last answer's own shortfall travels. A walk that could name one place on a
             * line and no second one is short of a population this compiler writes some of, not of
             * values; dropped for the word the first value came back with, the point is reported as
             * one that had everything tried at it.
             *
             * <p>What each search came to is kept either way. The vocabulary beside it says the
             * word is about what was tried rather than about the point, which is a second half and
             * not a different first one.
             */
            private SearchOutcomes endedBy(SearchOutcomes last, Realization ended) {
                if (ended instanceof Realization.Found) {
                    return overLessThanThePointHad(last,
                            Set.of(CompositionBudget.VALUES_A_POINT_IS_TRIED_WITH), Set.of(),
                            Set.of());
                }
                // A proof about what was left is no proof about the point: what it is a proof about
                // is the question this narrowed by leaving values out.
                if (ended instanceof Realization.Unknown left
                        && !(left.stoppedBy().isEmpty() && left.notAllOf().isEmpty()
                                && left.unheld().isEmpty())) {
                    return overLessThanThePointHad(last, left.stoppedBy(), left.notAllOf(),
                            left.unheld());
                }
                return last;
            }

            /**
             * The same answer, said as one that is about less than the point had.
             *
             * <p>On the searches' own answers and nowhere else. An outcome already naming something
             * of this compiler's is one where this was not what fell short, and a second name
             * beside it is a thing an author would act on to be told the same thing.
             *
             * <p>Every vocabulary the asking was short in goes with it, each under its own name. The
             * two readings of a pair walk one order, and one may meet a figure while the other walks
             * some of a population or reaches a place it cannot hold; choosing one of them would
             * tell a reader to act on it alone.
             */
            private SearchOutcomes overLessThanThePointHad(SearchOutcomes outcomes,
                    Set<CompositionBudget> budgets, Set<CompositionRepertoire> repertoires,
                    Set<CompositionCapacity> capacities) {
                java.util.List<ItemAssessment.Attempt> out = new java.util.ArrayList<>();
                for (ItemAssessment.Attempt each : outcomes.each()) {
                    out.add(each instanceof ItemAssessment.Attempt.Unresolved it
                            ? shortOf(it, budgets, repertoires, capacities) : each);
                }
                return SearchOutcomes.each(out);
            }

            /**
             * One search's answer, wearing what the asking after it was short of: under the figure
             * where one was met, since that is what a reader raises, and otherwise under what the
             * asking walked some of or could not hold.
             */
            private ItemAssessment.Attempt shortOf(ItemAssessment.Attempt.Unresolved it,
                    Set<CompositionBudget> budgets, Set<CompositionRepertoire> repertoires,
                    Set<CompositionCapacity> capacities) {
                return budgets.isEmpty()
                        ? new ItemAssessment.Attempt.Unexhausted(it.why(), it.way(), it.uncomposed(),
                                PublicationOrders.COMPOSITION_REPERTOIRES.keep(repertoires),
                                PublicationOrders.COMPOSITION_CAPACITIES.keep(capacities))
                        : new ItemAssessment.Attempt.Limited(it.why(), it.way(), it.uncomposed(),
                                PublicationOrders.COMPOSITION_BUDGETS.keep(budgets),
                                PublicationOrders.COMPOSITION_REPERTOIRES.keep(repertoires),
                                PublicationOrders.COMPOSITION_CAPACITIES.keep(capacities));
            }

            private Searching searchingWith(Criterion criterion, String label,
                    souther.compiler.partition.Reachability.Reaching able,
                    SearchRegion region, ValuesTried tried) {
                Realization answered = realized(criterion, able, region, tried);
                return switch (answered) {
                    case Realization.Found found -> {
                        // Asking nothing of what the dependencies answer. A point of a line is a
                        // place the positions stand at, and nothing about it turns on what a
                        // dependency says — so the row is stood in with whatever answers the
                        // behavior generally, which is what asking nothing gets.
                        //
                        // Which leaves the case of a union answer open, and a row arrives at a
                        // point inside one of the cases only by carrying that case. So each way of
                        // standing the dependencies in is built, read back, and kept: what the
                        // point comes to is what they all came to, and a reader asking whether one
                        // reached it, which row to offer, or what would have to give for the rest,
                        // asks that of {@link SearchOutcomes}.
                        java.util.List<souther.compiler.partition.Generator.BoundaryAttempt> made =
                                probe.attempt(label, found.fixing(),
                                        quantity.asksOfEachTerm(criterion), able,
                                        souther.compiler.partition.AnswersDemanded.NOTHING);                        // Nothing was tried at all, which is the classes not linking. An empty
                        // answer would say the point was searched and nothing happened. Not a value
                        // this point was tried with either: nothing was built, so there is nothing
                        // to leave out of the next asking and nothing another value would fix.
                        if (made.isEmpty()) {
                            yield new Searching(answered, null,
                                    SearchOutcomes.of(whatCameOfIt(null, label, within, () -> null)),
                                    Optional.empty());
                        }
                        SearchOutcomes outcomes = SearchOutcomes.none();
                        ItemAssessment.Attempt.Certified witness = null;
                        for (souther.compiler.partition.Generator.BoundaryAttempt each : made) {
                            ItemAssessment.Attempt came = whatCameOfIt(each, label, within,
                                    () -> standingThere(probe, toRows, criterion,
                                            (souther.compiler.partition.Generator
                                                    .BoundaryAttempt.Built) each));
                            if (witness == null
                                    && came instanceof ItemAssessment.Attempt.Certified certified) {
                                witness = certified;
                            }
                            outcomes = outcomes.plus(SearchOutcomes.of(came));
                        }
                        yield new Searching(answered, found, outcomes,
                                Optional.ofNullable(witness));
                    }
                    // And the two ways of finding nothing are not one answer. A walk of the whole
                    // of what the rules leave that reaches no value settles the point; a search
                    // that stopped, or one that composed no candidate at all, settles nothing
                    // (ADR-0091).
                    case Realization.Impossible _ -> new Searching(answered, null, SearchOutcomes.of(
                            new ItemAssessment.Attempt.Unresolved(
                                    new Generator.UnresolvedCombination(List.of(label),
                                            Generator.UnresolvedCombination.Reason
                                                    .NO_VALUE_CAN_STAND_THERE), within)),
                            Optional.empty());
                    // A walk that reached no placement. Where a budget of this compiler's is why it
                    // reached none, that travels: the point is one this declined to look further
                    // for, which is not the point being one nothing promises.
                    //
                    // And where what it could not reach is a population rather than a figure, that
                    // travels too and under its own name. Raising nothing reaches the rest of one,
                    // so a walk that wrote some of a population is neither a walk a figure stopped
                    // nor a walk that narrowed nothing — read as the second, a pair this looked for
                    // in the one place such an order names came out as the rules leaving none.
                    case Realization.Unknown unknown -> new Searching(answered, null,
                            SearchOutcomes.of(whatAWalkLeft(label, within, unknown)),
                            Optional.empty());
                };
            }
        };
    }

    /**
     * Two readings of one line, as the one line they are readings of.
     *
     * <p><b>Nothing is chosen between.</b> A helper called from two places is one line read once
     * and searched twice — the authored line and the target are the same, and what differs is the
     * region a row for it was composed in — so the two are put together and neither stands for the
     * other. Kept as whichever saw more, whatever the other established was gone before anything
     * downstream could ask, and a point whose only search a budget stopped came out holding nothing.
     *
     * <p>Point by point rather than border by border. Two readings of one line can have seen
     * different things at different points, and one answer for the whole border would settle a
     * point from what happened at another.
     *
     * <p>Everything but what put things on the ways, which stays {@code a}'s: that is put together
     * for every reading of the line at once, by {@link #asOneLine(List)}.
     */
    private static BorderAssessment asOneLine(BorderAssessment a, BorderAssessment b) {
        if (!a.border().obligation().equals(b.border().obligation())) {
            throw new IllegalStateException("two readings of one line owing different rows: "
                    + a.border().obligation() + " and " + b.border().obligation());
        }
        java.util.Map<DomainPoint, ItemAssessment> kept = new java.util.LinkedHashMap<>();
        for (DomainPoint point : a.items().keySet()) {
            kept.put(point, together(a.at(point), b.at(point)));
        }
        ModelOccurrences readAt = a.readAt().and(b.readAt());
        return new BorderAssessment(a.border(), kept, besides(a.beside(), b.beside()),
                // Both readings' searches and neither standing for the other. A row is composed in
                // one reading's region and at the positions that reading names, so the reading
                // travels with it — folded to one here, a row would arrive beside the other
                // reading's line and its input would be read at positions that line has none of.
                a.toldApart().and(b.toldApart()),
                // And both readings' copies, which is what tells the calls of a helper that read
                // one line apart. What put things on each one's way is put together once for every
                // reading of the line, by whoever holds them all.
                readAt, a.saidOnTheWay());
    }

    /**
     * What two readings of one line say about the lines beside it.
     *
     * <p>One answer, because there is one question, and it was asked once of every reading's rows
     * ({@link #besideEachLine}). What a reading adds after that is what its own search showed
     * arriving, at a line nothing showed an input arriving at — so two readings differ there and
     * nowhere else, and two that differ anywhere else are this compiler saying two things about
     * one measurement.
     */
    static AnotherLineTheRowsAllow besides(AnotherLineTheRowsAllow a,
                                           AnotherLineTheRowsAllow b) {
        if (a.equals(b)) {
            return a;
        }
        // Line by line of the family, which two readings of one line share.
        if (a instanceof AnotherLineTheRowsAllow.ByDirection one
                && b instanceof AnotherLineTheRowsAllow.ByDirection other
                && one.family().equals(other.family())) {
            List<AnotherLineTheRowsAllow.Direction> each = new ArrayList<>();
            for (int i = 0; i < one.each().size(); i++) {
                each.add(besides(one.each().get(i), other.each().get(i)));
            }
            return new AnotherLineTheRowsAllow.ByDirection(each);
        }
        throw new IllegalStateException("two readings of one line disagreeing about which lines"
                + " the rows leave standing beside it: " + a + " and " + b);
    }

    /**
     * What two readings of one line say about one line of its family.
     *
     * <p>The line's answer at both, except where a reading's search showed an input arriving at a
     * line the rows left with none: the line is then one the rows leave standing, at that input,
     * which the other reading's search did not show. Where both showed one, either input rules out
     * the line as the rows leave it: one that names an input is said before one that names none,
     * and otherwise the first.
     */
    static AnotherLineTheRowsAllow.Direction besides(AnotherLineTheRowsAllow.Direction a,
                                                     AnotherLineTheRowsAllow.Direction b) {
        if (a.equals(b) || shownArrivingAt(a, b)) {
            return a;
        }
        if (shownArrivingAt(b, a)) {
            return b;
        }
        if (a instanceof AnotherLineTheRowsAllow.Stands one
                && b instanceof AnotherLineTheRowsAllow.Stands other && one.isTheLineOf(other)) {
            return one.tellsApartAt() != null || other.tellsApartAt() == null ? one : other;
        }
        throw new IllegalStateException("two readings of one line answering differently about a"
                + " line beside it, which was asked once of both: " + a + " and " + b);
    }

    /** Whether {@code shown} is {@code left} with an input a search showed arriving at it. */
    private static boolean shownArrivingAt(AnotherLineTheRowsAllow.Direction shown,
                                           AnotherLineTheRowsAllow.Direction left) {
        return shown instanceof AnotherLineTheRowsAllow.Stands standing
                && left instanceof AnotherLineTheRowsAllow.Undecided(var _,
                        AnotherLineTheRowsAllow.Unsettled.NoReachableDistinguisher(var was))
                && standing.isTheLineOf(was);
    }

    /**
     * What two searches of one point of one reading come to, dimension by dimension.
     *
     * <p><b>Not one of them.</b> They are searches of the same point under one reading, and the
     * point is owed once — so what a reader is owed is what both of them found out. Taking whichever
     * saw more, every fact the other one established was gone before anything downstream could ask:
     * a search a budget of this compiler's stopped, dropped for one that came back with nothing, is
     * how a point this declined to work on left the count as one the model admits no row at.
     *
     * <p>Each dimension by whatever owns it. What the rows came to is coverage's own question
     * ({@link ObligationCoverage#acrossOneReadingsSearches}); what the rules prove is the
     * projection's ({@link ItemAssessment.WritabilityProjection#and}). The two searches read the
     * same declarations but each along its own way to the border — a rule written once and met
     * through two copies of the closure it is in is reached on a different condition by each — so
     * what one proved the other may not have been asked.
     */
    private static ItemAssessment together(ItemAssessment a, ItemAssessment b) {
        if (!(a instanceof ItemAssessment.Owed one) || !(b instanceof ItemAssessment.Owed two)) {
            // Two readings of one line owe the same points, so a point no row is owed at is that
            // under both — and there is nothing about it to put together.
            return a;
        }
        // Two readings of one line reach other lines of the position, so the run beside it stops at
        // a different one in each: the same point asked for under two ways. It is kept as the first
        // reading asks it, the border it is a point of being that reading's, and what each reading
        // found is put together below. A point asking for a different side or value is another
        // point, which two readings of one line do not owe.
        if (!one.criterion().equals(two.criterion())
                && !(one.criterion() instanceof Criterion.Within in
                        && two.criterion() instanceof Criterion.Within also
                        && in.besideTheSameLineAs(also))) {
            throw new IllegalStateException("two searches of one point asking for different"
                    + " values: " + one.criterion() + " and " + two.criterion());
        }
        return new ItemAssessment.Owed(one.criterion(),
                ObligationCoverage.acrossOneReadingsSearches(one.coverage(), two.coverage()),
                one.projection().and(two.projection()), one.searches().plus(two.searches()));
    }

    /**
     * A candidate the walk that reads a row at a point was seen to stand there, or a search that
     * composed a row and did not.
     *
     * <p><b>The one thing that says a row is at a point.</b> {@link StandingAtAPoint} answers it for
     * the rows in the file and for the rows a person is being offered, so a candidate goes through
     * it before it is offered rather than after somebody has been handed it. What a search knows
     * while it is composing is narrower — that each position it fixed reads back at the place it was
     * fixed at — and a row can pass that and turn back above the comparison, which is exactly the
     * disagreement this removes: the generator and the reading are no longer two accounts of one
     * model, because the generator asks the reading.
     *
     * <p><b>Where it fails open, and where it does not.</b> The two halves of standing at a point
     * are not the same question. Whether the values are at the level is read off the row and is
     * this compiler's to answer; whether the comparison was answered takes something having watched
     * the run, which is not. So a row nothing watched is offered — the values were seen at the
     * level and the rest is a thing nobody could put a question about — and a row whose values
     * could not be read at the point is not: that is the walk unable to confirm the half this
     * compiler owns, of a value this compiler has just built, which is the two readings coming
     * apart in the one place this exists to close.
     *
     * <p>So what holds of an offered row is that its values were seen at the point, and the run
     * either reached the comparison or was not watched. Kept open at both, an answer that used to
     * be a disagreement could go on being one under another name, and the measure would go green
     * over it.
     *
     * <p>An answer about this search and never about the model. A row composed here that does not
     * stand at the point says the way to the border was not composed against in full; the point is
     * owed the same row it was owed before, and nothing here says one cannot be written.
     *
     * <p>With the row as it was read back, which is what a reader asking what the row does to
     * anything beside the point reads: the values it was composed for are what the search asked
     * for, and the row need not hold them.
     */
    private static ReadBack standingThere(
            Probe probe, StandingAtAPoint.AtALine line, Criterion criterion,
            souther.compiler.partition.Generator.BoundaryAttempt.Built built) {
        souther.compiler.partition.ObservedInputs read =
                probe.read(built.row().toRun()).asInputs();
        return new ReadBack(read, read == null ? null : line.met(List.of(read), criterion));
    }

    /**
     * A row read back, and what the reading at a point made of it.
     *
     * @param read the row as its run read it back, or null where nothing came back to read it off
     * @param met  what the reading made of it, or null where there was nothing to read
     */
    private record ReadBack(souther.compiler.partition.ObservedInputs read,
                            StandingAtAPoint.Met met) {

        /** What the reading made of the row, and what nothing coming back to read is. */
        StandingAtAPoint.Met standing() {
            return met != null ? met : nothingCameBack();
        }
    }

    /**
     * What a row nothing came back to read off comes to, which is not an observation of it and is
     * not a position holding no value either. What did not happen is the running: the values would
     * not build a second time, or the model refused them, or the classes would not link — and every
     * one of those is something this run did rather than a value a limit shortened or a place a row
     * wrote nothing at. Named as the first, a linkage failure arrives at the account as an
     * observation that was stopped and the report says a limit did something that never fired;
     * named as the second, it says the row put nothing where nothing ever looked. And nothing was
     * left untried by a limit: there was no row for readings of it to be made from, so what stopped
     * this is the reason beside it and not the search.
     */
    private static StandingAtAPoint.Met nothingCameBack() {
        return new StandingAtAPoint.Met.CouldNotTell(
                Set.of(souther.compiler.partition.ReadingGap.COULD_NOT_READ_ROW),
                StandingAtAPoint.ReadingsTried.EVERY_ONE);
    }

    /** Whether an observation is among the reasons a reading came to nothing. */
    private static boolean observed(StandingAtAPoint.Met.CouldNotTell why) {
        return why.why().stream()
                .anyMatch(each -> each instanceof souther.compiler.partition.ReadingGap.Observation);
    }

    /**
     * The observations among them, which is what a gap about an observation may hold.
     *
     * <p>Only those. A walk that reached no value is a reason the reading came to nothing and is
     * not a thing an observation did, so it travels as far as the account's own reasons go and no
     * further.
     */
    private static EstablishmentGap.Observation stopped(StandingAtAPoint.Met.CouldNotTell why) {
        Set<Incompleteness.Code> codes = new LinkedHashSet<>();
        List<Figure> figures = new ArrayList<>();
        for (souther.compiler.partition.ReadingGap each : why.why()) {
            if (each instanceof souther.compiler.partition.ReadingGap.Observation it) {
                codes.add(it.code());
                figures.addAll(it.figures());
            }
        }
        return EstablishmentGap.Observation.of(codes, figures);
    }

    /** No population written some of, for an answer that met none. One value, since nothing
     *  differs between the empty selections an answer would otherwise make each time. */
    private static final CanonicalSelection<CompositionRepertoire> NO_REPERTOIRES =
            PublicationOrders.COMPOSITION_REPERTOIRES.keep(Set.of());

    /** No number not held, for an answer that held every one it worked out. */
    private static final CanonicalSelection<CompositionCapacity> NO_CAPACITIES =
            PublicationOrders.COMPOSITION_CAPACITIES.keep(Set.of());

    /**
     * What a walk that reached no placement left behind, in the words an assessment is read in.
     *
     * <p>Three shapes and not two, because what a reader does about each differs. A figure is a
     * number to raise; a population this writes some of is work nobody has done and no number
     * reaches the rest of it, and a number the walk could not hold is reached by a wider run or by
     * nothing, and both of those come back under the one shape with no figure in it; and a walk
     * with none of them to say narrowed nothing at all. Held as two, the middle one was read as the
     * last — so a search that looked in the one place an order without a step names came back
     * saying the rules leave nothing there.
     *
     * <p>The word is the walk's own either way and is not read off what it left, which is why it is
     * taken from the same place for all three.
     */
    private static ItemAssessment.Attempt whatAWalkLeft(
            String label, souther.compiler.partition.WayToTheBorder within,
            Realization.Unknown unknown) {
        souther.compiler.partition.Generator.UnresolvedCombination why =
                new souther.compiler.partition.Generator.UnresolvedCombination(
                        java.util.List.of(label), wordOf(unknown));
        if (!unknown.stoppedBy().isEmpty()) {
            return new ItemAssessment.Attempt.Stopped(why, within,
                    souther.compiler.partition.CompositionAccount.NOTHING,
                    PublicationOrders.COMPOSITION_BUDGETS.keep(unknown.stoppedBy()),
                    PublicationOrders.COMPOSITION_REPERTOIRES.keep(unknown.notAllOf()),
                    PublicationOrders.COMPOSITION_CAPACITIES.keep(unknown.unheld()));
        }
        if (!unknown.notAllOf().isEmpty() || !unknown.unheld().isEmpty()) {
            return new ItemAssessment.Attempt.Unexhausted(why, within,
                    souther.compiler.partition.CompositionAccount.NOTHING,
                    PublicationOrders.COMPOSITION_REPERTOIRES.keep(unknown.notAllOf()),
                    PublicationOrders.COMPOSITION_CAPACITIES.keep(unknown.unheld()));
        }
        return new ItemAssessment.Attempt.Unresolved(why, within);
    }

    /**
     * The word a walk that reached no placement comes back with.
     *
     * <p>The realizer's own, kept as it is. What it says is which of the two things a walk that
     * found nothing did, and it says it whether or not a figure of this compiler's was reached —
     * which is why the figure travels beside it rather than being read out of it.
     */
    private static souther.compiler.partition.Generator.UnresolvedCombination.Reason wordOf(
            Realization.Unknown unknown) {
        return switch (unknown.why()) {
            case NOTHING_COMPOSED_ONE -> souther.compiler.partition.Generator
                    .UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE;
            case THE_SEARCH_LEFT_SOMETHING_UNTRIED -> souther.compiler.partition.Generator
                    .UnresolvedCombination.Reason.THE_SEARCH_LEFT_SOMETHING_UNTRIED;
        };
    }

    /**
     * What a search of the module's own decoders came to, in this measure's words.
     *
     * <p>{@code within} travels as far as the answer does. The region is what the search ran in,
     * and a run that composed a row and never saw it arrive is the answer that most needs it — the
     * candidate came out of this box, and a condition on the way that nothing represented in the
     * box is a thing an author would want to know at exactly that point.
     *
     * <p>Including where the decoders could not be reached. This is asked only of a placement the
     * realizer found, so the region was walked and a candidate came out of it before anything was
     * run — which makes it a search that came to nothing rather than a search nobody made, and it
     * carries what it was looking over like the rest. Filed as one nobody made, it was the one
     * outcome of a search that dropped its region, and the reader that wanted it back built the
     * same value by hand a moment later.
     */
    private static ItemAssessment.Attempt whatCameOfIt(
            souther.compiler.partition.Generator.BoundaryAttempt made, String subject,
            souther.compiler.partition.WayToTheBorder within,
            Supplier<ReadBack> standing) {
        return switch (made) {
            case null -> new ItemAssessment.Attempt.Unresolved(
                    new souther.compiler.partition.Generator.UnresolvedCombination(
                            List.of(subject),
                            souther.compiler.partition.Generator.UnresolvedCombination.Reason
                                    .LINKAGE_FAILED), within);
            // The way as the walk left it, and beside it what the composer could not act on. Two
            // stages and two answers: a condition the walk stated stays stated, and writing the
            // composer's own failure onto the way would have one condition wearing two of the
            // walk's words.
            //
            // And the row read back, which is where a composed value becomes a value at the point
            // or stops short of being one. The three answers of that reading are the three this
            // hands on, and this is the only place they are turned into what a search came to.
            case souther.compiler.partition.Generator.BoundaryAttempt.Built built -> {
                ReadBack back = standing.get();
                yield switch (back.standing()) {
                        case StandingAtAPoint.Met.AtPoint at ->
                                new ItemAssessment.Attempt.Certified(built.row(), within,
                                        built.unrepresented(),
                                        at instanceof StandingAtAPoint.Met.Reached, back.read());
                        // Composed and not seen where it was composed for. Which says the way to
                        // the border was not composed against in full and never that the point is
                        // unwritable, and it carries what the composer could not act on because
                        // that is the first thing that would explain it.
                        case StandingAtAPoint.Met.NotAtPoint _ ->
                                new ItemAssessment.Attempt.Unresolved(
                                        new souther.compiler.partition.Generator
                                                .UnresolvedCombination(List.of(subject),
                                                souther.compiler.partition.Generator
                                                        .UnresolvedCombination.Reason
                                                        .NO_CERTIFIED_WITNESS),
                                        within, built.unrepresented());
                        // And a reading that could not look is not a reading that looked. The value
                        // was built and the decoders took it; what did not happen is the reading
                        // back. Said as the answer above, a point a value was just built at is
                        // reported as one nothing can write a row at.
                        // And only the observations among the reasons make an observation's gap. A
                        // walk that reached no value made no observation, so there is none to have
                        // been stopped, and a gap built from it would put a limit's name on
                        // something no limit did. Where that is all there was, what this run did is
                        // the search's own to say, in the generator's words.
                        case StandingAtAPoint.Met.CouldNotTell it ->
                                observed(it) ? new ItemAssessment.Attempt.Unverified(built.row(),
                                        within, built.unrepresented(), stopped(it))
                                        : new ItemAssessment.Attempt.Unresolved(
                                                new souther.compiler.partition.Generator
                                                        .UnresolvedCombination(List.of(subject),
                                                        souther.compiler.partition.Generator
                                                                .UnresolvedCombination.Reason
                                                                .NO_CERTIFIED_WITNESS),
                                                within, built.unrepresented());
                };
            }
            case souther.compiler.partition.Generator.BoundaryAttempt.Unresolved left ->
                    new ItemAssessment.Attempt.Unresolved(left.why(), within,
                            left.unrepresented());
            // And a search a budget of this compiler's ended, which is the one outcome here that
            // names something anybody could raise. Said as the one above, an obligation this
            // declined to work on left the count as one the model admits no row at.
            case souther.compiler.partition.Generator.BoundaryAttempt.Stopped left ->
                    new ItemAssessment.Attempt.Stopped(left.why(), within, left.unrepresented(),
                            PublicationOrders.COMPOSITION_BUDGETS.keep(left.met().figures()),
                            PublicationOrders.COMPOSITION_REPERTOIRES.keep(left.met().populations()),
                            PublicationOrders.COMPOSITION_CAPACITIES.keep(left.met().unheld()));
            // A search that ran to the end of what this compiler writes, where that is not the end
            // of what there is to write. It leaves the point open the way the one above does and
            // names nothing anybody could raise, which is why it arrives as its own arm and its
            // gap holds a vocabulary of its own.
            case souther.compiler.partition.Generator.BoundaryAttempt.Unexhausted left ->
                    new ItemAssessment.Attempt.Unexhausted(left.why(), within,
                            left.unrepresented(),
                            PublicationOrders.COMPOSITION_REPERTOIRES.keep(left.met().populations()),
                            PublicationOrders.COMPOSITION_CAPACITIES.keep(left.met().unheld()));
            // A search that ran to the end of what it was handed, where what it was handed was
            // short of the point. It names a figure like the one above and its word is its own, so
            // the two are carried side by side rather than one being read off the other.
            case souther.compiler.partition.Generator.BoundaryAttempt.Limited left ->
                    new ItemAssessment.Attempt.Limited(left.why(), within, left.unrepresented(),
                            PublicationOrders.COMPOSITION_BUDGETS.keep(left.by()),
                            NO_REPERTOIRES, NO_CAPACITIES);
            // And a point no search was made for at all. It names a figure like the two above and
            // is not an outcome of a search, which is what keeps it out of what the readings of a
            // line together establish.
            case souther.compiler.partition.Generator.BoundaryAttempt.Unplanned left ->
                    new ItemAssessment.Attempt.Unplanned(left.why(), within, left.unrepresented(),
                            PublicationOrders.COMPOSITION_BUDGETS.keep(left.by()));
        };
    }

    /**
     * What was established about each line a body draws between two of its positions.
     *
     * <p>Beside the lines an axis carries rather than among them. A line between two positions is on
     * neither of them, so there is no axis to hang it off — and a behavior can have one while having
     * no axis at all, which is every model whose inputs are plain numbers nothing bounds.
     *
     * <p>Nothing is promised of one yet, and the projection says so in the one word for it. Whether
     * a row can be written on the line takes a place both positions admit, and reading each position
     * on its own does not answer that: two ranges overlapping is not two positions holding a pair,
     * and what refuses the pair need not be in either range. So the reading is not made rather than
     * made and coming to nothing, and the line is one nothing has shown to be writable — reported and
     * not counted, the same account any other unpromised edge gets.
     */
    static List<ReadingOfALine> assessBetween(
            souther.compiler.partition.MeasuredInput subject,
            souther.compiler.query.Adequacy.RowReading observed,
            RowsPutToTheLines put, ReachingCuts reaching) {
        Partitions.Partitioning partitioning = subject.partitioning();
        // One entry per reading, the way a line at a place is read: what several readings of one
        // line come to is one answer, and it is put together where the last thing that is a
        // reading's own has been asked ({@link #merged}).
        List<ReadingOfALine> out = new ArrayList<>();
        MeasuredInput.Lines read = subject.lines();
        for (Border each : partitioning.between()) {
            out.add(assessed(each, reading(read.at(each),
                            ItemAssessment.WritabilityProjection.NOT_COMPUTED,
                            elsewhere(partitioning.between(), each), wayTo(each, reaching),
                            subject.quantities().region()),
                    observed, put));
        }
        return List.copyOf(out);
    }

    /**
     * What a reading of the rows comes to, once what could not be read is accounted for.
     *
     * <p>A row standing where the line is that nothing watched reach the comparison is counted here
     * as a row that did not meet the point. It is a miss the measure can hide: what the rows went
     * without is said below, and a run nobody watched is one of the things it says. So the
     * distinction the walk makes is not carried further — a hit needs a row seen reaching the
     * comparison, and everything else is answered by how whole the reading was.
     */
    private static Measurement<ItemAssessment.Coverage> verdictOf(
            StandingAtAPoint.Met met, Supplier<RowWitnesses> whoStandsThere, boolean guard,
            Border border, Adequacy.RowReading observed) {
        if (met instanceof StandingAtAPoint.Met.Reached) {
            // Found is found: a row settles this whatever else went unread, so nothing weakens it.
            return new Measurement.Complete<>(new ItemAssessment.Coverage.Hit(whoStandsThere.get()));
        }
        // What is not found is undecided rather than absent, wherever the reading behind it was not
        // whole — and now says which reading it was. A row whose value here could not be read; a row
        // nothing read at all, which may be the row that is at this value; and, for a line a fork
        // drew, a row that never finished and so never reached the comparison.
        Set<Weakening> by = new LinkedHashSet<>();
        // One per reason, each in its own words. What the rows leave open is the same whichever it
        // was — no row of theirs settles the point — and why there was nothing to read is not, so
        // every reason travels even where this block treats them alike.
        if (met instanceof StandingAtAPoint.Met.CouldNotTell it) {
            for (souther.compiler.partition.ReadingGap why : it.why()) {
                by.add(new Weakening.BorderValueUnreadable(border, why));
            }
            // And the readings nobody made, which is not one of the reasons the ones that were made
            // came to nothing. Both can be true of one point, so this is asked beside them rather
            // than after them.
            if (it.tried() instanceof StandingAtAPoint.ReadingsTried.StoppedAtTheLimit stopped) {
                by.add(new Weakening.BorderReadingsNotExhausted(border, stopped.limits()));
            }
        }
        for (Incompleteness.Met gap : observed.gaps()) {
            // Rows nothing read at all bear on every line. Rows that were read and did not finish
            // bear on a line a fork drew and on no other: meeting one takes the comparison having
            // run, which a row that stopped never reached.
            //
            // Read off the reasons rather than off the dispositions beside them. What a row that
            // stopped costs a measure is said once, where the row stopped (`ExampleVerifier`), and
            // a second reading here was a second statement of it that could differ (issue #996).
            if (gap.fact().code().leftNoRowRead()
                    || (guard && gap.fact().scope() == Incompleteness.Scope.ROW)) {
                by.add(new Weakening.ObservationIncomplete(gap));
            }
        }
        ItemAssessment.Coverage seen = new ItemAssessment.Coverage.NoHit();
        return by.isEmpty() ? new Measurement.Complete<>(seen)
                : new Measurement.Partial<>(seen, WeakeningSet.ofAll(by));
    }

    /**
     * Why nothing was read against a line at all, or null where the rows are what answer it.
     *
     * <p>The gates, behind one name. Which of them a line goes through is settled by what the
     * reading in hand was made of and by whether a fork or an invariant drew it, and that is one
     * decision with one owner — a caller writing the choice out again, and a check enumerating what
     * a reading can come to, would be two more statements of it, free to say what this stopped
     * saying.
     */
    static Measurement<ItemAssessment.Coverage> whyNothingWasReadAgainstTheLine(
            boolean drawnByAFork,
            souther.compiler.query.Adequacy.RowReading observed) {
        return drawnByAFork ? whyNoGuardLine(observed) : whyNoInvariantLine(observed);
    }

    /**
     * The first gate a {@code guard}'s line did not get through.
     *
     * <p>Its own path, because a guard's line and an invariant's are not measured the same way and so
     * cannot fail to be measured for the same reasons. Meeting this one takes the comparison having
     * run, which puts the arms in front of the rows: nothing a row carries decides it until the
     * classes that record where the row went exist and survived.
     */
    private static Measurement<ItemAssessment.Coverage> whyNoGuardLine(
            souther.compiler.query.Adequacy.RowReading observed) {
        Measurement<ItemAssessment.Coverage> nobodyAsked = whyNothingWasAsked(observed);
        if (nobodyAsked != null) {
            return nobodyAsked;
        }
        if (!observed.recordedArms()) {
            return new Measurement.NotMeasured<>(ItemAssessment.Coverage.NotAsked.ARMS_NOT_ASKED);
        }
        if (observed.armsUnseen()) {
            // Started and not finished, so it says what it went without.
            Set<Weakening> by = new LinkedHashSet<>();
            for (Incompleteness.Met gap : observed.gaps()) {
                by.add(new Weakening.ObservationIncomplete(gap));
            }
            return new Measurement.FailedToMeasure<>(
                    ItemAssessment.Coverage.CouldNotAsk.ARMS_UNREADABLE, WeakeningSet.ofAll(by));
        }
        return whyNoInvariantLine(observed);
    }

    /** What every line of every kind says where nothing was asked of the rows: the rules drew it,
     *  and nothing was read against it. Asked before either path below, because neither of them is
     *  about a run that did not happen. */
    private static Measurement<ItemAssessment.Coverage> whyNothingWasAsked(
            souther.compiler.query.Adequacy.RowReading observed) {
        return observed.rowsWereRead() ? null
                : new Measurement.NotMeasured<>(ItemAssessment.Coverage.NotAsked.NOT_ASKED);
    }

    /**
     * The first gate an invariant's line did not get through.
     *
     * <p>Only the one: nothing outside the bound can be constructed, so writing the value is the
     * whole of what there is to reach and no instrumentation is owed. This is why the two origins
     * are asked separately — an invariant's line can never be waiting on the arms, and a measure
     * that could say so would be able to say something that is not true of it.
     */
    private static Measurement<ItemAssessment.Coverage> whyNoInvariantLine(
            souther.compiler.query.Adequacy.RowReading observed) {
        Measurement<ItemAssessment.Coverage> nobodyAsked = whyNothingWasAsked(observed);
        if (nobodyAsked != null) {
            return nobodyAsked;
        }
        List<RowOutcome> rows = observed.rowsSeen();
        boolean someRowsUnseen = observed.someRowsUnseen();
        // Nothing read is not the same as nothing written. A source that could not be evaluated may
        // hold the row that is at this line, so the question is undecided rather than unasked, and
        // the reading below settles it that way.
        return rows.isEmpty() && !someRowsUnseen
                ? new Measurement.NotMeasured<>(ItemAssessment.Coverage.NotAsked.NO_ROWS) : null;
    }


    private Coverages() {}

}
