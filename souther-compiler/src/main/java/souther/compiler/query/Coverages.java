package souther.compiler.query;

import souther.compiler.check.ReadingPolicy;
import souther.compiler.ast.Hir;
import souther.compiler.check.PathReachability;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.numeric.Place;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.observe.Classification;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.Counting;
import souther.compiler.observe.RowOutcome;
import souther.compiler.partition.Axis;
import souther.compiler.partition.AxisId;
import souther.compiler.partition.Border;
import souther.compiler.partition.Criterion;
import souther.compiler.partition.ReachingCuts;
import souther.compiler.partition.Demand;
import souther.compiler.partition.PointRole;
import souther.compiler.partition.BorderQuantity;
import souther.compiler.partition.LevelRealizer;
import souther.compiler.partition.Realization;
import souther.compiler.inputs.InputDomain;
import souther.compiler.partition.EnsuresThresholds;
import souther.compiler.partition.GuardThresholds;
import souther.compiler.partition.BoundaryLine;
import souther.compiler.partition.PartitionClass;
import souther.compiler.partition.Partitions;
import souther.compiler.partition.BehaviorInputs;
import souther.compiler.partition.InputClassifications;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

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
     * the geometry a thing no answer could hold (issue #1001).
     *
     * <p>Handed over together because they are produced together and reading is what costs: every
     * rule of every parameter is read to arrive at either, and a caller that wanted both and asked
     * twice would read them twice.
     */
    record Partitioned(Partitions.Partitioning geometry,
                       souther.compiler.inputs.Quantities reading) {}

    /**
     * The positions one behavior is measured at, with what its own comparisons divide them into.
     *
     * <p>Asked here rather than worked out again wherever it is needed. What a report says is not
     * covered and what a generator writes a row for have to be the same positions and the same classes,
     * and two derivations of them would be two chances to disagree.
     */
    static Partitioned partitioningOf(Hir.SpecBehavior behavior, InputDomain inputs,
                                      Sig sig, Symbols symbols, ReadingPolicy policy,
                                      Core body,
                                      souther.compiler.check.ElementBindings elements,
                                      CoverageSites.Plan plan,
                                      PathReachability.Answers arrives,
                                      souther.compiler.check.StatedContract stated) {
        List<String> parameters = behavior.params().stream().map(Hir.Param::name).toList();
        // What a row's values are, where they sit and what they are written as, read together:
        // a field under a name is reached by taking the name off, and a walk given the paths
        // alone reaches nothing where the derivation reaches a field.
        BehaviorInputs where = new BehaviorInputs(parameters, sig.inputTypes(), symbols, policy);
        // Read once for the three below, and handed back beside what they produce. What it holds is
        // a way of asking the declarations reaching this input a further question, and each of them
        // asking for its own would read every rule of every parameter three times over to arrive at
        // the same answers.
        souther.compiler.inputs.Quantities quantities = inputs.quantities(symbols);
        Partitions.Partitioning partitioning =
                Partitions.of(behavior.name(), inputs, quantities, symbols, policy);
        // What the behavior states about its own answer, which is read whether or not anything
        // implements it: a clause is written against the declaration, so an injected behavior draws
        // its lines like any other and there is no body for them to have come out of.
        EnsuresThresholds.Clauses clauses =
                EnsuresThresholds.of(stated, inputs, quantities, symbols);
        GuardThresholds.Guards guards = body == null ? GuardThresholds.Guards.NONE
                : GuardThresholds.of(behavior.name(), body, plan, inputs, quantities,
                        symbols, elements);
        // Both producers of one kind of line, put together before the position is divided. Two
        // rules at one value are one cut and stay separate obligations, which is what the merge
        // below does — applied one producer at a time, a clause and a guard naming one number would
        // divide the position twice.
        return new Partitioned(Partitions.withThresholds(partitioning, quantities,
                both(clauses.thresholds(), guards.thresholds()), symbols, policy,
                both(clauses.unread(), guards.unread()),
                both(clauses.singled(), guards.singled()),
                both(clauses.between(), guards.between()), arrives,
                // What each comparison raised and what the reading of it answered, from both
                // producers. Carried rather than derived from the lines that came back: a
                // comparison this could not read draws no line, and that is when its questions
                // stand.
                both(clauses.accounting(), guards.accounting()),
                // What a row had to satisfy to arrive at each comparison, from the walk that
                // assumed it. A clause of a declaration is not written at a place in a body and has
                // nothing on the way to it, so only the guards have any of this.
                guards.reaching()), quantities);
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
     * @param partitioning what the model divides this behavior into, made once by
     *                   {@link souther.compiler.query.Adequacy.Divided} and read here. Worked out
     *                   again on the way in, this and the boundaries beside it would be two
     *                   derivations of one thing and two chances to disagree about it
     * @param boundaries what was established about every line this behavior's rules drew, made once
     *                   by {@link souther.compiler.query.Adequacy.Boundaries} and read here. Measuring
     *                   a line takes putting a value through the module's decoders, which is not
     *                   something a coverage count can do on its own and not something that should
     *                   happen twice.
     */
    static PartitionEvidence of(Hir.SpecBehavior behavior, InputDomain inputs, Sig sig,
                                Symbols symbols, ReadingPolicy policy,
                                Partitions.Partitioning partitioning,
                                souther.compiler.query.Adequacy.RowReading observed,
                                souther.compiler.query.Adequacy.Level level,
                                List<BorderAssessment> boundaries,
                                souther.compiler.partition.AdequacyPolicy.OfTheMeasures budget) {
        List<RowOutcome> rows = observed.rowsSeen();
        List<String> parameters = behavior.params().stream().map(Hir.Param::name).toList();
        // What a row's values are, where they sit and what they are written as, read together:
        // a field under a name is reached by taking the name off, and a walk given the paths
        // alone reaches nothing where the derivation reaches a field.
        BehaviorInputs where = new BehaviorInputs(parameters, sig.inputTypes(), symbols, policy);

        List<PartitionEvidence.AxisCoverage> axes = new ArrayList<>();

        List<Axis> divided = new ArrayList<>();
        List<PartitionEvidence.Unanswered> standing = new ArrayList<>();
        Readings readings = Readings.of(rows, where, partitioning.axes(),
                observed.gaps().stream()
                        .filter(gap -> gap.code().leftNoRowRead()).toList());
        for (Axis axis : partitioning.axes()) {
            // What the model asked about this position and nothing answered, said before anything
            // here decides whether the position could be measured. The questions are the model's;
            // `undivided` below explains why no evidence came back, which is a nothing of its own
            // and carries no word about what was written there.
            standing.addAll(unansweredAt(axis));
            if (!axis.measurable()) {
                continue;   // said by `undivided`, which also says which kind of nothing it is
            }
            if (axis.derivable()) {
                axes.add(coverageOf(axis, readings, level.readsRows()));
                divided.add(axis);
            }
        }
        // And what a body's and a declaration's comparisons left standing, which no axis carries:
        // the position a comparison is about need not be one anything divided.
        //
        // By the rule and the question, which is what one occurrence of a question is. A comparison
        // inside a helper is read once per call and is one rule (`RuleRef`), so readings of it are
        // one question raised once — walked as a list, a document says the same thing as many times
        // as the walk met it, and a consumer cannot tell that from two rules asking alike. Keyed on
        // the identity and not on everything an entry happens to carry, so a handle changing shape
        // cannot quietly turn one question into two.
        Set<java.util.Map.Entry<souther.compiler.check.RuleRef, souther.compiler.check.Owed>> asked =
                new LinkedHashSet<>();
        for (souther.compiler.partition.GuardThresholds.Guards.AtAPosition each
                : partitioning.compared()) {
            for (souther.compiler.check.RuleAccounting.Unanswered open
                    : each.accounting().unansweredQuestions()) {
                if (!asked.add(java.util.Map.entry(open.rule(), open.owed()))) {
                    continue;
                }
                standing.add(new PartitionEvidence.Unanswered(open, each.at().toString(),
                        // Spelled by the term itself, which is the one thing that spells a term. A
                        // second spelling here is a second key for one subject, and a document
                        // promises `String.length(code)` beside `code`.
                        measureSaid(open.owed().subject(), each)));
            }
        }
        // Each measure asked its own closure, and neither told from the length of what came back.
        // What one of them is short of says nothing about the other: a rule whose line nothing
        // could read leaves the border measure short while the classes either side of it were read
        // in full, and the enumeration above is the same case the other way round.
        return new PartitionEvidence(
                PartitionDerivation.of(axes, partitioning.partitionClosure()),
                BoundaryDerivation.of(boundaries, partitioning.borderClosure()),
                pairsOf(behavior.name(), divided, readings, level.readsRows(), budget),
                partitioning.undivided(), partitioning.unread(), partitioning.blocked(),
                partitioning.notSeparated(), List.copyOf(standing),
                whyUnclassified(readings.byRow(),
                        partitioning.axes().stream().map(Axis::id).toList()));
    }

    /**
     * Why the rows that could not be placed could not be placed — one reason per kind per position.
     *
     * <p>Not one per row. A hundred rows too large at the same position are one thing to say about
     * that position, and how many there were is the axis's count. Carrying the number here as well
     * would be the same fact under two names, and the two would be read side by side.
     *
     * <p>Walked in the order of {@code order} rather than of a row's own map, which is built with
     * {@code Map.copyOf} and so iterates in an order that changes between runs. A report that
     * changes between runs cannot be compared between runs.
     */
    static List<Incompleteness> whyUnclassified(List<Map<AxisId, Classification>> byRow,
                                                List<AxisId> order) {
        Map<Object, Incompleteness> byKind = new LinkedHashMap<>();
        for (Map<AxisId, Classification> where : byRow) {
            for (AxisId axis : order) {
                // Asked of every reading and not of the ones that placed nothing. A row that put
                // one value in a class and could not read the value beside it is counted among the
                // rows that could not say, so the reason it could not say is owed here too — left
                // to the arm, the count went up and the report said nothing about why.
                Classification said = where.get(axis);
                if (said != null && said.stopped() != null) {
                    byKind.putIfAbsent(said.stopped().identity(), said.stopped());
                }
            }
        }
        return List.copyOf(byKind.values());
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
    private record Readings(List<Map<AxisId, Classification>> byRow, List<Incompleteness> unseen) {

        static Readings of(List<RowOutcome> rows, BehaviorInputs where, List<Axis> axes,
                           List<Incompleteness> unseen) {
            List<Map<AxisId, Classification>> read = new ArrayList<>();
            for (RowOutcome row : rows) {
                read.add(InputClassifications.of(row.inputs(), where, axes));
            }
            return new Readings(List.copyOf(read), List.copyOf(unseen));
        }

        boolean someRowsUnseen() {
            return !unseen.isEmpty();
        }

        boolean noRows() {
            return byRow.isEmpty();
        }

        /**
         * Which classes a row fell in at one position, or nothing where it did not say.
         *
         * <p>More than one where the position is inside a sequence and the row's elements did not
         * fall together. Nothing where the row could not be read there, which is a different answer
         * from a row whose list held no element — that one is read and falls in no class.
         */
        static List<String> classesIn(Map<AxisId, Classification> where, Axis axis) {
            return where.get(axis.id()) instanceof Classification.Classified in ? in.classIds()
                    : null;
        }

        /** Whether the row could not read some value at {@code axis}, whatever else it placed. */
        static boolean stoppedAt(Map<AxisId, Classification> where, Axis axis) {
            Classification said = where.get(axis.id());
            return said != null && said.stopped() != null;
        }

        /** How many rows could not say where they were at this position. */
        int couldNotSay(Axis axis) {
            // A row that could not read a value here, whatever else it placed. One that read every
            // value and put none in a class is not one of these: it was read, and says so.
            return (int) byRow.stream().filter(where -> stoppedAt(where, axis)).count();
        }

        /**
         * Whether every row that bears on {@code axes} said where it was at all of them.
         *
         * <p>Only then does a class or a combination nothing sits in mean nothing reaches it. One row
         * that could not be placed at one of the positions leaves every class of that position, and
         * every combination it takes part in, undecided rather than untried.
         */
        WeakeningSet weakening(List<Axis> axes) {
            Set<Weakening> out = new LinkedHashSet<>();
            for (Incompleteness gap : unseen) {
                out.add(new Weakening.ObservationIncomplete(gap));
            }
            // One reason per kind per position, which is what a hundred rows too large at one
            // position are: how many there were is the count beside this, and carrying the number
            // here as well would be the same fact under two names.
            Map<Object, Incompleteness> byKind = new LinkedHashMap<>();
            for (Map<AxisId, Classification> where : byRow) {
                for (Axis axis : axes) {
                    Classification said = where.get(axis.id());
                    if (said != null && said.stopped() != null) {
                        byKind.putIfAbsent(said.stopped().identity(), said.stopped());
                    }
                }
            }
            byKind.values().forEach(gap -> out.add(new Weakening.ObservationIncomplete(gap)));
            return WeakeningSet.ofAll(out);
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
    private static PartitionEvidence.PairSpace pairsOf(String behavior, List<Axis> axes,
                                                      Readings readings, boolean asked,
                                                      souther.compiler.partition.AdequacyPolicy
                                                              .OfTheMeasures budget) {
        // The product of what a row can be written at, not of what the types declare. A case the
        // rules refuse is not a class of its position at all, so the slice of the product it would
        // have taken part in is not here to be counted — which is a different thing from a pair
        // whose two classes each have rows but never together.
        //
        // And a pair no value is in is not one either. A position under one case of a sum and a
        // position under another are not in one value, so their classes make no combination: counted
        // as the product, the measure of a behavior taking a sum would fall by however many
        // combinations the model does not have.
        long total = 0;
        for (int i = 0; i < axes.size(); i++) {
            for (int j = i + 1; j < axes.size(); j++) {
                total += combinationsOf(axes.get(i), axes.get(j));
            }
        }
        if (total == 0) {
            return PartitionEvidence.PairSpace.NONE;
        }
        // Before anything about the rows, because there are none to be about: a build that asked for
        // no measurement read no row, and how large the space is stays what the model says it is.
        if (!asked) {
            return PartitionEvidence.PairSpace.notAsked((int) Math.min(total, Integer.MAX_VALUE));
        }
        // Before the size of the space is worth mentioning. A combination nothing tried to sit in is
        // not a combination left untried by anybody, and how many of them there are says nothing
        // about a behavior no row names.
        if (readings.noRows() && !readings.someRowsUnseen()) {
            return PartitionEvidence.PairSpace.noRows((int) Math.min(total, Integer.MAX_VALUE));
        }
        if (total > budget.pairSpace()) {
            return PartitionEvidence.PairSpace.truncated(behavior, total, budget.pairSpace());
        }
        Set<String> covered = new LinkedHashSet<>();
        for (Map<AxisId, Classification> where : readings.byRow()) {
            for (int i = 0; i < axes.size(); i++) {
                for (int j = i + 1; j < axes.size(); j++) {
                    // Every pairing the row reaches, and only those. A row whose list holds
                    // elements either side of a line stands in both classes there, and which of
                    // them went with what the position beside it holds is settled by which element
                    // each came from — taken as every combination, a row is evidence for a pair
                    // none of its elements is in.
                    for (Map.Entry<String, String> pair : Classification.pairsOf(
                            where.get(axes.get(i).id()), where.get(axes.get(j).id()))) {
                        // Which positions, and not only which classes. A class id is unique within
                        // its axis and not across axes — three `Flag` inputs all have a `Yes` — so
                        // a key of two class names alone collapses every pair one row covers into
                        // one.
                        covered.add(i + "/" + pair.getKey() + " " + j + "/" + pair.getValue());
                    }
                }
            }
        }
        int reached = covered.size();
        PartitionEvidence.PairSpace.PairCounts counts = new PartitionEvidence.PairSpace.PairCounts(
                reached, reached, 0, (int) total - reached);
        WeakeningSet by = readings.weakening(axes);
        return new PartitionEvidence.PairSpace((int) total, by.isEmpty()
                ? new Measurement.Complete<>(counts) : new Measurement.Partial<>(counts, by));
    }

    /**
     * How many combinations two positions' classes make between them.
     *
     * <p>The product where the two are in one value, and less where they are not. What a row at a
     * class has to be is one merge ({@link souther.compiler.inputs.Requirements}), and the same
     * merge is what the generator asks before it composes a row — so what is counted here and what
     * a row is offered for come from one reading rather than from two that agree until a case is
     * added.
     */
    private static long combinationsOf(Axis one, Axis other) {
        long count = 0;
        for (PartitionClass here : one.classes()) {
            for (PartitionClass there : other.classes()) {
                if (one.requiring(here).compatibleWith(other.requiring(there))) {
                    count++;
                }
            }
        }
        return count;
    }

    /**
     * The questions the rules about one position raise that nothing answered, as a document says
     * them.
     *
     * <p>Read off the axis because that is what carries a position's accounting here, and not
     * because an axis owns the questions: one that could not be measured has them all the same.
     */
    private static List<PartitionEvidence.Unanswered> unansweredAt(Axis axis) {
        return axis.unanswered().stream()
                .map(each -> new PartitionEvidence.Unanswered(each, axis.path().toString(),
                        // The number the line falls on, where it falls on one. Which of the two the
                        // question is about was settled where it was raised — not here, and not by
                        // whatever a renderer has to hand.
                        each.owed().subject().measured() ? axis.term().toString() : null))
                .toList();
    }

    /**
     * What a comparison's question is about, as a report names it.
     *
     * <p>A place between two things names itself: it is on neither position, so nothing about the
     * position it was filed at spells it. A position's own subject is relative to where it is filed,
     * and the term it was measured by spells the rest.
     */
    private static String measureSaid(souther.compiler.check.Owed.Subject subject,
                                      souther.compiler.partition.GuardThresholds.Guards.AtAPosition
                                              filed) {
        // The number the line falls on, where it falls on one. A place between two moving terms has
        // none — writing one out is what naming it by its comparison exists not to do — and a
        // position's own values are named by the position.
        return subject instanceof souther.compiler.check.Owed.Subject.OfAPosition at
                && at.measured() && filed.term() != null ? filed.term().toString() : null;
    }

    private static PartitionEvidence.AxisCoverage coverageOf(Axis axis, Readings readings,
                                                             boolean asked) {
        List<String> classes = axis.classes().stream().map(PartitionClass::id).toList();
        // What the axis already says about which of this position's rules nothing accounted for,
        // each named. Read off the axis rather than worked out here, and in the questions' own
        // words: the vocabulary beside it says why a division could not be derived, which is a
        // different question, and borrowing it left a reader with a sentence that named neither
        // (issue #842).
        PartitionEvidence.AxisCoverage.Reading read = new PartitionEvidence.AxisCoverage.Reading(
                axis.rulesNotReached()
                        ? PartitionEvidence.AxisCoverage.Reach.SOME_OUT_OF_SIGHT
                        : PartitionEvidence.AxisCoverage.Reach.EVERY_RULE,
                // Of the questions standing at this position, the ones this measure is the reader
                // of. What classes are made of is which values may stand somewhere; where the line
                // falls is the border measure's question, and counting it here would put a number
                // #869 separated back together. The questions themselves are beside the measures
                // and are said there once.
                axis.unanswered().stream().noneMatch(each -> each.owed().obligation()
                        == souther.compiler.check.CoverageObligation.ADMITTED_VALUES));
        // Nothing a body claims is in scope here. What a row is owed at is counted first and on its
        // own, and what was declared about those positions is put beside it afterwards
        // ({@link ClaimReport}) — which is what keeps a claim from narrowing a denominator by being
        // in reach of the code that counts one.
        // Which classes there are is the model's answer and is above; what the rows reach of them is
        // below, and a build that asked for no measurement read no row.
        if (!asked) {
            return PartitionEvidence.AxisCoverage.notAsked(axis.id(),
                    axis.term().toString(), classes, read);
        }
        if (readings.noRows() && !readings.someRowsUnseen()) {
            return PartitionEvidence.AxisCoverage.noRows(axis.id(),
                    axis.term().toString(), classes, read);
        }
        Set<String> covered = new LinkedHashSet<>();
        for (Map<AxisId, Classification> where : readings.byRow()) {
            List<String> in = Readings.classesIn(where, axis);
            if (in != null) {
                covered.addAll(in);
            }
        }
        PartitionEvidence.AxisCoverage.Reached reached =
                new PartitionEvidence.AxisCoverage.Reached(covered, readings.couldNotSay(axis));
        WeakeningSet by = readings.weakening(List.of(axis));
        return new PartitionEvidence.AxisCoverage(axis.id(), axis.term().toString(),
                classes, read, by.isEmpty()
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
         * where {@code fixing} puts it, or null where the attempt could not be made at all — which
         * leaves the point unknown rather than refused.
         *
         * <p>One method, whatever the border was drawn on. What the row is for is the coverage item
         * and what is fixed to build it is a placement that stands for it; a side of a border is met
         * by a row anywhere in it, so a row labelled by the places a search happened to compose
         * would name a witness as though it were the item.
         */
        souther.compiler.partition.Generator.BoundaryAttempt attempt(
                String label,
                java.util.function.Function<souther.compiler.inputs.NumericTerm,
                        souther.compiler.check.Carrier> on,
                Map<souther.compiler.inputs.NumericTerm, Place> fixing);
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
     * @param armsAsked whether the build asked for the arms at all. Whether the run then managed to
     *                  read them is a second question, and {@code observed} answers it — the two fail
     *                  differently and a measure that took one boolean for both could not say which
     *                  had happened.
     * @param probe     null where the module's classes or the runtime are not there to build against
     * @param reaching  what a row had already satisfied when each comparison ran. Threaded here as
     *                  well as into {@link #assessBetween} because which shape of quantity a rule
     *                  cuts says nothing about where a row for it may be written — and a region put
     *                  into one of the two paths would leave the other searching over everything its
     *                  position could ever hold. No model was found where it moves an answer down
     *                  this path, and no test holds it: the points of a line at one position all sit
     *                  beside the line, and every line tried that the region excludes turned out to
     *                  be one {@link souther.compiler.check.PathReachability} had already taken the
     *                  obligation away for. Whether those two always coincide is not established
     *                  here — they are different readings — so what this says is that a path is not
     *                  left short of what it is owed, and not that the region is idle here.
     */
    static List<BorderAssessment> assess(
            Axis axis, BehaviorInputs where, souther.compiler.query.Adequacy.RowReading observed,
            souther.compiler.query.Adequacy.Level level, boolean knownWritable, Probe probe,
            souther.compiler.inputs.Quantities rules, ReachingCuts reaching,
            souther.compiler.numeric.NumericDomain.Bounds within) {
        // Keyed by the line rather than by the reading of it. A guard inside a non-recursive helper
        // is read once per call of that helper, and the rows do not owe the same border twice for
        // having been offered it twice; what each reading saw is merged below.
        java.util.SequencedMap<BoundaryLine, BorderAssessment> out = new java.util.LinkedHashMap<>();
        LevelRealizer realizer = new LevelRealizer();
        for (Border each : Partitions.bordersOf(axis, where.symbols(), within)) {
            out.merge(BoundaryLine.of(each),
                    assessed(each, shapeOf(each, where, knownWritable, probe,
                                    whenThereIsNoProbe(level), realizer,
                                    regionFor(each, rules, reaching)),
                            observed, level),
                    Coverages::whicheverSawMore);
        }
        return List.copyOf(out.values());
    }

    /**
     * Where a row for one border may be written.
     *
     * <p>Beside the border and not part of it. What a border is is what the rows are owed at, and it
     * is the same border wherever a row for it is looked for — put inside, two readings of one line
     * reached under different conditions would be two obligations, and a count of what an author
     * owes would move with how much of a body this compiler managed to read.
     *
     * <p>What the declarations leave, for a line a declaration draws. An invariant is about the
     * values and holds wherever one stands, so there is nothing on the way to it; a guard is at a
     * place in a body, and a row that never arrives there is no row at its line whatever it holds.
     * Read off which kind of rule it is rather than off whether anything was collected: a guard
     * nothing narrows and a clause are then the same region for the same stated reason, and each
     * says so in its own account rather than by coming back with nothing.
     */
    private static souther.compiler.partition.RegionForARow regionFor(
            Border border, souther.compiler.inputs.Quantities rules, ReachingCuts reaching) {
        return border.origin().comparisonAt()
                .map(site -> reaching.narrowing(rules.region(), site))
                .orElseGet(() -> souther.compiler.partition.RegionForARow.untouched(rules.region()));
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
        Met met(Criterion criterion, List<RowOutcome> rows);

        /** What building a row at it came to, asked only where one is worth building. */
        ItemAssessment.Attempt search(Criterion criterion, String label);

        /** Whether the rules this reading took in prove a row can be written at this border. */
        boolean provenWritable();
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
    private static BorderAssessment assessed(Border border, OneShapeOfBorder shape,
                                             souther.compiler.query.Adequacy.RowReading observed,
                                             souther.compiler.query.Adequacy.Level level) {
        // Whether meeting this border takes the comparison having run, asked of the rule rather than
        // read off which kind it is, and asked once for the border rather than once per point. A
        // guard's line is about a place in a body and is reached or not; an invariant's and a
        // clause's are about the values — one refuses everything outside its bound, the other states
        // a relation — so for both of those writing the value is the whole of what there is to reach.
        boolean guard = border.origin().comparisonAt().isPresent();
        Measurement<ItemAssessment.Coverage> absent = guard
                ? whyNoGuardLine(observed, level)
                : whyNoInvariantLine(observed, level);

        java.util.EnumMap<PointRole, ItemAssessment> items = new java.util.EnumMap<>(PointRole.class);
        for (PointRole role : PointRole.values()) {
            items.put(role, switch (border.demand(role)) {
                case Demand.NotOwed not -> new ItemAssessment.NotOwed(not.reason());
                case Demand.Owed owed -> {
                    Measurement<ItemAssessment.Coverage> coverage = absent != null ? absent
                            : verdictOf(shape.met(owed.criterion(), observed.rowsSeen()), guard,
                                    border, observed);
                    ItemAssessment.Attempt attempt = whereOneIsWorthBuilding(coverage,
                            () -> shape.search(owed.criterion(), border.label(role)));
                    yield new ItemAssessment.Owed(owed.criterion(), coverage,
                            writabilityOf(coverage, shape.provenWritable(), attempt), attempt);
                }
            });
        }
        return new BorderAssessment(border, items);
    }

    /**
     * One border, read on whatever it was drawn on.
     *
     * <p>The one reading. Whether a row sits at an item is the quantity's answer ({@link
     * BorderQuantity#standsAt}), where a row would have to stand is the quantity's too
     * ({@link BorderQuantity#standingAt}) and finding one there is the realizer's — so nothing here
     * asks which kind of line this is. Two readings written apart is what left a criterion about one
     * place reaching the reader of a pair as an {@code IllegalStateException}.
     */
    private static OneShapeOfBorder shapeOf(Border border, BehaviorInputs where,
                                            boolean knownWritable, Probe probe,
                                            ItemAssessment.Attempt.Reason whenThereIsNoProbe,
                                            LevelRealizer realizer,
                                            souther.compiler.partition.RegionForARow within) {
        BorderQuantity quantity = border.cut().of();
        java.util.Optional<souther.compiler.coverage.ComparisonOccurrence> site =
                border.origin().comparisonAt();
        return new OneShapeOfBorder() {

            @Override
            public Met met(Criterion criterion, List<RowOutcome> rows) {
                return metOn(quantity, where, rows, criterion, site);
            }

            @Override
            public ItemAssessment.Attempt search(Criterion criterion, String label) {
                // Which of the two nothings this is, said where the difference is known. A build
                // that asked for no values and a run with nothing to build against both arrive here
                // with no probe, and they license different sentences.
                if (probe == null) {
                    return new ItemAssessment.Attempt.NotAttempted(whenThereIsNoProbe);
                }
                // Where a row would have to stand is asked of the quantity, and finding one there of
                // the realizer. What it composes is a candidate and no part of the item: another row
                // in the same side is at the point as much as this one would be, so what the row is
                // offered for goes in beside it rather than being read back off it.
                return switch (realizer.realize(quantity.standingAt(criterion), within.where())) {
                    case Realization.Found found -> whatCameOfIt(
                            probe.attempt(label, quantity::carrierOf, found.fixing()),
                            label, within);
                    // And the two ways of finding nothing are not one answer. A walk of the whole
                    // of what the rules leave that reaches no value settles the point; a search
                    // that stopped, or one that composed no candidate at all, settles nothing
                    // (ADR-0091).
                    case Realization.Impossible _ -> new ItemAssessment.Attempt.Unresolved(
                            new souther.compiler.partition.Generator.UnresolvedCombination(
                                    java.util.List.of(label),
                                    souther.compiler.partition.Generator.UnresolvedCombination
                                            .Reason.THE_RULES_LEAVE_NOTHING_THERE), within);
                    case Realization.Unknown unknown -> switch (unknown.why()) {
                        case NOTHING_COMPOSED_ONE -> nothingComposedOne(label, within);
                        case THE_SEARCH_RAN_OUT -> new ItemAssessment.Attempt.Unresolved(
                                new souther.compiler.partition.Generator.UnresolvedCombination(
                                        java.util.List.of(label),
                                        souther.compiler.partition.Generator.UnresolvedCombination
                                                .Reason.SEARCH_LIMIT), within);
                    };
                };
            }

            @Override
            public boolean provenWritable() {
                return knownWritable;
            }
        };
    }

    /**
     * One row's values under one reading of it: an element chosen at each step inside a sequence
     * the line's positions take.
     *
     * <p>A row standing at a point is one of its readings standing there, and a reading has to be
     * one: two positions under one person are that person's two values, and offering the first
     * person's age beside the second person's status would have a row stand at a point neither
     * element is at. So an element is chosen per step and every position takes the one chosen for
     * the steps it shares — the same rule a pair of classes is read by, since it is the same
     * question.
     *
     * <p>Which readings there are is not known before the quantity has asked, since which positions
     * a line is over is its to say. So the choices are collected as it asks and the reading is run
     * again under each, until one stands or they are used up.
     */
    private static final class OneReadingOfARow implements BorderQuantity.Observation {

        private final BehaviorInputs where;
        private final RowOutcome row;
        /** The element chosen at each step, for this reading. */
        private final Map<souther.compiler.inputs.TermPath, Integer> chosen;
        /** How many elements each step was found to have, over every reading so far. */
        private final Map<souther.compiler.inputs.TermPath, Integer> held;
        private boolean wroteNothing;
        private boolean unreadable;

        OneReadingOfARow(BehaviorInputs where, RowOutcome row,
                         Map<souther.compiler.inputs.TermPath, Integer> chosen,
                         Map<souther.compiler.inputs.TermPath, Integer> held) {
            this.where = where;
            this.row = row;
            this.chosen = chosen;
            this.held = held;
        }

        @Override
        public souther.compiler.observe.ObservedValue at(souther.compiler.inputs.TermPath path) {
            List<BehaviorInputs.Occurrence> values = where.occurrencesAt(row.inputs(), path);
            if (values == null) {
                unreadable = true;
                return null;   // the walk and the type disagree, which is the quantity's to report
            }
            if (values.isEmpty()) {
                // The row wrote no element here, so nothing of it stands anywhere on this line.
                // That is a row that was read and does not reach the point, and reporting it as a
                // value nothing could read leaves the point undecided over a row that plainly
                // settles it.
                wroteNothing = true;
                return null;
            }
            for (BehaviorInputs.Occurrence each : values) {
                each.at().forEach((step, ordinal) ->
                        held.merge(step, ordinal + 1, Math::max));
            }
            for (BehaviorInputs.Occurrence each : values) {
                if (agrees(each)) {
                    return each.value();
                }
            }
            // No value here under this reading. Not a stop: the reading names an element this
            // position does not have, and another reading is where its values are.
            return null;
        }

        /** Whether {@code each} was reached through the elements this reading chose. */
        private boolean agrees(BehaviorInputs.Occurrence each) {
            for (Map.Entry<souther.compiler.inputs.TermPath, Integer> step : each.at().entrySet()) {
                Integer picked = chosen.get(step.getKey());
                if (picked != null && !picked.equals(step.getValue())) {
                    return false;
                }
            }
            return true;
        }

        /** Whether the row wrote nothing at some position this line is over. */
        boolean wroteNothing() {
            return wroteNothing;
        }

        /** Whether some position this line is over could not be read at all. */
        boolean unreadable() {
            return unreadable;
        }
    }

    /**
     * The readings of one row a point is tried against.
     *
     * <p>The first is run before the rest are known: which steps the line's positions take is the
     * quantity's to say as it reads them, so it says so by being asked once. Every choice those
     * steps allow follows it.
     */
    private static List<OneReadingOfARow> readings(BehaviorInputs where, RowOutcome row,
                                                   BorderQuantity quantity, Criterion criterion,
                                                   OneReadingOfARow first,
                                                   Map<souther.compiler.inputs.TermPath,
                                                           Integer> held) {
        quantity.standsAt(criterion, first);
        List<OneReadingOfARow> out = new ArrayList<>();
        for (Map<souther.compiler.inputs.TermPath, Integer> choice : readingsOver(held)) {
            out.add(new OneReadingOfARow(where, row, choice, held));
        }
        return out;
    }

    /**
     * Every reading of a row over the steps {@code held} says its positions take.
     *
     * <p>One choice per step, in every combination — which is a product and not a zip, because two
     * steps a row's positions do not take together are two independent choices. Bounded, since a
     * row holding several long lists has more readings than a measure is worth.
     */
    private static List<Map<souther.compiler.inputs.TermPath, Integer>> readingsOver(
            Map<souther.compiler.inputs.TermPath, Integer> held) {
        List<Map<souther.compiler.inputs.TermPath, Integer>> out = new ArrayList<>();
        out.add(Map.of());
        for (Map.Entry<souther.compiler.inputs.TermPath, Integer> step : held.entrySet()) {
            List<Map<souther.compiler.inputs.TermPath, Integer>> wider = new ArrayList<>();
            for (Map<souther.compiler.inputs.TermPath, Integer> each : out) {
                for (int i = 0; i < step.getValue() && wider.size() < MOST_READINGS; i++) {
                    Map<souther.compiler.inputs.TermPath, Integer> deeper =
                            new LinkedHashMap<>(each);
                    deeper.put(step.getKey(), i);
                    wider.add(deeper);
                }
            }
            out = wider;
        }
        return out;
    }

    /** How many readings of one row a point is tried against. */
    private static final int MOST_READINGS = 256;

    /**
     * Whether any row stands at one item of a border.
     *
     * <p>One walk for every kind of line. What a row put at the item is the quantity's to read — it
     * is the one thing that knows what it is a quantity of — and what this adds is the two facts that
     * belong to the rows: that a row nothing could read leaves the item undecided rather than missed,
     * and that a line a fork drew is met by getting the comparison to answer as well.
     *
     * @param site which comparison a row has to have got an answer out of, for a rule that meeting
     *             takes more than standing at the level. Empty where standing there is the whole
     *             of it
     */
    private static Met metOn(BorderQuantity quantity, BehaviorInputs where, List<RowOutcome> rows,
                             Criterion criterion,
                             java.util.Optional<souther.compiler.coverage.ComparisonOccurrence>
                                     site) {
        boolean unreadable = false;
        for (RowOutcome row : rows) {
            // A row has more than one value at a position inside a sequence, and standing at a point
            // is one element standing there. Asked for one value, such a row answered with none and
            // every point on such a line came back undecided — a measurement that could not look,
            // said of a row that wrote the values plainly.
            // The first reading both answers the point and says which steps the line's positions
            // take; the rest are tried under each choice those steps allow.
            Map<souther.compiler.inputs.TermPath, Integer> held = new LinkedHashMap<>();
            OneReadingOfARow first = new OneReadingOfARow(where, row, Map.of(), held);
            boolean stands = false;
            boolean stopped = false;
            for (OneReadingOfARow reading : readings(where, row, quantity, criterion, first, held)) {
                switch (quantity.standsAt(criterion, reading)) {
                    // A reading that could not look, unless what it could not find was an element
                    // the row wrote none of — that is a row that was read and does not stand, and
                    // said of the reading it happened in rather than of the row, since another
                    // reading of the same row may reach the point.
                    case UNREADABLE -> stopped = stopped || !reading.wroteNothing();
                    case NO -> { }
                    case YES -> stands = true;
                }
                if (stands) {
                    break;
                }
            }
            if (stands && site.stream().allMatch(seenBy(row)::reached)) {
                return Met.YES;
            }
            unreadable = unreadable || stopped;
        }
        return unreadable ? Met.UNREADABLE : Met.NO;
    }

    /**
     * Which of two readings of one line the report keeps.
     *
     * <p>Existential and per point, the same way an arm is: a row met a point if it met it through
     * any reading of the line. So a reading that found a row outranks one that could not tell, which
     * outranks one that looked and found none, which outranks one that was never made. Anything else
     * would let a second call site of a helper take back what a row at the first one established.
     *
     * <p>Point by point rather than border by border. Two readings of one line are the same border
     * and can have seen different things at different points, and keeping whichever border saw more
     * on the whole would throw away a point the other one had.
     */
    private static BorderAssessment whicheverSawMore(BorderAssessment a, BorderAssessment b) {
        java.util.EnumMap<PointRole, ItemAssessment> kept = new java.util.EnumMap<>(PointRole.class);
        for (PointRole role : PointRole.values()) {
            kept.put(role, rank(b.at(role)) > rank(a.at(role)) ? b.at(role) : a.at(role));
        }
        return new BorderAssessment(a.border(), kept);
    }

    private static int rank(ItemAssessment item) {
        if (!(item instanceof ItemAssessment.Owed owed)) {
            // Two readings of one line owe the same points, so this is one of them against itself.
            return 0;
        }
        return switch (owed.coverage()) {
            case Measurement.Complete<ItemAssessment.Coverage> whole ->
                    whole.value() instanceof ItemAssessment.Coverage.Hit ? 3 : 1;
            // A reading made in part saw less than a settled one and more than none: found is
            // found either way, and what it did not find is undecided rather than absent.
            case Measurement.Partial<ItemAssessment.Coverage> part ->
                    part.value() instanceof ItemAssessment.Coverage.Hit ? 3 : 2;
            case Measurement.NotMeasured<ItemAssessment.Coverage> _,
                 Measurement.FailedToMeasure<ItemAssessment.Coverage> _ -> 0;
        };
    }

    /**
     * What was tried at one point, where anything was worth trying at all.
     *
     * <p>The two gates in one place because they are one rule and there are three searches. A point
     * a row already sits at needs no candidate, and one whose measurement never happened is not a
     * piece of work to hand to anybody — offered anyway, both put a specific row in front of an
     * author that may already be written. Written per search, the third one to be added skipped
     * them and said a search had run and failed at points nothing had looked at.
     */
    private static ItemAssessment.Attempt whereOneIsWorthBuilding(
            Measurement<ItemAssessment.Coverage> coverage,
            java.util.function.Supplier<ItemAssessment.Attempt> search) {
        if (ItemAssessment.Coverage.hit(coverage)) {
            return new ItemAssessment.Attempt.NotAttempted(
                    ItemAssessment.Attempt.Reason.A_ROW_IS_ALREADY_THERE);
        }
        if (!worthBuilding(coverage)) {
            return new ItemAssessment.Attempt.NotAttempted(
                    ItemAssessment.Attempt.Reason.NOT_MEASURED);
        }
        return search.get();
    }

    /** A search that came to nothing at {@code subject}, which is what a point is written as. */
    private static ItemAssessment.Attempt nothingComposedOne(
            String subject, souther.compiler.partition.RegionForARow within) {
        return new ItemAssessment.Attempt.Unresolved(
                new souther.compiler.partition.Generator.UnresolvedCombination(List.of(subject),
                        souther.compiler.partition.Generator.UnresolvedCombination.Reason
                                .NOTHING_COMPOSES_ONE), within);
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
    private static ItemAssessment.Attempt.Searched whatCameOfIt(
            souther.compiler.partition.Generator.BoundaryAttempt made, String subject,
            souther.compiler.partition.RegionForARow within) {
        return switch (made) {
            case null -> new ItemAssessment.Attempt.Unresolved(
                    new souther.compiler.partition.Generator.UnresolvedCombination(
                            List.of(subject),
                            souther.compiler.partition.Generator.UnresolvedCombination.Reason
                                    .LINKAGE_FAILED), within);
            case souther.compiler.partition.Generator.BoundaryAttempt.Built built ->
                    new ItemAssessment.Attempt.Built(built.row(), within);
            case souther.compiler.partition.Generator.BoundaryAttempt.Unresolved left ->
                    new ItemAssessment.Attempt.Unresolved(left.why(), within);
        };
    }

    /**
     * What was established about each line a body draws between two of its positions.
     *
     * <p>Beside the lines an axis carries rather than among them. A line between two positions is on
     * neither of them, so there is no axis to hang it off — and a behavior can have one while having
     * no axis at all, which is every model whose inputs are plain numbers nothing bounds.
     *
     * <p>Nothing is promised of one yet. Whether a row can be written on the line takes a place both
     * positions admit, and until that is read the line is one nothing has shown to be writable —
     * which is reported and not counted, the same account any other unpromised edge gets. Two ranges
     * overlapping is not two positions holding a pair, and what refuses the pair need not be in
     * either range.
     */
    static List<BorderAssessment> assessBetween(
            Partitions.Partitioning partitioning, souther.compiler.inputs.Quantities reading,
            BehaviorInputs where,
            souther.compiler.query.Adequacy.RowReading observed,
            souther.compiler.query.Adequacy.Level level, Probe probe) {
        // Keyed by the line the author drew, the way a line at a place is. A guard inside a
        // non-recursive helper is read once per call of that helper, and the rows do not owe the same
        // line twice for having been offered it twice — nor may one reading of it take back what
        // another established.
        java.util.SequencedMap<BoundaryLine, BorderAssessment> out = new LinkedHashMap<>();
        LevelRealizer realizer = new LevelRealizer();
        for (Border each : partitioning.between()) {
            out.merge(BoundaryLine.of(each),
                    assessed(each, shapeOf(each, where, false, probe, whenThereIsNoProbe(level),
                                    realizer,
                                    regionFor(each, reading,
                                            partitioning.reaching())), observed,
                            level),
                    Coverages::whicheverSawMore);
        }
        return List.copyOf(out.values());
    }

    /** What a reading of the rows comes to, once what could not be read is accounted for. */
    private static Measurement<ItemAssessment.Coverage> verdictOf(
            Met met, boolean guard, souther.compiler.partition.Border border,
            souther.compiler.query.Adequacy.RowReading observed) {
        List<RowOutcome> rows = observed.rowsSeen();
        if (met == Met.YES) {
            // Found is found: a row settles this whatever else went unread, so nothing weakens it.
            return new Measurement.Complete<>(new ItemAssessment.Coverage.Hit());
        }
        // What is not found is undecided rather than absent, wherever the reading behind it was not
        // whole — and now says which reading it was. A row whose value here could not be read; a row
        // nothing read at all, which may be the row that is at this value; and, for a line a fork
        // drew, a row that never finished and so never reached the comparison.
        Set<Weakening> by = new LinkedHashSet<>();
        if (met == Met.UNREADABLE) {
            by.add(new Weakening.BorderValueUnreadable(border));
        }
        for (Incompleteness gap : observed.gaps()) {
            // Rows nothing read at all bear on every line. Rows that were read and did not finish
            // bear on a line a fork drew and on no other: meeting one takes the comparison having
            // run, which a row that stopped never reached.
            //
            // Read off the reasons rather than off the dispositions beside them. What a row that
            // stopped costs a measure is said once, where the row stopped (`ExampleVerifier`), and
            // a second reading here was a second statement of it that could differ (issue #996).
            if (gap.code().leftNoRowRead()
                    || (guard && gap.scope() == Incompleteness.Scope.ROW)) {
                by.add(new Weakening.ObservationIncomplete(gap));
            }
        }
        ItemAssessment.Coverage seen = new ItemAssessment.Coverage.NoHit();
        return by.isEmpty() ? new Measurement.Complete<>(seen)
                : new Measurement.Partial<>(seen, WeakeningSet.ofAll(by));
    }

    /**
     * What says a row can be written at one boundary: the verdict, over the evidence there is.
     *
     * <p>The strongest evidence already in hand first. A row at the value went through the decoder,
     * which is the whole of what writable means, and costs nothing to read. Then the value that was
     * built, which went through the same decoder. Then the projection, which stands behind both rather
     * than in front of them: where it read every rule it proves the edge inhabited whatever the search
     * made of the particular candidates it tried.
     *
     * <p>Only the verdict is decided here. What was tried and what came of it is the attempt's to
     * say, and it is kept whether or not it changed this answer — an edge the projection proves is one
     * a search can still fail to reach, and a reader that had only this could not tell that it had.
     */
    private static ItemAssessment.Writability writabilityOf(
            Measurement<ItemAssessment.Coverage> coverage, boolean knownWritable,
            ItemAssessment.Attempt attempt) {
        if (ItemAssessment.Coverage.hit(coverage)) {
            return new ItemAssessment.Writability.WitnessedByRow();
        }
        if (attempt instanceof ItemAssessment.Attempt.Built) {
            return new ItemAssessment.Writability.WitnessedByConstruction();
        }
        // A refusal and an attempt nobody made leave the same verdict, and a projection that read
        // every rule proves what neither of them found. Which is where the asymmetry lives: nothing
        // a search does can take a proof away, because nothing a search does is evidence against.
        return knownWritable ? new ItemAssessment.Writability.ProvenByProjection()
                : new ItemAssessment.Writability.Unknown();
    }

    /**
     * Whether a candidate is worth building for this boundary.
     *
     * <p>A line nothing measured is not a line an author is behind on. Where the arms were not asked
     * for, a guard's line has no answer at all, and where a row went unread the row that is at this
     * value may be one of the rows nothing saw — building a candidate for either hands somebody a
     * specific piece of work that may already be done.
     */
    private static boolean worthBuilding(Measurement<ItemAssessment.Coverage> coverage) {
        return coverage instanceof Measurement.Complete<ItemAssessment.Coverage> whole
                        && whole.value() instanceof ItemAssessment.Coverage.NoHit
                || coverage instanceof Measurement.NotMeasured<ItemAssessment.Coverage> none
                        && none.why() == ItemAssessment.Coverage.NotAsked.NO_ROWS;
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
            souther.compiler.query.Adequacy.RowReading observed,
            souther.compiler.query.Adequacy.Level level) {
        Measurement<ItemAssessment.Coverage> nobodyAsked = whyNothingWasAsked(level);
        if (nobodyAsked != null) {
            return nobodyAsked;
        }
        if (!level.runsInstrumentedRows()) {
            return new Measurement.NotMeasured<>(ItemAssessment.Coverage.NotAsked.ARMS_NOT_ASKED);
        }
        if (observed.armsUnseen()) {
            // Started and not finished, so it says what it went without.
            Set<Weakening> by = new LinkedHashSet<>();
            for (Incompleteness gap : observed.gaps()) {
                by.add(new Weakening.ObservationIncomplete(gap));
            }
            return new Measurement.FailedToMeasure<>(
                    ItemAssessment.Coverage.CouldNotAsk.ARMS_UNREADABLE, WeakeningSet.ofAll(by));
        }
        return whyNoInvariantLine(observed, level);
    }

    /** Why nothing was built, where nothing was: the level not asking for values comes before this
     *  run having nothing to build against, because a build that asked for none never looked for
     *  the classes. */
    private static ItemAssessment.Attempt.Reason whenThereIsNoProbe(
            souther.compiler.query.Adequacy.Level level) {
        return level.buildsValues() ? ItemAssessment.Attempt.Reason.NO_CLASSES
                : ItemAssessment.Attempt.Reason.VALUES_NOT_ASKED_FOR;
    }

    /** What every line of every kind says where the build asked for no measurement: the rules drew
     *  it, and nothing was read against it. Asked before either path below, because neither of them
     *  is about a run that did not happen. */
    private static Measurement<ItemAssessment.Coverage> whyNothingWasAsked(
            souther.compiler.query.Adequacy.Level level) {
        return level.readsRows() ? null
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
            souther.compiler.query.Adequacy.RowReading observed,
            souther.compiler.query.Adequacy.Level level) {
        Measurement<ItemAssessment.Coverage> nobodyAsked = whyNothingWasAsked(level);
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

    /**
     * Whether a row was at a boundary, and whether that could be told at all.
     *
     * <p>Three answers, because a value the observer could not read is not a value that missed. A row
     * writing the very number the rule names, whose observation was cut short by a limit somewhere
     * else in the same input, reads as "no row is at this boundary" — which is a sentence about the
     * model that is not true.
     */
    private enum Met { YES, NO, UNREADABLE, UNDECIDED }

    private Coverages() {}

    /**
     * What a row is known to have done.
     *
     * <p>Read as a {@code switch} so that a counting this does not know about is a compile error
     * here rather than a row silently counted as having done nothing. A row whose counting was never
     * read is known to have done none of it, and that it was left undecided is said where the row is
     * reported.
     */
    private static souther.compiler.coverage.Observation seenBy(RowOutcome row) {
        return switch (row.run().counting()) {
            case Counting.Read read -> read.observation();
            case Counting.Unread _ -> souther.compiler.coverage.Observation.NONE;
        };
    }

}
