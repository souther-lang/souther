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
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.observe.Counting;
import souther.compiler.observe.RowOutcome;
import souther.compiler.partition.Axis;
import souther.compiler.partition.AxisId;
import souther.compiler.partition.Border;
import souther.compiler.partition.Criterion;
import souther.compiler.partition.Demand;
import souther.compiler.partition.Generator;
import souther.compiler.partition.PointRole;
import souther.compiler.partition.BorderQuantity;
import souther.compiler.partition.LevelRealizer;
import souther.compiler.partition.Realization;
import souther.compiler.partition.Standing;
import souther.compiler.inputs.InputDomain;
import souther.compiler.partition.EnsuresThresholds;
import souther.compiler.partition.GuardThresholds;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.partition.BoundaryLine;
import souther.compiler.partition.PartitionClass;
import souther.compiler.partition.Partitions;
import souther.compiler.partition.BehaviorInputs;
import souther.compiler.partition.RowClasses;

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
     * The positions one behavior is measured at, with what its own comparisons divide them into.
     *
     * <p>Asked here rather than worked out again wherever it is needed. What a report says is not
     * covered and what a generator writes a row for have to be the same positions and the same classes,
     * and two derivations of them would be two chances to disagree.
     */
    static Partitions.Partitioning partitioningOf(Hir.SpecBehavior behavior, InputDomain inputs,
                                                  Sig sig, Symbols symbols, ReadingPolicy policy,
                                                  Core body, CoverageSites.Plan plan,
                                                  PathReachability.Answers arrives,
                                                  souther.compiler.check.StatedContract stated) {
        List<String> parameters = behavior.params().stream().map(Hir.Param::name).toList();
        // What a row's values are, where they sit and what they are written as, read together:
        // a field under a name is reached by taking the name off, and a walk given the paths
        // alone reaches nothing where the derivation reaches a field.
        BehaviorInputs where = new BehaviorInputs(parameters, sig.inputTypes(), symbols, policy);
        // Read once for the three below. What it holds is a way of asking the declarations reaching
        // this input a further question, and each of them asking for its own would read every rule
        // of every parameter three times over to arrive at the same answers.
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
                        symbols);
        // Both producers of one kind of line, put together before the position is divided. Two
        // rules at one value are one cut and stay separate obligations, which is what the merge
        // below does — applied one producer at a time, a clause and a guard naming one number would
        // divide the position twice.
        return Partitions.withThresholds(partitioning,
                both(clauses.thresholds(), guards.thresholds()), symbols, policy,
                both(clauses.unread(), guards.unread()),
                both(clauses.singled(), guards.singled()),
                both(clauses.between(), guards.between()), arrives,
                // What each comparison raised and what the reading of it answered, from both
                // producers. Carried rather than derived from the lines that came back: a
                // comparison this could not read draws no line, and that is when its questions
                // stand.
                both(clauses.accounting(), guards.accounting()));
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
     * @param boundaries what was established about every line this behavior's rules drew, made once
     *                   by {@link souther.compiler.query.Adequacy.Boundaries} and read here. Measuring
     *                   a line takes putting a value through the module's decoders, which is not
     *                   something a coverage count can do on its own and not something that should
     *                   happen twice.
     */
    static PartitionEvidence of(Hir.SpecBehavior behavior, InputDomain inputs, Sig sig,
                                Symbols symbols, ReadingPolicy policy, Core body,
                                CoverageSites.Plan plan, souther.compiler.query.Adequacy.Observed observed,
                                List<BorderAssessment> boundaries,
                                PathReachability.Answers arrives,
                                souther.compiler.check.StatedContract stated) {
        List<RowOutcome> rows = observed.rows();
        List<String> parameters = behavior.params().stream().map(Hir.Param::name).toList();
        // What a row's values are, where they sit and what they are written as, read together:
        // a field under a name is reached by taking the name off, and a walk given the paths
        // alone reaches nothing where the derivation reaches a field.
        BehaviorInputs where = new BehaviorInputs(parameters, sig.inputTypes(), symbols, policy);
        Partitions.Partitioning partitioning =
                partitioningOf(behavior, inputs, sig, symbols, policy, body, plan, arrives, stated);

        List<PartitionEvidence.AxisCoverage> axes = new ArrayList<>();

        List<Axis> divided = new ArrayList<>();
        List<PartitionEvidence.Unanswered> standing = new ArrayList<>();
        Readings readings = Readings.of(rows, where, partitioning.axes(),
                observed.someRowsUnseen());
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
                axes.add(coverageOf(axis, readings));
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
        return new PartitionEvidence(PartitionEvidence.Partitioned.of(axes),
                PartitionEvidence.Bounded.of(boundaries), pairsOf(divided, readings),
                partitioning.undivided(), partitioning.unread(), partitioning.blocked(),
                partitioning.notSeparated(), List.copyOf(standing),
                partitioning.omitted(),
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
                if (where.get(axis) instanceof Classification.Unclassified could) {
                    byKind.putIfAbsent(could.reason().identity(), could.reason());
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
     * @param someRowsUnseen rows that were never observed at all, which no reading can show
     */
    private record Readings(List<Map<AxisId, Classification>> byRow, boolean someRowsUnseen) {

        static Readings of(List<RowOutcome> rows, BehaviorInputs where, List<Axis> axes,
                           boolean someRowsUnseen) {
            List<Map<AxisId, Classification>> read = new ArrayList<>();
            for (RowOutcome row : rows) {
                read.add(RowClasses.of(row, where, axes));
            }
            return new Readings(List.copyOf(read), someRowsUnseen);
        }

        boolean noRows() {
            return byRow.isEmpty();
        }

        /** Which class a row fell in at one position, or null where it did not say. */
        static String classIn(Map<AxisId, Classification> where, Axis axis) {
            return where.get(axis.id()) instanceof Classification.Classified in ? in.classId() : null;
        }

        /** How many rows could not say where they were at this position. */
        int couldNotSay(Axis axis) {
            return (int) byRow.stream().filter(where -> classIn(where, axis) == null).count();
        }

        /**
         * Whether every row that bears on {@code axes} said where it was at all of them.
         *
         * <p>Only then does a class or a combination nothing sits in mean nothing reaches it. One row
         * that could not be placed at one of the positions leaves every class of that position, and
         * every combination it takes part in, undecided rather than untried.
         */
        MeasurementStatus status(List<Axis> axes) {
            if (someRowsUnseen) {
                return MeasurementStatus.PARTIAL;
            }
            for (Axis axis : axes) {
                if (couldNotSay(axis) > 0) {
                    return MeasurementStatus.PARTIAL;
                }
            }
            return MeasurementStatus.COMPLETE;
        }
    }

    /** How many pairs of classes across two positions the rows are enough to sit in at once. */
    private static final int PAIR_LIMIT = 20_000;

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
    private static PartitionEvidence.PairSpace pairsOf(List<Axis> axes, Readings readings) {
        // The product of what a row can be written at, not of what the types declare. A case the
        // rules refuse is not a class of its position at all, so the slice of the product it would
        // have taken part in is not here to be counted — which is a different thing from a pair
        // whose two classes each have rows but never together.
        long total = 0;
        for (int i = 0; i < axes.size(); i++) {
            for (int j = i + 1; j < axes.size(); j++) {
                total += (long) axes.get(i).classes().size() * axes.get(j).classes().size();
            }
        }
        if (total == 0) {
            return PartitionEvidence.PairSpace.NONE;
        }
        // Before the size of the space is worth mentioning. A combination nothing tried to sit in is
        // not a combination left untried by anybody, and how many of them there are says nothing
        // about a behavior no row names.
        if (readings.noRows() && !readings.someRowsUnseen()) {
            return PartitionEvidence.PairSpace.unavailable((int) Math.min(total, Integer.MAX_VALUE),
                    PartitionEvidence.PairSpace.Reason.NO_ROWS);
        }
        if (total > PAIR_LIMIT) {
            return new PartitionEvidence.PairSpace((int) Math.min(total, Integer.MAX_VALUE), 0, 0, 0,
                    (int) Math.min(total, Integer.MAX_VALUE), true, MeasurementStatus.PARTIAL, null);
        }
        Set<String> covered = new LinkedHashSet<>();
        for (Map<AxisId, Classification> where : readings.byRow()) {
            for (int i = 0; i < axes.size(); i++) {
                for (int j = i + 1; j < axes.size(); j++) {
                    String left = Readings.classIn(where, axes.get(i));
                    String right = Readings.classIn(where, axes.get(j));
                    if (left != null && right != null) {
                        // Which positions, and not only which classes. A class id is unique within
                        // its axis and not across axes — three `Flag` inputs all have a `Yes` — so a
                        // key of two class names alone collapses every pair one row covers into one.
                        covered.add(i + "/" + left + " " + j + "/" + right);
                    }
                }
            }
        }
        int reached = covered.size();
        return new PartitionEvidence.PairSpace((int) total, reached, reached, 0,
                (int) total - reached, false, readings.status(axes), null);
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

    private static PartitionEvidence.AxisCoverage coverageOf(Axis axis, Readings readings) {
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
        if (readings.noRows() && !readings.someRowsUnseen()) {
            return PartitionEvidence.AxisCoverage.unavailable(axis.id().toString(),
                    axis.term().toString(), classes,
                    PartitionEvidence.AxisCoverage.Reason.NO_ROWS, read);
        }
        Set<String> covered = new LinkedHashSet<>();
        for (Map<AxisId, Classification> where : readings.byRow()) {
            String in = Readings.classIn(where, axis);
            if (in != null) {
                covered.add(in);
            }
        }
        return new PartitionEvidence.AxisCoverage(axis.id().toString(), axis.term().toString(),
                classes, covered, readings.couldNotSay(axis), readings.status(List.of(axis)), null,
                read);
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
                String label, souther.compiler.check.Carrier carrier,
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
     */
    static List<BorderAssessment> assess(
            Axis axis, BehaviorInputs where, souther.compiler.query.Adequacy.Observed observed,
            boolean armsAsked, boolean knownWritable, Probe probe,
            souther.compiler.inputs.Quantities rules,
            souther.compiler.numeric.NumericDomain.Bounds within) {
        // Keyed by the line rather than by the reading of it. A guard inside a non-recursive helper
        // is read once per call of that helper, and the rows do not owe the same border twice for
        // having been offered it twice; what each reading saw is merged below.
        java.util.SequencedMap<BoundaryLine, BorderAssessment> out = new java.util.LinkedHashMap<>();
        LevelRealizer realizer = new LevelRealizer();
        for (Border each : Partitions.bordersOf(axis, where.symbols(), within)) {
            out.merge(BoundaryLine.of(each),
                    assessed(each, shapeOf(each, where, knownWritable, probe, realizer,
                                    rules.region()),
                            observed, armsAsked),
                    Coverages::whicheverSawMore);
        }
        return List.copyOf(out.values());
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
                                             souther.compiler.query.Adequacy.Observed observed,
                                             boolean armsAsked) {
        // Whether meeting this border takes the comparison having run, asked of the rule rather than
        // read off which kind it is, and asked once for the border rather than once per point. A
        // guard's line is about a place in a body and is reached or not; an invariant's and a
        // clause's are about the values — one refuses everything outside its bound, the other states
        // a relation — so for both of those writing the value is the whole of what there is to reach.
        boolean guard = border.origin().comparisonAt().isPresent();
        ItemAssessment.Coverage.Reason absent = guard
                ? whyNoGuardLine(observed.rows(), armsAsked, observed.armsUnseen(),
                        observed.someRowsUnseen())
                : whyNoInvariantLine(observed.rows(), observed.someRowsUnseen());

        java.util.EnumMap<PointRole, ItemAssessment> items = new java.util.EnumMap<>(PointRole.class);
        for (PointRole role : PointRole.values()) {
            items.put(role, switch (border.demand(role)) {
                case Demand.NotOwed not -> new ItemAssessment.NotOwed(not.reason());
                case Demand.Owed owed -> {
                    ItemAssessment.Coverage coverage = absent != null
                            ? new ItemAssessment.Coverage.NotMeasured(absent)
                            : verdictOf(shape.met(owed.criterion(), observed.rows()), guard,
                                    observed);
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
                                            LevelRealizer realizer,
                                            souther.compiler.inputs.SearchRegion within) {
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
                if (probe == null) {
                    return new ItemAssessment.Attempt.NotAttempted(
                            ItemAssessment.Attempt.Reason.NO_CLASSES);
                }
                // Where a row would have to stand is asked of the quantity, and finding one there of
                // the realizer. What it composes is a candidate and no part of the item: another row
                // in the same side is at the point as much as this one would be, so what the row is
                // offered for goes in beside it rather than being read back off it.
                return switch (realizer.realize(quantity.standingAt(criterion), within)) {
                    case Realization.Found found ->
                            whatCameOfIt(probe.attempt(label, quantity.carrier(), found.fixing()));
                    // And the two ways of finding nothing are not one answer. A walk of the whole
                    // of what the rules leave that reaches no value settles the point; a search
                    // that stopped, or one that composed no candidate at all, settles nothing
                    // (ADR-0091).
                    case Realization.Impossible _ -> new ItemAssessment.Attempt.Unresolved(
                            new souther.compiler.partition.Generator.UnresolvedCombination(
                                    java.util.List.of(label),
                                    souther.compiler.partition.Generator.UnresolvedCombination
                                            .Reason.THE_RULES_LEAVE_NOTHING_THERE));
                    case Realization.Unknown unknown -> switch (unknown.why()) {
                        case NOTHING_COMPOSED_ONE -> nothingComposedOne(label);
                        case THE_SEARCH_RAN_OUT -> new ItemAssessment.Attempt.Unresolved(
                                new souther.compiler.partition.Generator.UnresolvedCombination(
                                        java.util.List.of(label),
                                        souther.compiler.partition.Generator.UnresolvedCombination
                                                .Reason.SEARCH_LIMIT));
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
            switch (quantity.standsAt(criterion, path -> where.valueAt(row, path))) {
                case UNREADABLE -> unreadable = true;
                case NO -> { }
                case YES -> {
                    if (site.stream().allMatch(seenBy(row)::reached)) {
                        return Met.YES;
                    }
                }
            }
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
            case ItemAssessment.Coverage.Hit _ -> 3;
            case ItemAssessment.Coverage.Undecided _ -> 2;
            case ItemAssessment.Coverage.Missed _ -> 1;
            case ItemAssessment.Coverage.NotMeasured _ -> 0;
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
            ItemAssessment.Coverage coverage,
            java.util.function.Supplier<ItemAssessment.Attempt> search) {
        if (coverage instanceof ItemAssessment.Coverage.Hit) {
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
    private static ItemAssessment.Attempt nothingComposedOne(String subject) {
        return new ItemAssessment.Attempt.Unresolved(
                new souther.compiler.partition.Generator.UnresolvedCombination(List.of(subject),
                        souther.compiler.partition.Generator.UnresolvedCombination.Reason
                                .NOTHING_COMPOSES_ONE));
    }

    /** What a search of the module's own decoders came to, in this measure's words. */
    private static ItemAssessment.Attempt whatCameOfIt(
            souther.compiler.partition.Generator.BoundaryAttempt made) {
        return switch (made) {
            case null -> new ItemAssessment.Attempt.NotAttempted(
                    ItemAssessment.Attempt.Reason.LINKAGE_FAILED);
            case souther.compiler.partition.Generator.BoundaryAttempt.Built built ->
                    new ItemAssessment.Attempt.Built(built.row());
            case souther.compiler.partition.Generator.BoundaryAttempt.Unresolved left ->
                    new ItemAssessment.Attempt.Unresolved(left.why());
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
            Partitions.Partitioning partitioning, BehaviorInputs where,
            souther.compiler.query.Adequacy.Observed observed, boolean armsAsked, Probe probe) {
        // Keyed by the line the author drew, the way a line at a place is. A guard inside a
        // non-recursive helper is read once per call of that helper, and the rows do not owe the same
        // line twice for having been offered it twice — nor may one reading of it take back what
        // another established.
        java.util.SequencedMap<BoundaryLine, BorderAssessment> out = new LinkedHashMap<>();
        LevelRealizer realizer = new LevelRealizer();
        for (Border each : partitioning.between()) {
            out.merge(BoundaryLine.of(each),
                    assessed(each, shapeOf(each, where, false, probe, realizer,
                                    partitioning.quantities().region()), observed,
                            armsAsked),
                    Coverages::whicheverSawMore);
        }
        return List.copyOf(out.values());
    }

    /** What a reading of the rows comes to, once what could not be read is accounted for. */
    private static ItemAssessment.Coverage verdictOf(
            Met met, boolean guard, souther.compiler.query.Adequacy.Observed observed) {
        List<RowOutcome> rows = observed.rows();
        if (met == Met.YES) {
            return new ItemAssessment.Coverage.Hit();
        }
        if (met == Met.UNREADABLE) {
            return new ItemAssessment.Coverage.Undecided();
        }
        // A row nothing read may be the row that is at this value. Found is still found — one row at
        // the boundary settles it whatever else went unread — but not-found is not settled.
        if (observed.someRowsUnseen()) {
            return new ItemAssessment.Coverage.Undecided();
        }
        // Nor is a hit that could not be looked for: a row that never finished left no hits, and a
        // guard's line is met by going through the comparison.
        if (guard && rows.stream().anyMatch(
                row -> row.disposition() == souther.compiler.observe.Disposition.INCOMPLETE)) {
            return new ItemAssessment.Coverage.Undecided();
        }
        return new ItemAssessment.Coverage.Missed();
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
            ItemAssessment.Coverage coverage, boolean knownWritable,
            ItemAssessment.Attempt attempt) {
        if (coverage instanceof ItemAssessment.Coverage.Hit) {
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
    private static boolean worthBuilding(ItemAssessment.Coverage coverage) {
        return coverage instanceof ItemAssessment.Coverage.Missed
                || (coverage instanceof ItemAssessment.Coverage.NotMeasured absent
                        && absent.reason() == ItemAssessment.Coverage.Reason.NO_ROWS);
    }

    /**
     * The first gate a {@code guard}'s line did not get through.
     *
     * <p>Its own path, because a guard's line and an invariant's are not measured the same way and so
     * cannot fail to be measured for the same reasons. Meeting this one takes the comparison having
     * run, which puts the arms in front of the rows: nothing a row carries decides it until the
     * classes that record where the row went exist and survived.
     */
    private static ItemAssessment.Coverage.Reason whyNoGuardLine(
            List<RowOutcome> rows, boolean armsAsked, boolean armsUnseen, boolean someRowsUnseen) {
        if (!armsAsked) {
            return ItemAssessment.Coverage.Reason.ARMS_NOT_ASKED;
        }
        if (armsUnseen) {
            return ItemAssessment.Coverage.Reason.ARMS_UNREADABLE;
        }
        return whyNoInvariantLine(rows, someRowsUnseen);
    }

    /**
     * The first gate an invariant's line did not get through.
     *
     * <p>Only the one: nothing outside the bound can be constructed, so writing the value is the whole
     * of what there is to reach and no instrumentation is owed. This is why the two origins are asked
     * separately — an invariant's line can never be waiting on the arms, and a measure that could say
     * so would be able to say something that is not true of it.
     */
    private static ItemAssessment.Coverage.Reason whyNoInvariantLine(
            List<RowOutcome> rows, boolean someRowsUnseen) {
        // Nothing read is not the same as nothing written. A source that could not be evaluated may
        // hold the row that is at this line, so the question is undecided rather than unasked, and
        // the reading below settles it that way.
        return rows.isEmpty() && !someRowsUnseen
                ? ItemAssessment.Coverage.Reason.NO_ROWS : null;
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
