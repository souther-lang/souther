package souther.compiler.query;

import souther.compiler.check.Sig;
import souther.compiler.execute.BoundaryValues;
import souther.compiler.observe.ObservedValue;
import souther.compiler.partition.Axis;
import souther.compiler.partition.BehaviorInputs;
import souther.compiler.partition.BorderObligationPoint;
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.partition.Generator;
import souther.compiler.partition.InputClassifications;
import souther.compiler.partition.ObservedInputs;
import souther.compiler.partition.StandingAtAPoint;
import souther.compiler.observe.Classification;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.SequencedMap;
import java.util.Set;

/**
 * What each row a run offers would do about each thing the run was asked to offer a row for.
 *
 * <p>The whole table and not the diagonal. A row is composed for one thing, and what else it turns
 * out to answer is the question this exists to put — so every row is asked about every item, and a
 * row's own item is one entry of its column like any other.
 *
 * <p><b>The items are what was asked for.</b> They come from the plan a run was made with and from
 * the points its searches were put, never from what the rows say they were composed for: a row
 * carries the classes and arms it may be named after and never a line, so an item universe read off
 * the rows would be missing every line in the block.
 *
 * <p>Nothing here is a measurement. Each entry says what would follow if the row were written, and
 * the rows are questions nobody has answered yet.
 */
public record Settlements(List<OfferItem> requested,
                          SequencedMap<OfferItem, RowKey> composedFor,
                          SequencedMap<RowKey, Map<OfferItem, Settlement>> byRow) {

    public Settlements {
        requested = List.copyOf(requested);
        composedFor = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(composedFor));
        byRow = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(byRow));
    }

    /** What {@code row} would do about {@code item}, for a reader holding both. */
    public Settlement at(RowKey row, OfferItem item) {
        Map<OfferItem, Settlement> here = byRow.get(row);
        if (here == null || !here.containsKey(item)) {
            throw new IllegalArgumentException("no entry for " + row + " at " + item);
        }
        return here.get(item);
    }

    /**
     * What a set of rows puts in front of a person for one item.
     *
     * <p>Two ways, and a reduction has to keep both. A row that settles the item answers it whoever
     * it was composed for; and the row composed <em>for</em> the item is what a person was offered
     * for it, whether or not this walk can tell that it settles it — a row whose reading came back
     * undetermined is still the one piece of work anybody was handed there.
     *
     * <p>Written once because it is what {@link #keeping()} preserves. Said as two rules in two
     * places, the second is the one a later reader drops as an oversight.
     */
    public boolean offers(Set<RowKey> rows, OfferItem item) {
        for (RowKey row : rows) {
            if (byRow.get(row).get(item).settles()) {
                return true;
            }
        }
        return rows.contains(composedFor.get(item));
    }

    /**
     * The rows to keep: every one whose going would cost the offering something.
     *
     * <p>What is preserved is {@link #offers}, for every item. So the result holds, of the rows
     * {@code R*} it comes back with and the rows {@code R} it was given:
     *
     * <ol>
     *   <li>every item {@code R} offers something for, {@code R*} offers something for;</li>
     *   <li>no row of {@code R*} can go and leave that true.</li>
     * </ol>
     *
     * <p><b>Which is not "every row left settles something nothing else does".</b> A row kept by the
     * second half of {@code offers} settles nothing this could tell about — it is there because it
     * is the only thing composed for its item — and a reduction written to the shorter sentence
     * would drop it and take that item's only offer with it.
     *
     * <p>Nor is it the smallest set: a different, smaller set of rows may offer for the same items.
     * Irredundant is what this is, and finding a minimum is a different question.
     *
     * <p>Only {@link Settlement.Settles} counts as settling. A row that cannot be told about is not
     * a row that answers, and counting it would drop the row that did.
     *
     * <p>Walked from the back, so a row that came first stays. Which of two rows answering the same
     * things a person is handed is arbitrary, and taking the earlier one keeps the block steady:
     * the order rows are composed in is the order the searches were asked, and an edit somewhere
     * later in the model does not move what is offered above it.
     */
    public Set<RowKey> keeping() {
        Map<OfferItem, Integer> count = new LinkedHashMap<>();
        for (OfferItem item : requested) {
            int settling = 0;
            for (Map<OfferItem, Settlement> here : byRow.values()) {
                if (here.get(item).settles()) {
                    settling++;
                }
            }
            count.put(item, settling);
        }
        // What each row was composed for, the way round this asks it. Read out of the map the other
        // way for every row, the walk would go over every item once per row to find the few that
        // name it.
        Map<RowKey, List<OfferItem>> composedHere = new LinkedHashMap<>();
        composedFor.forEach((item, row) ->
                composedHere.computeIfAbsent(row, _ -> new ArrayList<>()).add(item));
        List<RowKey> inOrder = new ArrayList<>(byRow.keySet());
        Set<RowKey> kept = new LinkedHashSet<>(inOrder);
        for (int at = inOrder.size() - 1; at >= 0; at--) {
            RowKey row = inOrder.get(at);
            if (goes(row, composedHere.getOrDefault(row, List.of()), count)) {
                kept.remove(row);
                byRow.get(row).forEach((item, settlement) -> {
                    if (settlement.settles()) {
                        count.merge(item, -1, Integer::sum);
                    }
                });
            }
        }
        return Collections.unmodifiableSet(new LinkedHashSet<>(
                inOrder.stream().filter(kept::contains).toList()));
    }

    /**
     * Whether the offering offers as much without {@code row} as with it — {@link #offers} for
     * every item, read off the counts rather than walked again.
     *
     * <p>The counts hold the kept rows and this one among them. So an item this row settles needs a
     * second settler to be left after it goes, and an item it was composed for and settles nothing
     * of needs one at all: without a settler, taking the row away takes the item's only offer.
     *
     * @param composedHere what this row was composed for
     */
    private boolean goes(RowKey row, List<OfferItem> composedHere, Map<OfferItem, Integer> count) {
        Map<OfferItem, Settlement> here = byRow.get(row);
        for (Map.Entry<OfferItem, Settlement> each : here.entrySet()) {
            if (each.getValue().settles() && count.get(each.getKey()) <= 1) {
                return false;
            }
        }
        // And what was composed for it. An item whose own row settles nothing this could tell about
        // is one nobody would be offered a row for at all, which is a piece of work going missing
        // rather than a row being said once instead of twice.
        for (OfferItem item : composedHere) {
            if (!here.get(item).settles() && count.get(item) < 1) {
                return false;
            }
        }
        return true;
    }

    /** The items some row of this offering settles, which is what a reduction has to keep answered. */
    public Set<OfferItem> settled() {
        Set<OfferItem> out = new LinkedHashSet<>();
        for (OfferItem item : requested) {
            for (Map<OfferItem, Settlement> here : byRow.values()) {
                if (here.get(item).settles()) {
                    out.add(item);
                    break;
                }
            }
        }
        return Collections.unmodifiableSet(out);
    }

    /**
     * The table for one offering.
     *
     * <p>Read with the same walk a written row is read with. Where a candidate's values sit is
     * {@link InputClassifications}'s answer, whether it stands at a line is
     * {@link StandingAtAPoint}'s, and which arms it takes is what running it recorded — the three
     * questions a measurement puts to the rows in a file, put here to the rows a person is being
     * handed.
     */
    public static Settlements of(Db db, Offering offering) {
        String module = offering.request().module();
        Map<String, Sig> sigs = db.ask(new Bodies.Signatures(module)).value();
        BoundaryValues building = Adequacy.constructing(db, module);
        souther.compiler.execute.RowTrials trials = Adequacy.trialling(db, module);
        List<OfferItem> requested = new ArrayList<>();
        SequencedMap<OfferItem, RowKey> composedFor = new LinkedHashMap<>();
        SequencedMap<RowKey, Map<OfferItem, Settlement>> byRow = new LinkedHashMap<>();
        // How each behavior reads the lines the module's declarations own. A behavior's own account
        // holds the lines it is owed a row at and none of these — that is what the account is for —
        // so a walk that looked only there would find no reading of a declared line anywhere and
        // answer that no row stands at one, of rows composed to stand at exactly that.
        Map<BorderObligationPoint, Map<String, List<BorderAssessment>>> declaredReadings =
                readingsOfTheDeclaredLines(db, module, offering.request().boundaries());
        Map<String, OneBehavior> reading = new LinkedHashMap<>();
        for (Map.Entry<String, Adequacy.Filling> behavior : offering.searched().entrySet()) {
            OneBehavior read = OneBehavior.of(db, module, behavior.getKey(), behavior.getValue(),
                    sigs == null ? null : sigs.get(behavior.getKey()), building, trials,
                    offering.request().boundaries(), declaredReadings);
            reading.put(behavior.getKey(), read);
            requested.addAll(read.owed());
            composedFor.putAll(read.composed(behavior.getValue()));
        }
        // And the points the module's declarations are owed, which are no behavior's own. A row of
        // whichever behavior composed one answers the line for everybody, so they are items of the
        // offering rather than of the block a row happens to sit in.
        if (offering.declared() != null) {
            offering.declared().resolved().forEach((point, answer) -> {
                OfferItem item = new OfferItem.APointOfALine(point);
                switch (answer.resolution()) {
                    case DeclarationResolution.Generated(var by, var row) -> {
                        requested.add(item);
                        composedFor.put(item, RowKey.of(by, row));
                    }
                    // Asked for and nothing came of it, which is still a thing this run is short of
                    // — and something else may stand there, which is what makes it worth asking.
                    case DeclarationResolution.Unresolved _ -> requested.add(item);
                    // Not asked for at all: a row already stands there, or nothing measured it. A
                    // point in nobody's way is not work this run offers, and holding it here would
                    // let a candidate be the only offer for it.
                    case DeclarationResolution.NoSearch _ -> { }
                }
            });
        }
        List<OfferItem> items = List.copyOf(new LinkedHashSet<>(requested));
        offering.rows().forEach((behavior, rows) -> {
            OneBehavior read = reading.get(behavior);
            for (Offering.OfferedRow row : rows) {
                // Read once for the row and asked of every item. What a row is — where its values
                // sit and what running it recorded — does not change between the questions put to
                // it, and reading it per item would be the same row read as many times as this run
                // happens to be asked about, at the price of running it that many times.
                OneRow one = read == null ? OneRow.nothingRead() : read.read(row.inputs());
                Map<OfferItem, Settlement> here = new LinkedHashMap<>();
                for (OfferItem item : items) {
                    here.put(item, read == null ? one.undetermined() : read.settlementOf(one, item));
                }
                byRow.put(row.key(), Collections.unmodifiableMap(here));
            }
        });
        return new Settlements(items, composedFor, byRow);
    }

    /**
     * Which behaviors read each line a declaration owns, and what each of their readings is.
     *
     * <p>Asked of the debts and not of any behavior. A line a declaration draws is read wherever the
     * type is carried, and where a row written in one behavior's terms stands is a question about
     * that behavior's reading of it — so the readings are what a row is put to, one per position
     * that meets the line.
     */
    private static Map<BorderObligationPoint, Map<String, List<BorderAssessment>>>
            readingsOfTheDeclaredLines(Db db, String module, boolean boundaries) {
        Map<BorderObligationPoint, Map<String, List<BorderAssessment>>> out = new LinkedHashMap<>();
        if (!boundaries) {
            return out;
        }
        Adequacy.DeclaredBoundaries account = db.ask(new Adequacy.DeclaredBorders(module)).value();
        if (account == null) {
            return out;
        }
        for (Adequacy.DeclaredDebt owed : account.owed()) {
            Map<String, List<BorderAssessment>> here =
                    out.computeIfAbsent(owed.debt().point(), _ -> new LinkedHashMap<>());
            owed.debt().met().forEach((reading, at) ->
                    here.computeIfAbsent(reading.behavior(), _ -> new ArrayList<>()).add(at));
        }
        return out;
    }

    /**
     * One behavior's own reading of a candidate: what it is asked for, and how a row of it is read.
     *
     * <p>Made once per behavior and not once per row. What a row is read against — where its
     * positions are, what the model divides them into, and which lines this behavior's readings meet
     * — is the behavior's and does not move between the rows of one block.
     */
    private record OneBehavior(String behavior, BehaviorInputs where, List<Axis> axes, Sig sig,
                               BoundaryValues building, Generator.Trial trial,
                               List<Generator.ClassOwed> classes, List<Generator.ArmOwed> arms,
                               Map<OfferItem.APointOfALine, OwedBoundaryPoint> owedHere,
                               Map<OfferItem.APointOfALine, List<AtAPoint>> reads) {

        static OneBehavior of(Db db, String module, String behavior, Adequacy.Filling filling,
                              Sig sig, BoundaryValues building,
                              souther.compiler.execute.RowTrials trials, boolean boundaries,
                              Map<BorderObligationPoint, Map<String, List<BorderAssessment>>>
                                      declared) {
            Generator.Subject subject = filling.composed().plan().subject();
            Map<OfferItem.APointOfALine, OwedBoundaryPoint> owedHere = new LinkedHashMap<>();
            Map<OfferItem.APointOfALine, List<AtAPoint>> reads = new LinkedHashMap<>();
            if (boundaries) {
                List<BorderAssessment> edges =
                        db.ask(new Adequacy.BoundarySearch(module, behavior)).value();
                if (edges != null) {
                    // What this run was asked for a row at. Neither of the readings beside it will
                    // do: the places a row is composed at drop what tells two obligations at one
                    // point apart, and the account holds points the measurement has already
                    // settled — a point a written row stands at is owed and is nobody's work, and
                    // counted here a candidate standing there would be its only offer and could
                    // never be dropped.
                    for (OwedBoundaryPoint point
                            : OwedBoundaryPoint.askedForARow(OwedBoundaryPoint.across(edges)).at()) {
                        OfferItem.APointOfALine item =
                                new OfferItem.APointOfALine(point.owed());
                        owedHere.put(item, point);
                        reads.computeIfAbsent(item, _ -> new ArrayList<>())
                                .add(new AtAPoint(point.line(), point.item().criterion()));
                    }
                }
            }
            // And this behavior's readings of the lines the declarations own, which its own account
            // holds none of.
            declared.forEach((point, byBehavior) -> {
                for (BorderAssessment at : byBehavior.getOrDefault(behavior, List.of())) {
                    if (at.at(point.role()) instanceof ItemAssessment.Owed owed) {
                        reads.computeIfAbsent(new OfferItem.APointOfALine(point),
                                _ -> new ArrayList<>())
                                .add(new AtAPoint(at.border(), owed.criterion()));
                    }
                }
            });
            return new OneBehavior(behavior, subject.inputs(), subject.axes(), sig, building,
                    sig == null || trials == null ? Generator.Trial.NOTHING_RUNS
                            : Adequacy.runningRowsOf(trials, behavior, sig),
                    filling.composed().plan().classesOwed(), filling.composed().plan().armsOwed(),
                    owedHere, reads);
        }

        /**
         * Which row was composed for each of them, where one was.
         *
         * <p>Read off what the searches answered with and never off the rows. A row carries the
         * classes and arms it may be named after and never a line, so a walk from the rows would
         * have every line in the block composed for nothing.
         */
        Map<OfferItem, RowKey> composed(Adequacy.Filling filling) {
            Map<OfferItem, RowKey> out = new LinkedHashMap<>();
            for (Generator.ClassOwed each : classes) {
                if (filling.composed().discharge().at(each)
                        instanceof souther.compiler.partition.ClassDisposition.Built built) {
                    out.put(new OfferItem.AClass(each),
                            RowKey.of(behavior, filling.composed().rowFor(built.row())));
                }
            }
            for (Generator.ArmOwed each : arms) {
                if (filling.composed().discharge().at(each)
                        instanceof souther.compiler.partition.ArmDisposition.Built built) {
                    out.put(new OfferItem.AnArm(each),
                            RowKey.of(behavior, filling.composed().rowFor(built.row())));
                }
            }
            owedHere.forEach((item, point) -> {
                if (point.item().attempt() instanceof ItemAssessment.Attempt.Built built) {
                    out.put(item, RowKey.of(behavior, built.row()));
                }
            });
            return out;
        }

        /** What this behavior was asked to offer a row for. */
        List<OfferItem> owed() {
            List<OfferItem> out = new ArrayList<>();
            classes.forEach(each -> out.add(new OfferItem.AClass(each)));
            arms.forEach(each -> out.add(new OfferItem.AnArm(each)));
            out.addAll(owedHere.keySet());
            return out;
        }

        /**
         * The row as the two things every question here is put to.
         *
         * <p>Made once. The values are built through this module's own decoders and the account is
         * what running it recorded — and a row read again for the next item would be run again for
         * it, which is the same row asked to do the same thing as many times as this run has
         * questions.
         */
        OneRow read(List<FixtureTemplate> inputs) {
            Generator.Watched watched = trial.run(inputs);
            if (building == null || sig == null) {
                return new OneRow(null, Settlement.Reason.NOTHING_BUILT_THE_VALUES, watched);
            }
            List<ObservedValue> values = new ArrayList<>();
            for (int at = 0; at < inputs.size(); at++) {
                if (at >= sig.ins().size()) {
                    return new OneRow(null, Settlement.Reason.NOTHING_BUILT_THE_VALUES, watched);
                }
                switch (building.build(sig.ins().get(at), inputs.get(at).value())) {
                    case BoundaryValues.Built.Value(var observed) -> values.add(observed);
                    // The model would not take the value the row names. Told apart from having
                    // nothing to build against: this found something out about the row, and that
                    // found nothing out at all.
                    case BoundaryValues.Built.Refused _ -> {
                        return new OneRow(null, Settlement.Reason.THE_VALUES_WERE_REFUSED, watched);
                    }
                }
            }
            return new OneRow(List.copyOf(values), null, watched);
        }

        Settlement settlementOf(OneRow row, OfferItem item) {
            return switch (item) {
                case OfferItem.AClass(var owed) -> inClass(row, owed);
                case OfferItem.AnArm(var owed) -> throughArm(row, owed);
                case OfferItem.APointOfALine at -> atThePoint(row, at);
            };
        }

        /**
         * Whether the row's value at the position falls in the class.
         *
         * <p>Of this behavior's positions only. An axis names the behavior it divides, so a class of
         * another one is not something a row written here has a value at — which is a row that does
         * not settle it rather than one nothing could tell about.
         */
        private Settlement inClass(OneRow row, Generator.ClassOwed owed) {
            if (!behavior.equals(owed.at().behavior())) {
                return new Settlement.DoesNotSettle();
            }
            if (row.values() == null) {
                return row.undetermined();
            }
            Classification at =
                    InputClassifications.of(row.values(), where, axes).get(owed.at());
            if (at == null) {
                return new Settlement.DoesNotSettle();
            }
            return switch (at) {
                case Classification.Classified in -> in.classIds().contains(owed.classId())
                        ? new Settlement.Settles() : new Settlement.DoesNotSettle();
                case Classification.Unclassified _ -> new Settlement.Undetermined(
                        Settlement.Reason.THE_VALUES_COULD_NOT_BE_READ);
            };
        }

        /**
         * Whether running the row goes through the arm.
         *
         * <p>Not something the values answer. A row whose values sit in the classes a way into an
         * arm leaves may still go elsewhere, so the account of the run is the whole of the evidence
         * — and where there is none, this says so rather than reading the absence as a row that
         * missed.
         */
        private Settlement throughArm(OneRow row, Generator.ArmOwed owed) {
            return switch (row.watched()) {
                case Generator.Watched.Ran(var account) -> account.taken().contains(owed.probe())
                        ? new Settlement.Settles() : new Settlement.DoesNotSettle();
                case Generator.Watched.NoAccount _ ->
                        new Settlement.Undetermined(Settlement.Reason.NO_ACCOUNT_OF_THE_RUN);
            };
        }

        /**
         * Whether the row stands at the point, as this behavior reads the line.
         *
         * <p>A line is owed a row once and is met at whichever position reads it, so a point this
         * behavior's readings do not meet is one a row written here does not settle. Where they do,
         * the walk that reads a written row against the point reads this one.
         */
        private Settlement atThePoint(OneRow read, OfferItem.APointOfALine at) {
            List<AtAPoint> here = reads.get(at);
            if (here == null || here.isEmpty()) {
                // No reading of this line in this behavior. A row written here has no value on the
                // line at all, which is a row that does not settle the point rather than one
                // nothing could tell about.
                return new Settlement.DoesNotSettle();
            }
            if (read.values() == null) {
                return read.undetermined();
            }
            ObservedInputs row = new ObservedInputs(read.values(), read.watched());
            // Existential over the readings, the way a point met at one position of a behavior is
            // met: a row standing on the line anywhere the behavior reads it is a row at the point.
            Settlement answer = new Settlement.DoesNotSettle();
            for (AtAPoint one : here) {
                Settlement said = switch (StandingAtAPoint.met(one.line().cut().of(), where,
                        List.of(row), one.criterion(), one.line().origin().comparisonAt())) {
                    case YES -> new Settlement.Settles();
                    case NO -> new Settlement.DoesNotSettle();
                    case NOT_WATCHED ->
                            new Settlement.Undetermined(Settlement.Reason.NO_ACCOUNT_OF_THE_RUN);
                    case UNREADABLE -> new Settlement.Undetermined(
                            Settlement.Reason.THE_VALUES_COULD_NOT_BE_READ);
                };
                if (said.settles()) {
                    return said;
                }
                if (said instanceof Settlement.Undetermined) {
                    answer = said;
                }
            }
            return answer;
        }

    }

    /** One position's reading of one line, as a row is put to it: the border this behavior met and
     *  what a row there has to do. */
    private record AtAPoint(souther.compiler.partition.Border line,
                            souther.compiler.partition.Criterion criterion) {}

    /**
     * One row of the offering, read.
     *
     * @param values      what its inputs build to, or null where they do not all build
     * @param whyNotBuilt why they did not, where they did not, and null where they did
     * @param watched     what running it recorded, which a row whose values would not build still
     *                    has: the two are found out separately and one failing is not the other
     *                    failing
     */

    private record OneRow(List<ObservedValue> values, Settlement.Reason whyNotBuilt,
                          Generator.Watched watched) {

        static OneRow nothingRead() {
            return new OneRow(null, Settlement.Reason.NOTHING_BUILT_THE_VALUES,
                    new Generator.Watched.NoAccount());
        }

        /** What an item that needs the values is told, where they are not here. */
        Settlement undetermined() {
            return new Settlement.Undetermined(whyNotBuilt);
        }
    }
}
