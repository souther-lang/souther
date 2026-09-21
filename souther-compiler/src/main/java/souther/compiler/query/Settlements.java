package souther.compiler.query;

import souther.compiler.check.Sig;
import souther.compiler.execute.BoundaryValues;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.Place;
import souther.compiler.partition.BorderObligationPoint;
import souther.compiler.partition.ClassOfAPosition;
import souther.compiler.partition.GenerationObligation;
import souther.compiler.partition.ObligationIdentity;
import souther.compiler.partition.Generator;
import souther.compiler.partition.InputClassifications;
import souther.compiler.partition.MeasuredInput;
import souther.compiler.partition.ObservedInputs;
import souther.compiler.partition.OrderedAffineBoundary;
import souther.compiler.partition.RowToRun;
import souther.compiler.partition.RulesTaken;
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
public record Settlements(List<ObligationIdentity> requested,
                          SequencedMap<ObligationIdentity, RowKey> composedFor,
                          SequencedMap<RowKey, Map<ObligationIdentity, Settlement>> byRow,
                          SequencedMap<RowKey, Map<ObligationIdentity,
                                  InputOfARowForALine>> standsAt,
                          Map<ObligationIdentity, InputOfARowForALine> composedAt) {

    public Settlements {
        requested = List.copyOf(requested);
        composedFor = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(composedFor));
        byRow = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(byRow));
        standsAt = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(standsAt));
        composedAt = Collections.unmodifiableMap(new LinkedHashMap<>(composedAt));
        // A row composed for a line was composed somewhere, and what a person is shown for such a
        // line is that. Held here because the two are separate maps a caller fills: a line with a
        // row and no input is one this would show the measurement's own answer for while the block
        // hands the row over, which is the pair of sentences all of this exists to keep together.
        // Asked of the lines alone — a class is where a value falls and an arm is a place a run
        // went, and neither is somewhere a report sends a reader.
        for (Map.Entry<ObligationIdentity, RowKey> each : composedFor.entrySet()) {
            if (each.getKey() instanceof ObligationIdentity.OfABorder
                    && !composedAt.containsKey(each.getKey())) {
                throw new IllegalArgumentException("a row composed for a line and composed nowhere: "
                        + each.getKey() + " by " + each.getValue());
            }
        }
    }

    /**
     * The input of the row a person is handed for each line, once the reduction has settled which
     * rows those are.
     *
     * <p><b>After {@link #keeping()} and never before it.</b> What is composed for a line and what
     * is offered for it are two answers: a row that tells the two lines apart answers the line
     * whoever it was composed for, so the row composed for it goes when another one already does
     * that ({@link #offers}). A place read off the search is a place from before that was decided,
     * and a report naming it sends a reader to an input the block does not hand them.
     *
     * <p><b>Two rules, and each has its own source for the input.</b> They are the two halves of
     * {@link #offers}: the row composed for the line is what a person was offered for it, and a row
     * that settles the line answers it whoever it was composed for. The first is known from the
     * search — the values it asked for are what the row was built from — and the second from
     * reading that row against the line. Only the second of those is a reading, and a row this
     * compiler could not read back is offered all the same
     * ({@link ItemAssessment.Attempt.Unverified}), so a walk that took its input from the reading
     * alone had nothing to name for exactly the rows the second half of {@code offers} keeps.
     *
     * <p>The row composed for the line first, where the reduction kept it, and otherwise whichever
     * kept row settles it — in the order the rows are offered, which is the order a person reads
     * them in.
     *
     * <p>Empty for a line no kept row is offered for, which is a line the block says nothing offers
     * a row for. What is shown then is what the measurement saw, and that is the measurement's to
     * say.
     */
    public Map<ObligationIdentity, InputOfARowForALine> shownFor(Set<RowKey> kept) {
        Map<ObligationIdentity, InputOfARowForALine> out = new LinkedHashMap<>();
        for (ObligationIdentity item : requested) {
            RowKey composed = composedFor.get(item);
            InputOfARowForALine at = null;
            if (composed != null && kept.contains(composed)) {
                at = composedAt.get(item);
            } else {
                for (RowKey rowKey : byRow.keySet()) {
                    if (kept.contains(rowKey) && byRow.get(rowKey).get(item).settles()) {
                        at = standsAt.getOrDefault(rowKey, Map.of()).get(item);
                        break;
                    }
                }
            }
            if (at != null) {
                out.put(item, at);
            }
        }
        return Collections.unmodifiableMap(out);
    }

    /** What the row {@code rowKey} addresses would do about {@code item}, for a reader holding
     *  both. */
    public Settlement at(RowKey rowKey, ObligationIdentity item) {
        Map<ObligationIdentity, Settlement> here = byRow.get(rowKey);
        if (here == null || !here.containsKey(item)) {
            throw new IllegalArgumentException("no entry for " + rowKey + " at " + item);
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
    public boolean offers(Set<RowKey> rowKeys, ObligationIdentity item) {
        for (RowKey rowKey : rowKeys) {
            if (byRow.get(rowKey).get(item).settles()) {
                return true;
            }
        }
        return rowKeys.contains(composedFor.get(item));
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
        Map<ObligationIdentity, Integer> count = new LinkedHashMap<>();
        for (ObligationIdentity item : requested) {
            int settling = 0;
            for (Map<ObligationIdentity, Settlement> here : byRow.values()) {
                if (here.get(item).settles()) {
                    settling++;
                }
            }
            count.put(item, settling);
        }
        // What each row was composed for, the way round this asks it. Read out of the map the other
        // way for every row, the walk would go over every item once per row to find the few that
        // name it.
        Map<RowKey, List<ObligationIdentity>> composedHere = new LinkedHashMap<>();
        composedFor.forEach((item, rowKey) ->
                composedHere.computeIfAbsent(rowKey, _ -> new ArrayList<>()).add(item));
        List<RowKey> inOrder = new ArrayList<>(byRow.keySet());
        Set<RowKey> kept = new LinkedHashSet<>(inOrder);
        for (int at = inOrder.size() - 1; at >= 0; at--) {
            RowKey rowKey = inOrder.get(at);
            if (goes(rowKey, composedHere.getOrDefault(rowKey, List.of()), count)) {
                kept.remove(rowKey);
                byRow.get(rowKey).forEach((item, settlement) -> {
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
     * Whether the offering offers as much without the row {@code rowKey} addresses as with it —
     * {@link #offers} for every item, read off the counts rather than walked again.
     *
     * <p>The counts hold the kept rows and this one among them. So an item this row settles needs a
     * second settler to be left after it goes, and an item it was composed for and settles nothing
     * of needs one at all: without a settler, taking the row away takes the item's only offer.
     *
     * @param composedHere what this row was composed for
     */
    private boolean goes(RowKey rowKey, List<ObligationIdentity> composedHere,
                         Map<ObligationIdentity, Integer> count) {
        Map<ObligationIdentity, Settlement> here = byRow.get(rowKey);
        for (Map.Entry<ObligationIdentity, Settlement> each : here.entrySet()) {
            if (each.getValue().settles() && count.get(each.getKey()) <= 1) {
                return false;
            }
        }
        // And what was composed for it. An item whose own row settles nothing this could tell about
        // is one nobody would be offered a row for at all, which is a piece of work going missing
        // rather than a row being said once instead of twice.
        for (ObligationIdentity item : composedHere) {
            if (!here.get(item).settles() && count.get(item) < 1) {
                return false;
            }
        }
        return true;
    }

    /** The items some row of this offering settles, which is what a reduction has to keep answered. */
    public Set<ObligationIdentity> settled() {
        Set<ObligationIdentity> out = new LinkedHashSet<>();
        for (ObligationIdentity item : requested) {
            for (Map<ObligationIdentity, Settlement> here : byRow.values()) {
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
    public static Settlements of(Db db, Composition offering) {
        String module = offering.request().module();
        Map<String, Sig> sigs = db.ask(new Bodies.Signatures(module)).value();
        BoundaryValues building = Adequacy.constructing(db, module);
        souther.compiler.execute.RowTrials trials = Adequacy.trialling(db, module);
        List<ObligationIdentity> requested = new ArrayList<>();
        SequencedMap<ObligationIdentity, RowKey> composedFor = new LinkedHashMap<>();
        SequencedMap<RowKey, Map<ObligationIdentity, Settlement>> byRow = new LinkedHashMap<>();
        // And where each row stands on each line it answers, which is what a report names when it
        // sends a reader to an input. Kept beside the settlements and made with them: the row was
        // read once, and a place worked out again afterwards is a second reading of it.
        SequencedMap<RowKey, Map<ObligationIdentity, InputOfARowForALine>> standsAt =
                new LinkedHashMap<>();
        // And the input each search composed at, for the lines it composed a row for. The other
        // half of what a person may be shown: a row the reading above could not read back is one
        // this offers all the same, and what it was composed at is what there is to name for it.
        Map<ObligationIdentity, InputOfARowForALine> composedAt = new LinkedHashMap<>();
        // How each behavior reads the lines the module's declarations own. A behavior's own account
        // holds the lines it is owed a row at and none of these — that is what the account is for —
        // so a walk that looked only there would find no reading of a declared line anywhere and
        // answer that no row stands at one, of rows composed to stand at exactly that.
        Map<BorderObligationPoint, Map<String, List<BorderAssessment>>> declaredReadings =
                readingsOfTheDeclaredLines(db, module);
        // A reader for every behavior a row is written under, and not only for the ones a search
        // answered about. A row a declaration's line is owed is composed by whichever reading could
        // compose it, and that behavior need not be one anything else was asked of — read off the
        // searches alone, such a row came back undetermined at every item, so nothing it stands at
        // could ever make another row redundant.
        Map<String, OneBehavior> reading = new LinkedHashMap<>();
        Set<String> carriers = new LinkedHashSet<>(offering.rowsByBehavior().keySet());
        carriers.addAll(offering.searched().keySet());
        for (String behavior : carriers) {
            Adequacy.Filling filling = offering.searched().get(behavior);
            OneBehavior read = OneBehavior.of(db, module, behavior, filling,
                    sigs == null ? null : sigs.get(behavior), building, trials,
                    declaredReadings);
            if (read == null) {
                continue;   // nothing here can read a row of it, which its rows are told below
            }
            reading.put(behavior, read);
            requested.addAll(read.owed());
            if (filling != null) {
                composedFor.putAll(read.composed(filling));
                // The row and the input it was composed at, from the one value that holds both.
                // Taken from two askings, a line could end up with a row from one reading and an
                // input from another — which is the pair a report would then show a person.
                read.composedForALine().forEach((item, made) -> composedAt.put(item, made.at()));
            }
        }
        // And the points the module's declarations are owed, which are no behavior's own. A row of
        // whichever behavior composed one answers the line for everybody, so they are items of the
        // offering rather than of the block a row happens to sit in.
        if (offering.account() != null) {
            offering.account().resolved().forEach((point, answer) -> {
                ObligationIdentity item = new ObligationIdentity.OfALine(point);
                switch (answer.resolution()) {
                    case PointResolution.Generated(var at, var row) -> {
                        requested.add(item);
                        composedFor.put(item, RowKey.of(at.behavior(), row));
                    }
                    // Asked for and nothing came of it, which is still a thing this run is short of
                    // — and something else may stand there, which is what makes it worth asking.
                    case PointResolution.Unresolved _ -> requested.add(item);
                    // Not asked for at all: a row already stands there, or nothing measured it. A
                    // point in nobody's way is not work this run offers, and holding it here would
                    // let a candidate be the only offer for it.
                    case PointResolution.NoSearch _ -> { }
                }
            });
        }
        List<ObligationIdentity> items = List.copyOf(new LinkedHashSet<>(requested));
        offering.rowsByBehavior().forEach((behavior, rows) -> {
            OneBehavior read = reading.get(behavior);
            for (OfferedRow row : rows) {
                // Read once for the row and asked of every item. What a row is — where its values
                // sit and what running it recorded — does not change between the questions put to
                // it, and reading it per item would be the same row read as many times as this run
                // happens to be asked about, at the price of running it that many times.
                RowAsRead one = read == null ? RowAsRead.nothingRead() : read.read(row.toRun());
                Map<ObligationIdentity, Settlement> here = new LinkedHashMap<>();
                Map<ObligationIdentity, InputOfARowForALine> where = new LinkedHashMap<>();
                for (ObligationIdentity item : items) {
                    ToldApartAt answered = read == null
                            ? new ToldApartAt(undetermined(one), null)
                            : read.answerFor(one, item);
                    here.put(item, answered.said());
                    if (answered.at() != null) {
                        where.put(item, answered.at());
                    }
                }
                byRow.put(row.key(), Collections.unmodifiableMap(here));
                if (!where.isEmpty()) {
                    standsAt.put(row.key(), Collections.unmodifiableMap(where));
                }
            }
        });
        return new Settlements(items, composedFor, byRow, standsAt, composedAt);
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
            readingsOfTheDeclaredLines(Db db, String module) {
        Map<BorderObligationPoint, Map<String, List<BorderAssessment>>> out = new LinkedHashMap<>();
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
    private record OneBehavior(String behavior,
                               souther.compiler.partition.MeasuredInput subject, Sig sig,
                               BoundaryValues building, Generator.Trial trial,
                               List<GenerationObligation> obligations,
                               Map<Generator.ArmOwed, ObligationIdentity.OfAnArm> identityOfArm,
                               Map<ObligationIdentity.OfAnArm, Generator.ArmOwed> targetOfArm,
                               RulesTaken rules,
                               souther.compiler.partition.InteractionRequirements combinations,
                               Adequacy.Generated.RowsForRules ruleRows,
                               Map<ObligationIdentity.OfALine, List<AtAPoint>> reads,
                               Map<ObligationIdentity.OfABorder, List<ALineBesideOne>> besides) {

        /**
         * A reader for one behavior, and what this run asked of that behavior.
         *
         * <p><b>Two things, and a carrier may have only the first.</b> How a row is read is what its
         * positions are and what runs it; what this run asked for is a search's answer, and a
         * behavior that composed a row for somebody else's line was asked nothing. Read together,
         * the account of a behavior nothing was searched for is fetched to build it — which asks the
         * search this run had decided not to make, and puts its points into a universe as work
         * nobody was set.
         *
         * @param filling what this run asked of the behavior, or null where it asked nothing. A
         *                carrier with rows and no filling still has its rows read: what it holds is
         *                a row somebody else's line needed
         */
        static OneBehavior of(Db db, String module, String behavior, Adequacy.Filling filling,
                              Sig sig, BoundaryValues building,
                              souther.compiler.execute.RowTrials trials,
                              Map<BorderObligationPoint, Map<String, List<BorderAssessment>>>
                                      declared) {
            // What a row of this behavior is measured against, asked of the store rather than
            // taken off a search. A behavior that composed a row for a declaration's line and was
            // asked nothing else has no search to take it from, and its rows are read like any
            // other.
            souther.compiler.partition.MeasuredInput subject = Adequacy.subjectOf(db, module,
                    behavior);
            if (subject == null) {
                return null;
            }
            Map<ObligationIdentity.OfALine, List<AtAPoint>> reads = new LinkedHashMap<>();
            // Where this behavior meets each point its own rules are owed a row at. Read whether or
            // not anything was asked of the behavior, for the reason the declarations' lines below
            // are: a row written under it stands where it stands, and whether this run went looking
            // for one has nothing to do with it.
            //
            // Which row is offered there is not here. That is one search over every reading of the
            // point, and the module's account holds it ({@link BorderAccount}) — a behavior
            // resolving its own points beside that would be one search made twice, free to come to
            // two answers about one row.
            List<BorderObligationPointAssessment> points = db.ask(
                    new Adequacy.Obligations(module, new GenerationScope.Behavior(behavior),
                            Adequacy.OFFERED_ROWS_READ_AS))
                    .value();
            for (BorderObligationPointAssessment point
                    : points == null ? List.<BorderObligationPointAssessment>of() : points) {
                if (!point.belongsToBehaviorAccount(behavior)) {
                    continue;
                }
                ObligationIdentity.OfALine item = new ObligationIdentity.OfALine(point.point());
                point.met().forEach((_, at) -> reads.computeIfAbsent(item, _ -> new ArrayList<>())
                        .add(new AtAPoint(at.border(), at.owedAt(point.at()).criterion())));
            }
            // And this behavior's readings of the lines the declarations own, which its own rules
            // are owed none of. Read the same way and for the same reason.
            declared.forEach((point, byBehavior) -> {
                for (BorderAssessment at : byBehavior.getOrDefault(behavior, List.of())) {
                    if (at.at(point.point()) instanceof ItemAssessment.Owed owed) {
                        reads.computeIfAbsent(new ObligationIdentity.OfALine(point),
                                _ -> new ArrayList<>())
                                .add(new AtAPoint(at.border(), owed.criterion()));
                    }
                }
            });
            // Which occurrence each arm's search target is, both ways round. Read off
            // {@link Adequacy.RowsOwed} — the one place a fork's occurrences and the account
            // identity a row is offered under were bound together — and not off a second reading
            // of the body: worked out again here, from whatever this module's bodies happen to
            // elaborate to, it would be a second answer that a partial elaboration elsewhere in the
            // module could disagree with.
            //
            // Asked only where something was asked of this behavior, for the reason the lines
            // below are: a carrier with no filling owns no arm of its own — {@link #owed} and
            // {@link #composed} read no arm off an empty obligation list, and {@link #throughArm}
            // never reaches this behavior's own binding for an arm behind another behavior's item —
            // so asking here for a behavior nothing was asked of would be a search this run decided
            // not to make, paid for a map neither method would ever read.
            Map<Generator.ArmOwed, ObligationIdentity.OfAnArm> identityOfArm = new LinkedHashMap<>();
            Map<ObligationIdentity.OfAnArm, Generator.ArmOwed> targetOfArm = new LinkedHashMap<>();
            if (filling != null) {
                RowWork owed = db.ask(new Adequacy.RowsOwed(module, behavior)).value();
                if (owed != null) {
                    owed.arms().forEach((identity, target) -> {
                        identityOfArm.put(target, identity);
                        targetOfArm.put(identity, target);
                    });
                }
            }
            // And the lines of this behavior that the rows do not tell from the lines beside them,
            // which are the lines a row is offered for as whole lines rather than at a point.
            // Asked only where something was asked of this behavior: a carrier that composed a row
            // for somebody else's line was asked for none of its own, and reading them would make
            // the search this run decided not to make.
            //
            // One entry per reading of the line, the way the points above are. A row is composed
            // under one reading and is read back at every one of them: kept as one reading, a row
            // composed where one call site's conditions allow it would be read at another's and
            // answer nothing, and the line would be offered a second row it already has.
            Map<ObligationIdentity.OfABorder, List<ALineBesideOne>> besides = new LinkedHashMap<>();
            if (filling != null) {
                List<BorderAssessment> lines =
                        db.ask(new Adequacy.BoundarySearch(module, behavior)).value();
                for (BorderAssessment at : lines == null ? List.<BorderAssessment>of() : lines) {
                    if (!(at.beside() instanceof AnotherLineTheRowsAllow.OneDoes named)) {
                        continue;
                    }
                    ObligationIdentity.OfABorder item =
                            new ObligationIdentity.OfABorder(at.border().obligation());
                    for (ARowTellingTheLinesApart.AtOneReading one : at.toldApart().each()) {
                        besides.computeIfAbsent(item, _ -> new ArrayList<>())
                                .add(new ALineBesideOne(subject.at(one.reading()),
                                        OrderedAffineBoundary.of(one.reading()), named, one));
                    }
                }
            }
            // What this behavior was asked to offer a row for, which is the search's answer and
            // is nothing where nothing asked it.
            return new OneBehavior(behavior, subject, sig, building,
                    sig == null || trials == null ? Generator.Trial.NOTHING_RUNS
                            : Adequacy.runningRowsOf(trials, behavior, sig,
                                    Adequacy.numberingOf(db, module),
                                    RequiredDependencies.of(db, module, behavior)),
                    filling == null ? List.of() : filling.composed().plan().obligations(),
                    identityOfArm, targetOfArm, rulesOf(db, module, behavior),
                    combinationsOf(db, module, behavior, subject),
                    filling == null ? Adequacy.Generated.RowsForRules.NOTHING : filling.rules(),
                    reads, besides);
        }

        /**
         * The combinations of this body's decisions, and what a run that made each would be seen
         * doing.
         *
         * <p>Read off the one walk of the body this module holds, and under the measurement's own
         * budget: what the generation may spend on a group is a different question from how much of
         * the model is measured, and a behavior would otherwise be asked for what one dial allows
         * and measured against what the other does.
         *
         * <p>Nothing where the body was not lowered, which is a behavior with no meetings to state
         * requirements rather than one whose meetings state none.
         */
        private static souther.compiler.partition.InteractionRequirements combinationsOf(
                Db db, String module, String behavior,
                souther.compiler.partition.MeasuredInput subject) {
            Map<String, souther.compiler.reading.CoverageRead.Read> met =
                    db.ask(new Adequacy.Meets(module)).value();
            souther.compiler.reading.CoverageRead.Read here =
                    met == null ? null : met.get(behavior);
            if (here == null) {
                return souther.compiler.partition.InteractionRequirements.NONE;
            }
            return souther.compiler.partition.InteractionRequirements.of(behavior,
                    here.interactions(), subject.axes().axes(),
                    db.ask(new Front.Adequacy()).value().measures().cellsPerGroup());
        }

        /**
         * How a run of this behavior is placed among the rules of its decision, or null where the
         * body's decision could not be read.
         *
         * <p>Asked of the one placement this module has rather than made here. Which rules a body
         * states is one answer and how a run meets them is one more, and a second walk of either
         * would be free to place a run in a rule the account has no entry for.
         */
        private static RulesTaken rulesOf(Db db, String module, String behavior) {
            Map<String, RulesTaken> placed = db.ask(new Adequacy.Placements(module)).value();
            return placed == null ? null : placed.get(behavior);
        }

        /**
         * Which row was composed for each of them, where one was.
         *
         * <p>Read off what the searches answered with and never off the rows. A row carries the
         * classes and arms it may be named after and never a line, so a walk from the rows would
         * have every line in the block composed for nothing.
         *
         * <p>One switch over every kind the plan can hold, rather than one loop apiece. A kind
         * added to {@link GenerationObligation} without a case here does not compile, which is what
         * keeps this in step with what a run was actually asked for — three loops agreeing with
         * each other said nothing about whether either agreed with a fourth this held and never
         * walked.
         */
        Map<ObligationIdentity, RowKey> composed(Adequacy.Filling filling) {
            Map<ObligationIdentity, RowKey> out = new LinkedHashMap<>();
            for (GenerationObligation each : obligations) {
                switch (each) {
                    case GenerationObligation.Class(var target) -> {
                        if (filling.composed().discharge().at(target)
                                instanceof souther.compiler.partition.ClassDisposition.Built built) {
                            out.put(new ObligationIdentity.OfAClass(target),
                                    RowKey.of(behavior, filling.composed().rowFor(built.rowId())));
                        }
                    }
                    case GenerationObligation.Arm(var target) -> {
                        ObligationIdentity.OfAnArm identity = identityOfArm.get(target);
                        if (identity == null) {
                            throw new IllegalStateException(
                                    "the generation plan asks for an arm RowsOwed did not bind: "
                                            + target);
                        }
                        if (filling.composed().discharge().at(target)
                                instanceof souther.compiler.partition.ArmDisposition.Built built) {
                            out.put(identity,
                                    RowKey.of(behavior, filling.composed().rowFor(built.rowId())));
                        }
                    }
                    // The combination and not the space it sits in: the plan says which were
                    // asked for and the discharge says which got a row; read off the rows
                    // instead, a row that happens to sit in a combination nobody asked about
                    // would be published as having been composed for it.
                    case GenerationObligation.Pair(var target) -> {
                        if (filling.composed().discharge().at(target)
                                instanceof souther.compiler.partition.ClassDisposition.Built built) {
                            out.put(target,
                                    RowKey.of(behavior, filling.composed().rowFor(built.rowId())));
                        }
                    }
                    case GenerationObligation.Meeting(var target) -> {
                        if (filling.composed().discharge().at(target)
                                instanceof souther.compiler.partition.ClassDisposition.Built built) {
                            out.put(target,
                                    RowKey.of(behavior, filling.composed().rowFor(built.rowId())));
                        }
                    }
                }
            }
            filling.rules().byRule().forEach((rule, row) ->
                    out.put(new ObligationIdentity.OfADecisionRule(behavior, rule),
                            RowKey.of(behavior, row)));
            // And the row composed at a line the rows do not tell from another, where one was. The
            // reading that composed it says which row it is, and the first of them is the row the
            // block offers — read off any reading that has one, a line searched twice would be
            // said to have been composed for by a row nobody is offered.
            composedForALine().forEach((item, made) -> out.put(item, made.key()));
            return out;
        }

        /**
         * The row composed for each line the rows do not tell from another, and the input it was
         * composed at.
         *
         * <p><b>One value, because the two have to be one asking.</b> Which reading composed the
         * row and which input that reading composed it at are the same answer read twice, and two
         * walks arriving at it are two walks somebody has to keep in step — a report would then be
         * able to name the input of a row nobody is handed. There is nothing to keep in step here.
         *
         * <p>The input off the search and not off a reading of the row. What the realizer asked for
         * is what the row was built from, and it is the only thing there is to name for a row
         * nothing read back — which is a row a person is offered like any other.
         */
        Map<ObligationIdentity, ARowComposedForALine> composedForALine() {
            Map<ObligationIdentity, ARowComposedForALine> out = new LinkedHashMap<>();
            besides.forEach((item, readings) -> readings.stream()
                    .filter(one -> one.toldApart().composed().isPresent()).findFirst()
                    .ifPresent(one -> out.put(item, new ARowComposedForALine(
                            RowKey.of(behavior, one.toldApart().composed().orElseThrow().row()),
                            new InputOfARowForALine(one.reading().border(),
                                    one.toldApart().composedAt())))));
            return out;
        }

        /**
         * What this behavior was asked to offer a row for.
         *
         * <p>Every kind the plan can hold, in one switch, and no point of a line. A row at a point
         * is owed once however many readings there are, and it is offered from the module's
         * account of them — so a behavior listing its own points here would put one piece of work
         * into a run twice and let the two answer differently.
         */
        List<ObligationIdentity> owed() {
            List<ObligationIdentity> out = new ArrayList<>();
            for (GenerationObligation each : obligations) {
                switch (each) {
                    case GenerationObligation.Class(var target) ->
                            out.add(new ObligationIdentity.OfAClass(target));
                    // The arm and not the place a search steers a row to. A helper carrying a
                    // fork is spliced into each call site, so what the plan names is one of
                    // those occurrences — the one a run through this arm would be recorded at,
                    // chosen where the finding was made. What a row is offered for is the arm.
                    case GenerationObligation.Arm(var target) -> {
                        ObligationIdentity.OfAnArm identity = identityOfArm.get(target);
                        if (identity == null) {
                            throw new IllegalStateException(
                                    "the generation plan asks for an arm RowsOwed did not bind: "
                                            + target);
                        }
                        out.add(identity);
                    }
                    // The combination this run was asked about, which is the plan's answer: what
                    // the criterion states is the account's, and a universe read off the space
                    // here would hold what nobody asked for.
                    case GenerationObligation.Pair(var target) -> out.add(target);
                    // A meeting is not an arm — rows through every arm of a body can leave one
                    // unmade — so it is owed in its own right and not reached through the arms
                    // it claims.
                    case GenerationObligation.Meeting(var target) -> out.add(target);
                }
            }
            // And every rule of this behavior's decision a row was asked for, which is not the
            // rules a row was composed for. A row composed for a class may take a rule as well,
            // and a universe read off what this run managed to compose would leave such a rule
            // with nothing weighing that row against it — so the block would offer a row for a
            // rule its own row already discharges.
            ruleRows.asked().forEach(rule ->
                    out.add(new ObligationIdentity.OfADecisionRule(behavior, rule)));
            // And every line the rows do not tell from a line beside it. The whole line and not a
            // point of it: what a row here shows is which of two lines the model draws, and a line
            // is what two lines are two of.
            out.addAll(besides.keySet());
            return out;
        }

        /** The row as the two things every question here is put to ({@link RowAsRead}). */
        RowAsRead read(RowToRun row) {
            return RowAsRead.of(sig, building, trial, row);
        }

        /**
         * What this row would do about {@code item}, and where it stands if the item is a line it
         * answers.
         *
         * <p>One question, because reading the row is the expensive half and the two answers come
         * out of one reading. Asked apart, a caller wanting the place would put the row through the
         * line a second time — and could be handed a place from a reading the settlement was not
         * made at.
         *
         * <p>{@code at} is empty for every item but a whole line. A class is where a value falls
         * and an arm is a place a run went, and neither is somewhere a report sends a reader.
         */
        ToldApartAt answerFor(RowAsRead asRead, ObligationIdentity item) {
            if (item instanceof ObligationIdentity.OfABorder line) {
                return tellingTheLinesApart(asRead, line);
            }
            return new ToldApartAt(settlementOf(asRead, item), null);
        }

        private Settlement settlementOf(RowAsRead asRead, ObligationIdentity item) {
            return switch (item) {
                case ObligationIdentity.OfAClass(var owed) -> inClass(asRead, owed);
                // A case of an input of a behavior that divides no position of its own. Nothing
                // asks for a row at one — what is offered comes from the classes a position
                // divides into — and what discharges it is what a row states at that input, which
                // the signature measure counts off the row's own text. Answered here as well, that
                // would be a second reading of one relation, made from the values a row builds
                // rather than from what it states.
                //
                // A case of the output is the same relation read the other way round, and what
                // discharges it is what a row states as well.
                //
                // And a row waiting for its answer is discharged by nothing composed at all: what
                // it is owed is what the system does, written where that row is by somebody who
                // knows it, and a row composed here would be a second row rather than that answer.
                case ObligationIdentity.OfAnInputCase _, ObligationIdentity.OfAnOutputCase _,
                     ObligationIdentity.OfARow _ -> throw new IllegalStateException(
                        "no row is offered for " + item + ", so none is weighed against it");
                case ObligationIdentity.OfABorder at -> tellingTheLinesApart(asRead, at).said();
                case ObligationIdentity.OfAnArm owed -> throughArm(asRead, owed);
                case ObligationIdentity.OfALine at -> atThePoint(asRead, at);
                case ObligationIdentity.OfADecisionRule owed -> takingTheRule(asRead, owed);
                case ObligationIdentity.OfACombinationOfDecisions owed ->
                        makingTheDecisions(asRead, owed);
                case ObligationIdentity.OfAFallbackPairCell owed -> inBothClasses(asRead, owed);
            };
        }

        /**
         * Whether running the row made the decisions the combination is of.
         *
         * <p>The run and not the values. What a combination of a body's decisions asks for is that
         * they were settled those ways together, and a row whose values sit where a search would
         * have steered it may have gone elsewhere — which is the reading this measure exists to
         * stop standing in for the fact.
         *
         * <p>Some one way of arriving at them, which {@link InteractionRequirements} answers. Where
         * this behavior states no way to the combination it is another behavior's, and a row
         * written here does not settle it.
         */
        private Settlement makingTheDecisions(RowAsRead asRead,
                                              ObligationIdentity.OfACombinationOfDecisions owed) {
            if (!behavior.equals(owed.behavior())) {
                return new Settlement.DoesNotSettle();
            }
            return switch (asRead.watched()) {
                case Generator.Watched.Ran(var account) ->
                        combinations.met(owed, claim -> claim.satisfiedBy(account))
                                ? new Settlement.Settles() : new Settlement.DoesNotSettle();
                case Generator.Watched.NoAccount _ ->
                        new Settlement.Undetermined(Settlement.Reason.NO_ACCOUNT_OF_THE_RUN);
            };
        }

        /**
         * Whether the row's values sit in both classes of the pair.
         *
         * <p>The values and not the run, which is where this parts from the combination above. A
         * fallback pair is the criterion of a behavior whose decisions meet nowhere — and of one
         * with no body at all — so there is nothing for a run to have been seen doing, and where a
         * row sits is the whole of the evidence there is.
         *
         * <p>Undetermined where either position could not be read. A row placed at one class and
         * unreadable at the other says nothing about the pair, and reading the second as a miss
         * would report a combination as untried on the strength of a value nobody could classify.
         */
        private Settlement inBothClasses(RowAsRead asRead,
                                         ObligationIdentity.OfAFallbackPairCell owed) {
            Settlement answer = new Settlement.Settles();
            for (ClassOfAPosition each : owed.inOrder()) {
                Settlement here = inClass(asRead, each);
                if (here instanceof Settlement.DoesNotSettle) {
                    return here;
                }
                if (here instanceof Settlement.Undetermined) {
                    answer = here;
                }
            }
            return answer;
        }

        /**
         * Whether running the row takes the rule.
         *
         * <p>Not something the values answer. A rule is a way through the body and what a row does
         * is where its run went, so the account of the run is the whole of the evidence — and where
         * there is none, this says so rather than reading the absence as a row that went elsewhere.
         *
         * <p>Of this behavior's rules only. A rule is written in the terms of one body's positions,
         * so a rule of another behavior is not something a row written here goes down.
         */
        private Settlement takingTheRule(RowAsRead asRead,
                                         ObligationIdentity.OfADecisionRule owed) {
            if (!behavior.equals(owed.behavior()) || rules == null) {
                return new Settlement.DoesNotSettle();
            }
            return switch (asRead.watched()) {
                case Generator.Watched.Ran(var account) -> switch (rules.takenBy(account)) {
                    case RulesTaken.WhichRule.TookThis took ->
                            took.rule().equals(owed.rule())
                                    ? new Settlement.Settles() : new Settlement.DoesNotSettle();
                    // A run this reading could not place says nothing about where the row went,
                    // which is this compiler falling short rather than the row missing.
                    case RulesTaken.WhichRule.CouldNotTell _ ->
                            new Settlement.Undetermined(
                                    Settlement.Reason.THE_VALUES_COULD_NOT_BE_READ);
                };
                case Generator.Watched.NoAccount _ ->
                        new Settlement.Undetermined(Settlement.Reason.NO_ACCOUNT_OF_THE_RUN);
            };
        }

        /**
         * Whether the row's value at the position falls in the class.
         *
         * <p>Of this behavior's positions only. An axis names the behavior it divides, so a class of
         * another one is not something a row written here has a value at — which is a row that does
         * not settle it rather than one nothing could tell about.
         */
        private Settlement inClass(RowAsRead asRead, ClassOfAPosition owed) {
            if (!behavior.equals(owed.at().behavior())) {
                return new Settlement.DoesNotSettle();
            }
            if (asRead.values() == null) {
                return undetermined(asRead);
            }
            Classification at =
                    InputClassifications.of(asRead.values(), subject.axes()).get(owed.at());
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
        private Settlement throughArm(RowAsRead asRead, ObligationIdentity.OfAnArm owed) {
            // The whole table asks every row about every item, including an arm of a behavior
            // other than the one the row was composed for — and this behavior's own binding has
            // nothing to say about such an arm, which is not the same as this behavior having lost
            // track of one of its own.
            if (!behavior.equals(owed.arm().behavior())) {
                return new Settlement.DoesNotSettle();
            }
            Generator.ArmOwed target = targetOfArm.get(owed);
            if (target == null) {
                throw new IllegalStateException(
                        "this behavior is asked about an arm with no search target: " + owed);
            }
            return switch (asRead.watched()) {
                // Any occurrence of it. The arm is what the author wrote and a helper carrying it
                // stands in the running tree once per call site, so a run through any of those is
                // a run through the arm — which is the reading the arm account already takes.
                case Generator.Watched.Ran(var account) ->
                        target.occurrences().stream().anyMatch(account::lit)
                                ? new Settlement.Settles() : new Settlement.DoesNotSettle();
                case Generator.Watched.NoAccount _ ->
                        new Settlement.Undetermined(Settlement.Reason.NO_ACCOUNT_OF_THE_RUN);
            };
        }

        /**
         * Whether writing this row would show which of the two lines the model draws.
         *
         * <p>The question the finding asks and nothing narrower. What settles it is a row the
         * model's own rule refuses and the line beside it keeps, or the other way about — so it is
         * asked of the row's values under both lines, and never of where the row was composed. A
         * row composed elsewhere that happens to answer this settles it as much as the one composed
         * for it, which is what every entry of this table is for.
         *
         * <p>Over the readings this behavior has of the line, existentially: a row answering the
         * two lines differently at any position the behavior reads the line at is a row that shows
         * which of them it is.
         */
        private ToldApartAt tellingTheLinesApart(RowAsRead asRead,
                                                 ObligationIdentity.OfABorder at) {
            List<ALineBesideOne> here = besides.get(at);
            if (here == null || here.isEmpty()) {
                // No line of this behavior. A row written here says nothing about a line it is not
                // read against, which is a row that does not settle it rather than one nothing
                // could tell about.
                return new ToldApartAt(new Settlement.DoesNotSettle(), null);
            }
            if (asRead.values() == null) {
                return new ToldApartAt(undetermined(asRead), null);
            }
            // Existential over the readings, the way a point met at one position of a behavior is:
            // a row answering the two lines differently anywhere the behavior reads the line is a
            // row that shows which of them it is. A reading that could not tell is carried and does
            // not decide, so a run nothing watched does not turn a row that settles into one that
            // is open.
            ToldApartAt answer = new ToldApartAt(new Settlement.DoesNotSettle(), null);
            for (ALineBesideOne one : here) {
                ToldApartAt said = tellsThemApartAt(asRead, one);
                if (said.said().settles()) {
                    return said;
                }
                if (said.said() instanceof Settlement.Undetermined) {
                    answer = said;
                }
            }
            return answer;
        }

        /**
         * The same question at one reading of the line.
         *
         * <p>The row read at the positions that reading names, and the two lines put to those
         * values. Which is why the reading is what this is asked of rather than the line: how far
         * apart two positions stand is a number a reading has, and another reading of the same line
         * is over other positions.
         */
        private ToldApartAt tellsThemApartAt(RowAsRead asRead, ALineBesideOne one) {
            StandingAtAPoint.RowsRead read = StandingAtAPoint.valuesOf(one.reading(),
                    List.of(asRead.asInputs()), one.reading().border().origin().recordedAt());
            if (read.each().isEmpty()) {
                // The row holds no value on this line at all, whether because nothing watched its
                // run or because its positions could not be read there. Which of those it is is
                // the reading's own answer and is what a reader is told.
                return new ToldApartAt(read.everyOne() ? new Settlement.DoesNotSettle()
                        : new Settlement.Undetermined(read.unwatched()
                                ? Settlement.Reason.NO_ACCOUNT_OF_THE_RUN
                                : Settlement.Reason.THE_VALUES_COULD_NOT_BE_READ), null);
            }
            for (Map<NumericTerm, Place> values : read.each()) {
                if (one.drawn().satisfiedBy(values) != one.beside().keeps(values)) {
                    // Where it answered them differently, kept beside the answer. What a person is
                    // shown for this line is where the row they are handed stands, and that is this
                    // — worked out again by whoever shows it, it would be a second reading of the
                    // row, free to name a reading this one did not settle at.
                    return new ToldApartAt(new Settlement.Settles(),
                            new InputOfARowForALine(one.reading().border(), values));
                }
            }
            return new ToldApartAt(new Settlement.DoesNotSettle(), null);
        }

        /**
         * Whether the row stands at the point, as this behavior reads the line.
         *
         * <p>A line is owed a row once and is met at whichever position reads it, so a point this
         * behavior's readings do not meet is one a row written here does not settle. Where they do,
         * the walk that reads a written row against the point reads this one.
         */
        private Settlement atThePoint(RowAsRead asRead, ObligationIdentity.OfALine at) {
            List<AtAPoint> here = reads.get(at);
            if (here == null || here.isEmpty()) {
                // No reading of this line in this behavior. A row written here has no value on the
                // line at all, which is a row that does not settle the point rather than one
                // nothing could tell about.
                return new Settlement.DoesNotSettle();
            }
            if (asRead.values() == null) {
                return undetermined(asRead);
            }
            ObservedInputs observed = asRead.asInputs();
            // Existential over the readings, the way a point met at one position of a behavior is
            // met: a row standing on the line anywhere the behavior reads it is a row at the point.
            Settlement answer = new Settlement.DoesNotSettle();
            for (AtAPoint one : here) {
                Settlement said = switch (StandingAtAPoint.met(subject.at(one.line()),
                        List.of(observed), one.criterion(),
                        one.line().origin().recordedAt())) {
                    case StandingAtAPoint.Met.Reached _ -> new Settlement.Settles();
                    case StandingAtAPoint.Met.NotAtPoint _ -> new Settlement.DoesNotSettle();
                    case StandingAtAPoint.Met.NotWatched _ ->
                            new Settlement.Undetermined(Settlement.Reason.NO_ACCOUNT_OF_THE_RUN);
                    // Whichever reason there was none, this reader is deciding whether the row
                    // before it answers the point, and none of them lets it say so.
                    case StandingAtAPoint.Met.CouldNotTell _ -> new Settlement.Undetermined(
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
     * The row a search composed for one line, and the input it composed it at.
     *
     * <p>Two facts about one asking, so they travel as one value. Which reading composed the row
     * decides both, and a caller holding them apart is a caller that can hand over the row from one
     * reading beside the input from another.
     */
    private record ARowComposedForALine(RowKey key, InputOfARowForALine at) {

        private ARowComposedForALine {
            if (key == null || at == null) {
                throw new IllegalArgumentException(
                        "a row composed for a line was composed somewhere: " + key);
            }
        }
    }

    /**
     * What a row does about one line, and where it stands on it where that is the answer.
     *
     * <p>The two together because one reading of the row produced both. A place beside a settlement
     * that is not {@link Settlement.Settles} would be a row shown as answering a line it does not.
     */
    private record ToldApartAt(Settlement said, InputOfARowForALine at) {

        private ToldApartAt {
            if (at != null && !said.settles()) {
                throw new IllegalArgumentException("a row shown standing on a line it does not"
                        + " answer: " + at.said());
            }
        }
    }

    /**
     * One line the rows do not tell from a line beside it, as a row is put to it.
     *
     * <p>The line the model drew, the line these rows leave standing beside it, and what a search
     * for a row telling the two apart came to. All three, because the question a row is put here is
     * about the pair: a row settles this by answering differently under the two, which neither of
     * them says alone.
     *
     * <p><b>The line as this behavior reads it, and as the inequality it is, worked out once.</b>
     * Both are settled by the border and by nothing a row says, and a row is put to this once per
     * row a run offers — derived where the question is asked, finding the reading walks every line
     * of the behavior and reading the inequality folds the quantity's own step, once per row for an
     * answer that was the same every time.
     */
    private record ALineBesideOne(MeasuredInput.BorderReading reading, OrderedAffineBoundary drawn,
                                  AnotherLineTheRowsAllow.OneDoes beside,
                                  ARowTellingTheLinesApart.AtOneReading toldApart) {

        ALineBesideOne {
            if (drawn == null) {
                // A rule that names a value orders nothing, so no line beside it is ever named.
                // Refused where the pair is put together rather than where a row is weighed against
                // it: what it says is that the measurement and this account disagree about the
                // line, which is true of the pair whether or not a row is ever offered.
                throw new IllegalStateException("a line the rows allow beside a rule that orders"
                        + " nothing: " + reading.border().obligation());
            }
        }
    }

    /** What an item that needs the values is told, where they are not here. */
    private static Settlement undetermined(RowAsRead asRead) {
        return new Settlement.Undetermined(asRead.whyNotRead());
    }
}
