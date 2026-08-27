package souther.compiler.query;

import souther.compiler.partition.FixtureTemplate;
import souther.compiler.partition.Generator;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.SequencedMap;

/**
 * The rows one run hands a person, under the behavior each is written for.
 *
 * <p>What a run offers is one answer, made where both halves of it are. A behavior's own rows and
 * the rows a declaration's line is owed are composed by two searches asked in two ways, and they
 * meet as work for one person: a line is one piece of work and is offered once, in the terms of
 * whichever reading composed it. Put together where the block is written, the meeting was a step of
 * the layout — so what a run offers could only be said by printing it.
 *
 * <p>Nothing here is evidence of coverage. A row this holds is a question — these inputs, and what
 * does the system answer? — and what it would settle if it were written is not something this says.
 *
 * <p>And what the two searches came to beside the rows they composed, which is the other half of
 * what a person is owed: a block that printed only what it managed would read as though it had
 * filled everything. The rows are this one's answer; those are the searches' own, carried here so
 * that whoever writes the block asks one question rather than putting the halves together again.
 *
 * @param request  what was asked for, which is what settles which rows are here
 * @param rows     one entry per behavior with rows to offer, in the order they were asked about
 * @param searched what each behavior's own search came to, keyed the way a report keys them
 * @param declared what the module's declarations are owed, or null where the request asked for no
 *                 boundary rows — which is not the same as a request that asked and found none
 * @param answered what the rows here settle: every item one of them would answer if it were
 *                 written, whichever row it was composed for. Empty on a composition nobody has
 *                 put the question to, which is a run that has not been asked rather than one whose
 *                 rows answer nothing
 */
public record Offering(OfferingRequest request, SequencedMap<String, List<OfferedRow>> rows,
                       SequencedMap<String, Adequacy.Filling> searched, DeclaredRows declared,
                       java.util.Set<OfferItem> answered) {

    public Offering {
        rows = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(rows));
        searched = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(searched));
        answered = java.util.Collections.unmodifiableSet(
                new java.util.LinkedHashSet<>(answered));
    }

    /**
     * One row as it will be written, and what it may be named after.
     *
     * <p>A candidate is composed once per thing it is owed for and the positions that thing does not
     * name hold whatever the row has to hold, so two of them can come out as one row. What is
     * offered is the row: a reader is handed one piece of work rather than the same values twice.
     *
     * <p><b>Every purpose a cell composed it for, and not the first.</b> Two purposes converging on
     * one row is a fact about this run, and keeping one of them leaves a name that says the row is
     * about one thing while it answers two.
     *
     * <p><b>And nothing from a line.</b> A cell can name a row — a candidate's values follow from
     * the classes it was composed for, so the cell a row is named by is the row's own and is there
     * whatever else this run offers. A line cannot: lines coincide, each probe filling the positions
     * its own edge does not name from the bottom of their domains, so two minimum edges compose one
     * row and which of them is offered is exactly what changes when something else is written. A row
     * named for whichever line happened to be offered would be renamed by an edit that did not touch
     * it. So a row composed only at lines is offered with nothing to be named after, which the
     * language allows — an unnamed row cannot be addressed from outside, and that is the state of a
     * row nobody has named yet.
     *
     * @param key      what tells this row from the others a person is handed
     * @param inputs   the values, as the search composed them. One row's worth: rows that came out
     *                 as one piece of work are written the same way, so which of them these came
     *                 from is not a difference anybody can read
     * @param namedFor the classes and arms this row was composed for, in the order they were taken
     */
    public record OfferedRow(RowKey key, List<FixtureTemplate> inputs,
                             List<Generator.Purpose> namedFor) {

        public OfferedRow {
            inputs = List.copyOf(inputs);
            namedFor = List.copyOf(namedFor);
            for (Generator.Purpose purpose : namedFor) {
                if (!(purpose instanceof Generator.Purpose.ForAClass
                        || purpose instanceof Generator.Purpose.ForAnArm)) {
                    throw new IllegalArgumentException(
                            "a row is named after a class or an arm, and never after a line: "
                                    + purpose);
                }
            }
        }

        /** The row with {@code more} added to what it may be named after. */
        OfferedRow and(List<Generator.Purpose> more) {
            if (more.isEmpty()) {
                return this;
            }
            List<Generator.Purpose> both = new ArrayList<>(namedFor);
            both.addAll(more);
            return new OfferedRow(key, inputs, both);
        }
    }

    /**
     * What the two searches composed, before anything asks what the rows settle.
     *
     * <p>Not what a person is handed. A row here may answer what another here answers, and which of
     * them goes out is settled by asking — {@link Adequacy#offeredFor} is where that happens, and
     * what it hands back is the offering. So {@link #answered} is empty on one of these, which says
     * nobody has asked rather than that the rows answer nothing.
     *
     * <p>Walked in the order the behaviors were asked about, and within a behavior the cells before
     * the lines. The order a person is offered the rows in is the order they were composed in, and a
     * block read against the one before it is read by somebody who did not change the model between
     * them.
     *
     * @param generated one filling per behavior, keyed the way a report keys them
     * @param declared  the rows the module's declarations are owed, or null where the request asked
     *                  for no boundary rows. One row per point of a line however many behaviors
     *                  carry the type, and under the behavior whose reading composed it
     */
    public static Offering composed(OfferingRequest request,
                                    Map<String, Adequacy.Filling> generated,
                                    DeclaredRows declared) {
        Map<String, List<Generator.GeneratedRow>> owed = declared == null
                ? Map.of() : declared.rowsByCarrier();
        SequencedMap<String, Map<RowKey, OfferedRow>> byBehavior = new LinkedHashMap<>();
        for (Map.Entry<String, Adequacy.Filling> behavior : generated.entrySet()) {
            take(byBehavior, behavior.getKey(), behavior.getValue().composed().rows(),
                    request.boundaries()
                            ? atTheLines(behavior.getValue().boundaries().rows(),
                                    owed.get(behavior.getKey()))
                            : List.of());
        }
        // A behavior with nothing of its own to fill can still be the one reading that composed the
        // row a declaration is owed. Left out, that row would be resolved and then dropped on the
        // way to the block.
        for (Map.Entry<String, List<Generator.GeneratedRow>> carrier : owed.entrySet()) {
            if (!generated.containsKey(carrier.getKey())) {
                take(byBehavior, carrier.getKey(), List.of(), carrier.getValue());
            }
        }
        SequencedMap<String, List<OfferedRow>> out = new LinkedHashMap<>();
        byBehavior.forEach((behavior, here) -> out.put(behavior, List.copyOf(here.values())));
        return new Offering(request, out, new LinkedHashMap<>(generated), declared,
                java.util.Set.of());
    }

    /** One behavior's rows, joined onto whatever it already offers. */
    private static void take(SequencedMap<String, Map<RowKey, OfferedRow>> byBehavior,
                             String behavior, List<Generator.GeneratedRow> cells,
                             List<Generator.GeneratedRow> lines) {
        // One block per behavior, however many kinds of row it holds. Rows of one behavior written
        // under two headings are legal and read as two lists of something, which they are not.
        Map<RowKey, OfferedRow> here =
                byBehavior.computeIfAbsent(behavior, _ -> new LinkedHashMap<>());
        for (Generator.GeneratedRow row : cells) {
            RowKey key = RowKey.of(behavior, row);
            here.put(key, here.computeIfAbsent(key,
                    _ -> new OfferedRow(key, row.inputs(), List.of())).and(row.purposes()));
        }
        for (Generator.GeneratedRow row : lines) {
            RowKey key = RowKey.of(behavior, row);
            here.putIfAbsent(key, new OfferedRow(key, row.inputs(), List.of()));
        }
    }

    /**
     * The rows at one behavior's lines: the ones its own readings are owed, and the ones a
     * declaration is owed that this behavior's reading composed.
     *
     * <p>Two sources and one list, because they are one kind of row — a value standing at a line —
     * and what tells them apart is who owes the line rather than anything a reader of the block
     * would act on. Where they coincide the block offers one row, which is what it already does for
     * two of a behavior's own lines that meet.
     *
     * <p>Public because it is a question and not a step of the layout: what is offered at one
     * behavior's lines is what a reader of the block beside that behavior sees, and it is asked
     * elsewhere. Written twice, the two would come apart the day either half of the join moved.
     */
    public static List<Generator.GeneratedRow> atTheLines(List<Generator.GeneratedRow> own,
                                                          List<Generator.GeneratedRow> owed) {
        if (owed == null || owed.isEmpty()) {
            return own;
        }
        List<Generator.GeneratedRow> out = new ArrayList<>(own);
        out.addAll(owed);
        return List.copyOf(out);
    }

    /** How many pieces of work this offers, which is what a block says at the top of it. */
    public int count() {
        return rows.values().stream().mapToInt(List::size).sum();
    }

    /**
     * The same offering with only {@code kept} in it.
     *
     * <p>The rows and nothing else. What the searches came to is what they came to whatever a person
     * is handed afterwards — a row not offered was still composed, and the note beside a search that
     * came to nothing says what happened rather than what is in the block.
     */
    public Offering keeping(java.util.Set<RowKey> kept, java.util.Set<OfferItem> answered) {
        SequencedMap<String, List<OfferedRow>> out = new LinkedHashMap<>();
        rows.forEach((behavior, here) -> {
            List<OfferedRow> left = here.stream().filter(row -> kept.contains(row.key())).toList();
            if (!left.isEmpty()) {
                out.put(behavior, left);
            }
        });
        return new Offering(request, out, searched, declared, answered);
    }
}
