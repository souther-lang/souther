package souther.compiler.query;

import souther.compiler.partition.FixtureTemplate;
import souther.compiler.partition.Generator;
import souther.compiler.partition.RepairShortfall;
import souther.compiler.partition.RowToRun;
import souther.compiler.partition.StoodInAnswer;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;

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
 * <p>A rule of the body's decision is the row's own the same way an arm is: the search that
 * composed the row ran it and saw it take the way, so nothing an edit does elsewhere moves what it
 * is for. What it has no word for is a name — a rule is told from the rules beside it by the
 * conditions it turns on, and those are said under the row rather than in it.
 *
 * @param answers  what the row stands each asking of a dependency in with. A row of a behavior
 *                 that requires one is not a row anybody can run until something answers for it,
 *                 so the stand-ins go out with the row — every dependency the target requires, and
 *                 not only the ones its decision turns on
 * @param namedFor the classes, arms and rules this row was composed for, in the order they were
 *                 taken
 * @param stops    what looking for a row that goes further came to, for each search that composed
 *                 this row and took it no further than a guard — each once, in the order they
 *                 arrived, and each saying which requirement it was looked for
 *                 ({@link RepairShortfall#soughtFor}). A row two searches arrive at stops where it
 *                 stops for both of them, and what each found out is about its own requirement,
 *                 so neither is the other's to drop and neither is read as the other's
 */
public record OfferedRow(RowKey key, List<FixtureTemplate> inputs, List<StoodInAnswer> answers,
                         List<Generator.Purpose> namedFor, List<RepairShortfall> stops) {

    public OfferedRow {
        inputs = List.copyOf(inputs);
        answers = List.copyOf(answers);
        namedFor = List.copyOf(namedFor);
        stops = List.copyOf(new LinkedHashSet<>(stops));
        for (Generator.Purpose purpose : namedFor) {
            // A combination of two classes is one of these too, where the pair space is what the
            // behavior is held to: the search composed the row for it and the row's own values are
            // what settle it, so nothing an edit does elsewhere moves what it is for. A rewrite of
            // the body is one as well: the search ran the row under the body and under the rewrite
            // and saw the two answer differently, which is the row's own run.
            if (!(purpose instanceof Generator.Purpose.ForAClass
                    || purpose instanceof Generator.Purpose.ForAnArm
                    || purpose instanceof Generator.Purpose.ForADecisionRule
                    || purpose instanceof Generator.Purpose.ForAFallbackPairCell
                    || purpose instanceof Generator.Purpose.ForACombinationOfDecisions
                    || purpose instanceof Generator.Purpose.ForAReplacement)) {
                throw new IllegalArgumentException(
                        "a row is composed for a class, an arm, a rule, a combination the body"
                                + " settles a value by or a rewrite of the body, and never for a"
                                + " line: " + purpose);
            }
        }
    }

    /** The row as everything it takes to run one. */
    public RowToRun toRun() {
        return new RowToRun(inputs, answers);
    }

    /** A row of these values offered for nothing yet, which is what the first road to it makes. */
    static OfferedRow of(RowKey key, Generator.GeneratedRow row) {
        return new OfferedRow(key, row.inputs(), row.answers(), List.of(), List.of());
    }

    /**
     * The row with what {@code row} was composed for added to what it may be named after, and
     * where it stops at a guard, what looking past it came to ({@code stop}, or null where there
     * is nothing to say).
     *
     * <p>One join for both. A road that brought the purposes here and left what its search found
     * out behind would offer the row as the answer to that requirement with nothing said about
     * where it stops.
     */
    OfferedRow and(Generator.GeneratedRow row, RepairShortfall stop) {
        if (row.purposes().isEmpty() && stop == null) {
            return this;
        }
        List<Generator.Purpose> both = new ArrayList<>(namedFor);
        both.addAll(row.purposes());
        List<RepairShortfall> all = new ArrayList<>(stops);
        if (stop != null) {
            all.add(stop);
        }
        return new OfferedRow(key, inputs, answers, both, all);
    }
}
