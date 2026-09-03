package souther.compiler.partition;

import souther.compiler.coverage.Observation;
import souther.compiler.coverage.RunRecord;
import souther.compiler.coverage.SiteNumbering;
import souther.compiler.observe.Counting;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.RowOutcome;

import java.util.List;

/**
 * A tuple of values and what running them recorded.
 *
 * <p>The two things anything here reads of a row, and neither of them is the row. Where the values
 * sit is what says which classes they fill and whether they stand at a line; what the run did is
 * what says which arms of the body they went through. The second does not follow from the first — a
 * tuple whose values sit in a combination's classes and whose run went elsewhere took none of the
 * arms it names, and looks from the values alone exactly like one that took them.
 *
 * <p><b>What a caller has a tuple for, it hands over.</b> A written {@code example} row has one and
 * so does a candidate the generator has just built, and the questions put to them here are the same
 * questions. Written to take a row, every one of those questions could only be asked of what is
 * already in the file, and a second answer written for the other kind would be the same rule twice
 * — free to agree until one of them moved.
 *
 * <p>Nothing here says a tuple covers anything. What it is a tuple of, and what its run reached, are
 * facts about the values; whether the module is covered is a measure over the rows that are written,
 * and it is made elsewhere.
 *
 * @param inputs  one value per parameter, in the order the behavior takes them
 * @param watched what came of running it. A sum and not an account that may be empty: a run that
 *                recorded nothing and a tuple nothing recorded are the same empty account and are
 *                not the same fact, and which of them this is decides what may be concluded
 */
public record ObservedInputs(List<ObservedValue> inputs, Generator.Watched watched) {

    public ObservedInputs {
        inputs = List.copyOf(inputs);
        // Said and not left out. Having no account of the run is one of the two answers here, and a
        // caller that has nothing to say says that one; taken as an absence to be filled in, the
        // distinction this holds would be made by whoever forgot to pass it.
        java.util.Objects.requireNonNull(watched, "a tuple says what came of running it");
    }

    /**
     * A written row read as the two things above.
     *
     * <p>What the run recorded, and not whether this build was recording. Whether anything was
     * watching is the caller's own — it follows from what was asked for rather than from the row —
     * and a reading that took it in would answer differently about one row depending on who asked.
     */
    public static ObservedInputs of(RowOutcome row,
                                    SiteNumbering numbering) {
        return new ObservedInputs(row.inputs(), switch (row.run().counting()) {
            // Read under the numbering asking, which is where the numbers a run left behind become
            // places. A recording made under another one is refused here rather than answered
            // about places it was never near.
            case Counting.Read(long _, RunRecord.Recorded(Observation seen)) ->
                    new Generator.Watched.Ran(numbering.align(seen));
            // And a row nothing watched has no account of where it went, whether that is because
            // the compile records nothing or because its counting was never read at all.
            case Counting.Read(long _, RunRecord.NoAccount _) ->
                    new Generator.Watched.NoAccount();
            case Counting.Unread _ -> new Generator.Watched.NoAccount();
        });
    }

}
