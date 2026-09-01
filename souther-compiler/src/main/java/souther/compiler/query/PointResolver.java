package souther.compiler.query;

import souther.compiler.partition.Generator;
import souther.compiler.query.BorderObligationPointAssessment.Reading;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.SequencedMap;
import java.util.function.Function;

/**
 * Which reading of an authored line composes the one row it is owed.
 *
 * <p>A row at a line is composed by walking one behavior's inputs, and a line is read wherever the
 * model carries the rule — so this is a search over the readings and not a fold of them. What it
 * does is walk them in the order the module declares them and stop at the first that composed a
 * row.
 *
 * <p><b>Whose the line is makes no difference here.</b> A clause of a {@code data} is read once per
 * position of every behavior carrying the type; a guard on a name the cases of a sum spread is read
 * once under each case of one behavior's own input. Either way the readings ask the same of a row
 * and any one of them that composes one answers the point, and either way taking a reading instead
 * of searching them is offering whatever that reading came to.
 *
 * <p><b>Nothing here asks anything.</b> What each reading holds is handed in, so what was searched
 * and what may be concluded from it are two pieces of code rather than one. The conclusions — a row
 * is enough from any one reading, a terminal answer takes all of them — are then decidable from a
 * value, and a test of them does not have to arrange a compilation to ask a question of.
 *
 * <p>Which is also what keeps the walk from being read off a database. The readings some earlier
 * caller happened to have paid for are not the readings this request is about, and a resolver that
 * enumerated them would answer differently depending on the order the requests arrived in.
 */
public final class PointResolver {

    /**
     * What one reading of a line holds, as the walk finds it.
     *
     * <p>Three states, told apart because they license three different things. A reading that was
     * searched says something about the point; a search with no answer says something about this
     * run; a reading nobody asked about says nothing at all.
     */
    public sealed interface ReadingEvidence {

        /**
         * The reading was searched, and this is what the search made of the point.
         *
         * <p>Never null. A reading covered by a search that composed nothing at a point the line is
         * owed a row at is the search and the debt disagreeing about the same point, which the walk
         * refuses rather than records.
         */
        record Searched(ItemAssessment.Attempt attempt) implements ReadingEvidence {

            public Searched {
                if (attempt == null) {
                    throw new IllegalArgumentException(
                            "a reading that was searched came to something");
                }
            }
        }

        /** The search of this reading had no answer to give. */
        record NoAnswer() implements ReadingEvidence {}

        /** The request did not ask about this reading ({@link GenerationScope}). */
        record OutOfScope() implements ReadingEvidence {}
    }

    /**
     * What a generation comes to at one point of one line.
     *
     * <p>Stops at the first reading that composed a row, which is what makes this a search: what the
     * two points against a line ask is the same at every reading of it, so a row standing at one
     * reading's point stands at the line and the readings past it are work nobody needs done.
     *
     * <p>Where none of them composed one, every reading is accounted for — including the ones this
     * request never asked about — because what an empty answer is worth is exactly how much of the
     * line was looked at ({@link SearchCoverage}).
     *
     * @param owed     what the line came to at this point, over all of its readings. What decides
     *                 whether there is anything to look for, which is the measurement's answer and
     *                 not the search's
     * @param readings the readings, in the order the module declares them. A reading is a behavior
     *                 at one of its positions: one behavior carrying the type twice is two of them,
     *                 and what a search of each came to is a fact about that position
     * @param held     what each of them holds, asked in that order and only as far as the walk gets
     */
    public static PointResolution resolveAt(ObligationAssessment owed,
                                                  List<Reading> readings,
                                                  Function<Reading, ReadingEvidence> held) {
        if (!owed.worthSearching()) {
            // The measurement's own answer and not a search that came back empty. A point a row
            // already stands at is work that is done, and one nothing measured is not known to be
            // work at all — searched anyway, both would put a specific row in front of an author.
            return new PointResolution.NoSearch(owed.hasRowWitness()
                    ? PointResolution.Cause.A_ROW_ALREADY_STANDS
                    : PointResolution.Cause.NOTHING_MEASURED);
        }
        SequencedMap<Reading, SearchCoverage.ReadingSearch> walked = new LinkedHashMap<>();
        PointResolution.Generated offered = null;
        for (Reading reading : readings) {
            switch (held.apply(reading)) {
                case ReadingEvidence.OutOfScope _ ->
                        walked.put(reading, new SearchCoverage.ReadingSearch.OutOfScope());
                case ReadingEvidence.NoAnswer _ ->
                        walked.put(reading, new SearchCoverage.ReadingSearch.Unavailable());
                case ReadingEvidence.Searched(ItemAssessment.Attempt attempt) -> {
                    switch (attempt) {
                        // A row read back where it was built for. Which reading composed it is
                        // where the row goes, and what a reader asking about one coordinate
                        // compares against — so the position is carried and not the behavior alone.
                        case ItemAssessment.Attempt.Certified made ->
                                { return new PointResolution.Generated(reading, made.row()); }
                        // And one nothing could place, which is a row an author may still want and
                        // is not one this settles the point with. Kept in case no reading of the
                        // line has better, and answered only after every one of them has been
                        // asked: taken as soon as it is met, a reading that could not read its
                        // candidate back would stand in for one that could.
                        case ItemAssessment.Attempt.Unverified made -> {
                            if (offered == null) {
                                offered = new PointResolution.Generated(reading, made.row());
                            }
                        }
                        case ItemAssessment.Attempt.Unresolved(var why, var _, var _) ->
                                walked.put(reading,
                                        new SearchCoverage.ReadingSearch.Attempted(why));
                        // A search that ran with nothing to run against. Said in the words the
                        // generator says it in, as the reading's own outcome: it is a fact about
                        // this run, and one of the reasons a reader may not act on — so a line
                        // holding one of these is not one the model settles.
                        //
                        // Named by the reading it happened at, which is what has a name for the
                        // quantity: a clause names what it is about and a comparison in a body
                        // names nothing, so a subject taken from the point would be a word the
                        // model does not have wherever the line is a body's.
                        //
                        // Put into words here and nowhere earlier. Which reading this is is settled
                        // by the value the walk is keyed on, and what goes into the outcome is a
                        // sentence for whoever reads it — the whole of the line, because half of it
                        // is a word two readings of one line can share.
                        case ItemAssessment.Attempt.Unavailable _ -> walked.put(reading,
                                new SearchCoverage.ReadingSearch.Attempted(
                                        new Generator.UnresolvedCombination(
                                                List.of(reading.target().label()),
                                                Generator.UnresolvedCombination.Reason
                                                        .NOTHING_TO_BUILD_AGAINST)));
                    }
                }
            }
        }
        // A row nothing placed, where no reading of the line placed one. It is what a search came
        // back with and an author asked for a row is owed it; what it is not is the point settled,
        // and nothing here says it is.
        return offered != null ? offered
                : new PointResolution.Unresolved(new SearchCoverage(readings, walked));
    }

    private PointResolver() {}
}
