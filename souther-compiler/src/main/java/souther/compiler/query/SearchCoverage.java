package souther.compiler.query;

import souther.compiler.partition.CameToNothing;
import souther.compiler.partition.Generator;
import souther.compiler.query.BorderObligationPointAssessment.Reading;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.SequencedMap;

/**
 * What became of every reading of one authored line, when none of them composed a row.
 *
 * <p>Total over the readings the line has, and that is the whole reason it is a value. A search over
 * the readings comes back with a row or with nothing, and what "nothing" is worth turns entirely on
 * how much of the line was looked at: a walk that stopped at the first behavior and a walk that
 * reached the end of every one of them are the same empty answer and are not the same fact. Read off
 * a map of what happened to be searched, the difference is an absence, and an absence is what a
 * reader fills in with whatever it assumes.
 *
 * <p><b>Three states and no fourth.</b> A reading was walked and said something, or the search of it
 * had no answer to give, or the request never asked about it. The first is evidence about the line;
 * the other two are facts about this run and about what was asked, and neither may be read as the
 * line saying anything.
 *
 * <p>Held only where nothing was composed. A run that produced a row stopped at the reading that
 * produced it, so the readings past it were not walked — and a coverage beside a row would have to
 * say something about readings nobody had any reason to look at. Which is also why this being total
 * costs nothing: it is built where the walk reached the end.
 *
 * <p>A reading is a behavior at one of its positions and not a behavior. One behavior can carry the
 * type at more than one position, and what a search of one of them came to is a fact about that
 * position — so a coverage keyed by the behavior holds one of the two answers, chosen by the order
 * the walk took, which is the thing this value exists to refuse.
 *
 * @param readings the readings the line has, in the order the module declares them. Named rather
 *                 than left as whatever the map happens to hold, because it is what the map is
 *                 checked against — the universe is a fact about the line, and a coverage built
 *                 from its own keys could not be short of anything
 * @param came     what became of each of them
 */
public record SearchCoverage(List<Reading> readings, SequencedMap<Reading, ReadingSearch> came) {

    /** What became of one reading. */
    public sealed interface ReadingSearch {

        /**
         * The reading was searched and no row came of it, in the search's own words.
         *
         * <p>The reading's reason and not the line's. What a search of one position came to is a
         * fact about that position — the rules reaching it, the values its decoder took — and a
         * line is what its readings agree about rather than what one of them found.
         *
         * <p>Every search of the reading, held as they came back and never as one of them or as
         * words taken off them. A reading may be searched more than once, and what the searches
         * come to together is their owner's to say ({@link SearchOutcomes#provesInfeasible}): kept
         * as one search's words, the reading would be whichever search the walk took last, and
         * taken down to words, what a search met or was cut short by would be gone from whatever
         * reads them next.
         *
         * @param outcomes every search of the reading, one of which at least ran
         */
        record Attempted(SearchOutcomes outcomes) implements ReadingSearch {

            public Attempted {
                if (outcomes == null || outcomes.each().stream()
                        .allMatch(ItemAssessment.Attempt.Unplanned.class::isInstance)) {
                    throw new IllegalArgumentException("a reading searched is one a search ran at");
                }
            }

            /** Whether every search of the reading showed the rules leave nothing there. */
            public boolean proves() {
                return outcomes.provesInfeasible();
            }

            /**
             * What the searches of {@code reading} that came to nothing came back with, a word once
             * with all it met ({@link CameToNothing#joined}). A search that ran with nothing to run
             * against says so in the words the generator does, named by the reading, which is what
             * has a name for the quantity — a comparison in a body names nothing.
             */
            public List<CameToNothing> came(Reading reading) {
                List<CameToNothing> each = new ArrayList<>();
                for (ItemAssessment.Attempt attempt : outcomes.each()) {
                    if (attempt instanceof ItemAssessment.Attempt.Unavailable) {
                        each.add(CameToNothing.metNothing(new Generator.UnresolvedCombination(
                                List.of(reading.target().label()),
                                Generator.UnresolvedCombination.Reason.NOTHING_TO_BUILD_AGAINST)));
                    } else {
                        CameToNothing came = ARowTellingTheLinesApart.cameToNothing(attempt);
                        if (came != null) {
                            each.add(came);
                        }
                    }
                }
                return CameToNothing.joined(each);
            }
        }

        /**
         * What every search of a reading came to, as the reading's part of a coverage: searched
         * where any search ran at it, and one with no answer to give where none did — a reading
         * nobody looked at taking part in what the readings establish would be this compiler's
         * shortfall read as the model's answer.
         */
        static ReadingSearch of(SearchOutcomes outcomes) {
            return outcomes.each().stream()
                    .allMatch(ItemAssessment.Attempt.Unplanned.class::isInstance)
                    ? new Unavailable() : new Attempted(outcomes);
        }

        /**
         * The search of this reading had no answer to give.
         *
         * <p>A fact about this run. Nothing about the point was established here, so a conclusion
         * about the line counting this reading as one that refused it would be reading our own
         * shortfall as the model's answer.
         *
         * <p>Not where the search answered and the line was not in it. A reading the search covered
         * and holds no occurrence of is the search and the debt disagreeing about which lines this
         * behavior meets, which is a defect here rather than a state of the evidence.
         */
        record Unavailable() implements ReadingSearch {}

        /** The request did not ask about this reading ({@link GenerationScope}). Nothing was spent
         *  on it and nothing is known about it. */
        record OutOfScope() implements ReadingSearch {}
    }

    public SearchCoverage {
        readings = List.copyOf(readings);
        if (readings.isEmpty()) {
            // A line is what its readings came to and a line with none is not one. Allowed, a walk
            // over nothing would come back having proven whatever it was asked to prove.
            throw new IllegalArgumentException("a line nothing reads is not a line");
        }
        came = java.util.Collections.unmodifiableSequencedMap(new LinkedHashMap<>(came));
        // In order and not merely the same set. What the map is ordered by is the order the module
        // declares the readings in, which is what makes "the first that composed a row" one answer
        // rather than whichever the walk happened to reach — checked as a set, that half of the
        // contract was a convention. A repeated reading is refused by the same comparison.
        if (!List.copyOf(came.keySet()).equals(readings)) {
            throw new IllegalStateException(
                    "a coverage of a line that is not what its readings are, in their order: "
                            + readings + " against " + came.keySet());
        }
    }

    /**
     * Whether every reading of the line was walked to the end.
     *
     * <p>The one gate a terminal answer about the line passes. Never the shape of the request: a
     * line one behavior carries is walked entirely by a request about that behavior, and a rule
     * that asked which scope this was would refuse it the answer its own evidence supports.
     */
    public boolean walkedEveryReading() {
        return came.values().stream().allMatch(ReadingSearch.Attempted.class::isInstance);
    }

    /** What each reading that was walked came to, in the order they were walked. */
    public List<Generator.UnresolvedCombination> attempted() {
        List<Generator.UnresolvedCombination> out = new ArrayList<>();
        came.forEach((reading, each) -> {
            if (each instanceof ReadingSearch.Attempted searched) {
                searched.came(reading).forEach(it -> out.add(it.why()));
            }
        });
        return List.copyOf(out);
    }

    /**
     * Whether this settles that no row can be written at the line.
     *
     * <p>False is the readings not settling it, and never the model leaving a value there. Most of
     * what a search comes back with is this compiler falling short — a value it could not build, a
     * walk that stopped — and one reading of one position proving there is nothing at the point
     * proves it of the position, whose bounds every other rule reaching it takes part in. So the
     * claim a reader may act on (ADR-0091) is released here and nowhere else, and only where every
     * reading of the line was walked to the end and every one of them proves it.
     *
     * <p>A boolean and not the reason. Two of the reasons prove it and they are about different
     * things, so an answer that named one would be picking which reading stands for the line — and
     * a reader wanting what each of them said has them all in {@link #attempted}.
     *
     * <p>Asked of what each search's outcome answered, which is where that decision lives
     * ({@link ItemAssessment.Attempt#proves}), and never of its word alone.
     */
    public boolean provesTheLineCannotBeWritten() {
        return walkedEveryReading() && came.values().stream().allMatch(each ->
                each instanceof ReadingSearch.Attempted searched && searched.proves());
    }
}
