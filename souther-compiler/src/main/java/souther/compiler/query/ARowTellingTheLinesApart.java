package souther.compiler.query;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.Place;
import souther.compiler.partition.Border;
import souther.compiler.partition.CameToNothing;
import souther.compiler.partition.CompositionShortfall;
import souther.compiler.partition.GenerationOutcome;
import souther.compiler.partition.Realization;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * What looking for a row that tells this line from the line beside it came to, at each reading of
 * the line.
 *
 * <p>Beside the points of the border rather than among them. A row at a point shows the line has
 * not moved; this one shows it has not turned, which takes an input the two lines answer
 * differently at — so it is looked for under a condition the points know nothing about
 * ({@link AnotherLineTheRowsAllow.OneDoes#tellingThemApart}) and comes back as its own answer.
 *
 * <p><b>One answer per reading, and never one for the line.</b> Which lines the rows leave standing
 * beside this one is about the line and the rows, and two readings of it agree or one of them is
 * wrong — that is {@link AnotherLineTheRowsAllow}, and it is held once. Where a row may be composed
 * is not like that: a reading is reached under its caller's own conditions, so each has a region of
 * its own, and the place a row stands is written in the positions <em>that</em> reading names. Held
 * as one answer for the line, a row composed under one reading arrives beside another reading's
 * line — and the place it stands is then read at positions that reading does not have, which is a
 * row offered under a sentence naming nowhere.
 *
 * <p><b>Where the row stands is kept beside what the search came to, and not read back off the
 * row.</b> A row is written as the values an author would type, and where its positions stand on
 * the quantity the line is drawn on is what the search settled — recovered from the text, it would
 * be a second reading of one thing, free to name a place the search never chose.
 *
 * @param each one entry per reading that was asked, in the order the readings were walked
 */
public record ARowTellingTheLinesApart(List<AtOneReading> each) {

    public ARowTellingTheLinesApart {
        each = List.copyOf(each);
    }

    /**
     * What one reading's search came to, and where the row it hands over stands.
     *
     * @param reading    the line as that reading met it, which is what says at which positions
     *                   {@code standingAt} is written and where a row is read back
     * @param standingAt where the row this composed stands, in the positions the line is drawn on
     *                   at this reading, or null where nothing was composed. The place the offered
     *                   row is at and no other: a reader shown one place and handed a row at
     *                   another has been shown two answers
     * @param searches   what each search made at this reading came to
     */
    public record AtOneReading(Border reading, Map<NumericTerm, Place> standingAt,
                               SearchOutcomes searches) {

        public AtOneReading {
            standingAt = standingAt == null ? null
                    : Collections.unmodifiableMap(new LinkedHashMap<>(standingAt));
            if (reading == null || searches == null) {
                throw new IllegalArgumentException(
                        "a search is of a line, and says what it came to: " + reading);
            }
            // Both ways round, so that neither can be read as the other's absence. A place with no
            // row to hand over is a witness nothing composed; a row with nowhere named is one a
            // reader could be offered under a sentence about somewhere else.
            if ((standingAt == null) == searches.rowToOffer().isPresent()) {
                throw new IllegalArgumentException("a row composed here stands somewhere and a"
                        + " search that composed none stands nowhere: " + standingAt);
            }
        }

        /** The search of this reading that composed a row, where one did. */
        Optional<ItemAssessment.Attempt.Built> composed() {
            return searches.rowToOffer();
        }
    }

    /** Nobody asked for a row that tells the two lines apart, which is most lines of most
     *  compiles: one value, because it says nothing about the line it is beside. */
    private static final ARowTellingTheLinesApart NOT_ASKED =
            new ARowTellingTheLinesApart(List.of());

    /** Nobody asked for a row that tells the two lines apart. */
    public static ARowTellingTheLinesApart notAsked() {
        return NOT_ASKED;
    }

    /**
     * One reading's search, with the place it composed at where it composed one.
     *
     * <p>The realization and the outcomes together, because they are one answer. Taken apart, a
     * caller could hand over the place one asking reached beside the row another one composed.
     */
    static ARowTellingTheLinesApart of(Border reading, Realization.Found offered,
                                       SearchOutcomes searches) {
        if (offered == null || searches.rowToOffer().isEmpty()) {
            return new ARowTellingTheLinesApart(
                    List.of(new AtOneReading(reading, null, searches)));
        }
        Map<NumericTerm, Place> at = new LinkedHashMap<>();
        offered.fixing().forEach((target, place) -> at.put(target.term(), place));
        return new ARowTellingTheLinesApart(List.of(new AtOneReading(reading, at, searches)));
    }

    /**
     * These readings and those, which is what two readings of one line come to.
     *
     * <p>Kept apart rather than chosen between. Two readings searched two regions and neither
     * stands for the other: one that composed nowhere says nothing about the other's region, and
     * the row either composed is written in its own reading's positions. Folded into one, a row
     * would travel beside a line it was not composed at.
     */
    ARowTellingTheLinesApart and(ARowTellingTheLinesApart other) {
        if (other.each.isEmpty()) {
            return this;
        }
        if (each.isEmpty()) {
            return other;
        }
        List<AtOneReading> both = new ArrayList<>(each);
        both.addAll(other.each);
        return new ARowTellingTheLinesApart(both);
    }

    /**
     * The reading whose row a person is offered, where one was composed.
     *
     * <p>The first that composed one, which is a choice about what to show and takes nothing away:
     * what every reading came to is still here for whoever asks. In the order the readings were
     * walked, so that an edit elsewhere in the body does not move which row is offered.
     */
    public Optional<AtOneReading> offered() {
        return each.stream().filter(one -> one.composed().isPresent()).findFirst();
    }

    /**
     * What a generation can say about the line this was looked for at.
     *
     * <p>Read off what happened and never off which kind of finding raised it. A reading that
     * composed a row hands the row over; readings that ran and came back with nothing say what they
     * met, in the words the searches themselves came back in; and a line nobody looked at is one
     * this run was not asked about.
     *
     * <p>Over every reading, because one row settles the line and a reading that composed none has
     * still said something about its own region. A reader asking what would let the search go
     * further is owed what each of them met.
     *
     * <p>Reachable from the package and no further. What a generation can do about a finding is
     * read where the dispositions are made, and a report asks the reading itself — handed this, a
     * report would reach every word a generation has for a finding through a value it holds for
     * another reason.
     */
    GenerationOutcome outcome() {
        Optional<AtOneReading> made = offered();
        if (made.isPresent()) {
            return new GenerationOutcome.Generated(
                    List.of(made.orElseThrow().composed().orElseThrow().row()));
        }
        List<CameToNothing> why = new ArrayList<>();
        for (AtOneReading one : each) {
            for (ItemAssessment.Attempt attempt : one.searches().each()) {
                CameToNothing came = cameToNothing(attempt);
                if (came != null) {
                    why.add(came);
                }
            }
        }
        return why.isEmpty()
                // Nothing was looked for, or nothing could be: a search this compiler had no way
                // to run says that about itself and says nothing about the line.
                ? new GenerationOutcome.NotApplicable(
                        GenerationOutcome.NotApplicable.Reason.NOTHING_WAS_MEASURED)
                : new GenerationOutcome.CannotGenerate(why);
    }

    /**
     * What one search that composed no row came back with, or null where it composed one or never
     * ran.
     *
     * <p>The word and what the search met of this compiler's, which travel together: a figure
     * dropped here reaches an author as work to do with nothing in it they could act on.
     *
     * <p>Exhaustive with no {@code default}, so an outcome added later is answered here rather than
     * inheriting whichever answer sat under a catch-all.
     */
    private static CameToNothing cameToNothing(ItemAssessment.Attempt attempt) {
        return switch (attempt) {
            // A row was composed, which is the answer above rather than a search that came to
            // nothing. And nothing could be built to look with, which is not the line's answer
            // either: no search ran, so none of them said anything about it.
            case ItemAssessment.Attempt.Certified _, ItemAssessment.Attempt.Unverified _,
                 ItemAssessment.Attempt.Unavailable _ -> null;
            case ItemAssessment.Attempt.Unresolved it -> CameToNothing.metNothing(it.why());
            case ItemAssessment.Attempt.Stopped it -> new CameToNothing(it.why(),
                    CompositionShortfall.of(it.stoppedBy().written(), it.notAllOf().written()));
            case ItemAssessment.Attempt.Unexhausted it -> new CameToNothing(it.why(),
                    CompositionShortfall.writing(it.notAllOf().written()));
            case ItemAssessment.Attempt.Limited it -> new CameToNothing(it.why(),
                    CompositionShortfall.of(it.limitedBy().written()));
            case ItemAssessment.Attempt.Unplanned it -> new CameToNothing(it.why(),
                    CompositionShortfall.of(it.limitedBy().written()));
        };
    }
}
