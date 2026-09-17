package souther.compiler.query;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.Place;
import souther.compiler.partition.CameToNothing;
import souther.compiler.partition.CompositionShortfall;
import souther.compiler.partition.GenerationOutcome;
import souther.compiler.partition.Realization;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * What looking for a row that tells one line from the line beside it came to.
 *
 * <p>Beside the points of the border rather than among them. A row at a point shows the line has
 * not moved; this one shows it has not turned, which takes an input the two lines answer
 * differently at — so it is looked for under a condition the points know nothing about
 * ({@link AnotherLineTheRowsAllow.OneDoes#tellingThemApart}) and comes back as its own answer.
 *
 * <p><b>Where the row stands is kept beside what the search came to, and not read back off the
 * row.</b> A row is written as the values an author would type, and where its positions stand on
 * the quantity the line is drawn on is what the search settled — recovered from the text, it would
 * be a second reading of one thing, free to name a place the search never chose.
 *
 * @param standingAt where the row this composed stands, in the positions the line is drawn on, or
 *                   null where nothing was composed. The place the offered row is at and no other:
 *                   a reader shown one place and handed a row at another has been shown two answers
 * @param searches   what each search made here came to
 */
public record ARowTellingTheLinesApart(Map<NumericTerm, Place> standingAt,
                                       SearchOutcomes searches) {

    public ARowTellingTheLinesApart {
        standingAt = standingAt == null ? null
                : Collections.unmodifiableMap(new LinkedHashMap<>(standingAt));
        if (searches == null) {
            throw new IllegalArgumentException("a search says what it came to");
        }
        // Both ways round, so that neither can be read as the other's absence. A place with no row
        // to hand over is a witness nothing composed; a row with nowhere named is one a reader
        // could be offered under a sentence about somewhere else.
        //
        // Asked of a search that ran, which is what makes this free on the line it is asked of
        // most. Every reading of every border is one of these and almost none of them was searched
        // — a walk of what nothing looked for would be this compiler asking, once per line of every
        // compile, what a search that never happened composed.
        if (searches.ran() && (standingAt == null) == searches.rowToOffer().isPresent()) {
            throw new IllegalArgumentException("a row composed here stands somewhere and a search"
                    + " that composed none stands nowhere: " + standingAt);
        }
        if (!searches.ran() && standingAt != null) {
            throw new IllegalArgumentException("a row standing somewhere that no search composed: "
                    + standingAt);
        }
    }

    /** Nobody asked for a row that tells the two lines apart, which is most lines of most
     *  compiles: one value, because it says nothing about the line it is beside. */
    private static final ARowTellingTheLinesApart NOT_ASKED =
            new ARowTellingTheLinesApart(null, SearchOutcomes.none());

    /** Nobody asked for a row that tells the two lines apart. */
    public static ARowTellingTheLinesApart notAsked() {
        return NOT_ASKED;
    }

    /**
     * What one search of the region came to, with the place it composed at where it composed one.
     *
     * <p>The realization and the outcomes together, because they are one answer. Taken apart, a
     * caller could hand over the place one asking reached beside the row another one composed.
     */
    static ARowTellingTheLinesApart of(Realization.Found offered, SearchOutcomes searches) {
        if (offered == null || searches.rowToOffer().isEmpty()) {
            return new ARowTellingTheLinesApart(null, searches);
        }
        Map<NumericTerm, Place> at = new LinkedHashMap<>();
        offered.fixing().forEach((target, place) -> at.put(target.term(), place));
        return new ARowTellingTheLinesApart(at, searches);
    }

    /**
     * What a generation can say about the line this was looked for at.
     *
     * <p>Read off what happened and never off which kind of finding raised it. A search that
     * composed a row hands the row over; one that ran and came back with nothing says what it met,
     * in the words the search itself came back in; and a line nobody looked at is one this run was
     * not asked about.
     *
     * <p>Reachable from the package and no further. What a generation can do about a finding is
     * read where the dispositions are made, and a report asks the reading itself — handed this, a
     * report would reach every word a generation has for a finding through a value it holds for
     * another reason.
     */
    GenerationOutcome outcome() {
        if (searches.rowToOffer().isPresent()) {
            return new GenerationOutcome.Generated(
                    List.of(searches.rowToOffer().orElseThrow().row()));
        }
        List<CameToNothing> why = new ArrayList<>();
        for (ItemAssessment.Attempt attempt : searches.each()) {
            CameToNothing came = cameToNothing(attempt);
            if (came != null) {
                why.add(came);
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
