package souther.compiler.query;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.NumericTerms;
import souther.compiler.numeric.Place;
import souther.compiler.partition.Border;
import souther.compiler.partition.CameToNothing;
import souther.compiler.partition.CompositionShortfall;
import souther.compiler.partition.GenerationOutcome;
import souther.compiler.partition.Realization;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
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
 * its own, and the input a row is composed at is written in the positions <em>that</em> reading
 * names. Held as one answer for the line, a row composed under one reading arrives beside another
 * reading's line — and its input is then read at positions that reading does not have, which is a
 * row offered under a sentence naming nowhere.
 *
 * <p><b>The input a search composed at is kept beside what it came to, and not read back off the
 * row.</b> A row is written as the values an author would type, and what the realizer asked for is
 * what the row was built from — recovered from the text, it would be a second reading of one
 * thing, free to name an input the search never chose. It is not where the row was seen standing
 * either: nothing may have read it back, and it is offered all the same.
 *
 * @param each one entry per reading that was asked, in the order the readings were walked
 */
public record ARowTellingTheLinesApart(List<AtOneReading> each) {

    public ARowTellingTheLinesApart {
        each = List.copyOf(each);
    }

    /**
     * What one reading's search came to, and the input it composed its row at.
     *
     * @param reading    the line as that reading met it, which is what says at which positions
     *                   {@code composedAt} is written and where a row is read back
     * @param composedAt the input this search composed a row at, in the positions the line is drawn
     *                   on at this reading, or null where nothing was composed. What the realizer
     *                   asked for, which is what the row was built from — and so the one thing
     *                   there is to name for a row nothing read back
     * @param searches   what each search made at this reading came to
     */
    public record AtOneReading(Border reading, Map<NumericTerm, Place> composedAt,
                               SearchOutcomes searches) {

        public AtOneReading {
            composedAt = composedAt == null ? null
                    : Collections.unmodifiableMap(new LinkedHashMap<>(composedAt));
            if (reading == null || searches == null) {
                throw new IllegalArgumentException(
                        "a search is of a line, and says what it came to: " + reading);
            }
            // Both ways round, so that neither can be read as the other's absence. An input with no
            // row built from it is a place nothing composed; a row with nowhere named is one a
            // reader could be shown under a sentence about somewhere else.
            if ((composedAt == null) == searches.rowToOffer().isPresent()) {
                throw new IllegalArgumentException("a row composed here was composed somewhere and"
                        + " a search that composed none was composed nowhere: " + composedAt);
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
    static ARowTellingTheLinesApart of(Border reading, Realization.Found composed,
                                       SearchOutcomes searches) {
        if (composed == null || searches.rowToOffer().isEmpty()) {
            return new ARowTellingTheLinesApart(
                    List.of(new AtOneReading(reading, null, searches)));
        }
        Map<NumericTerm, Place> byTerm = new HashMap<>();
        composed.fixing().forEach((target, place) -> byTerm.put(target.term(), place));
        // A linked map answers in the order it was filled, so it is filled in the terms' own order
        // and not in the order the fixing happened to be walked.
        Map<NumericTerm, Place> at = new LinkedHashMap<>();
        for (Map.Entry<NumericTerm, Place> each : NumericTerms.entriesInOrder(byTerm)) {
            at.put(each.getKey(), each.getValue());
        }
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
     * The first reading whose search composed a row, where one did.
     *
     * <p><b>A candidate and never what a person is handed.</b> Which row goes out for this line is
     * settled two stages later — every offered row is asked what it would answer, and a row whose
     * going costs the offering nothing goes — so another row may end up answering this line and
     * this one be dropped. What is offered is the offering's answer ({@link Offering#shownAt}), and
     * a reader taking this for it is reading a choice made before the one that decides.
     *
     * <p>The first, in the order the readings were walked, so that an edit elsewhere in the body
     * does not move which candidate this is. What every reading came to is still here for whoever
     * asks.
     */
    public Optional<AtOneReading> firstComposed() {
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
        Optional<AtOneReading> made = firstComposed();
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
