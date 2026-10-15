package souther.compiler.query;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.NumericTerms;
import souther.compiler.numeric.Place;
import souther.compiler.partition.Border;
import souther.compiler.partition.CameToNothing;
import souther.compiler.partition.CompositionShortfall;
import souther.compiler.partition.GenerationOutcome;
import souther.compiler.partition.QuantityKey;
import souther.compiler.partition.Realization;
import souther.compiler.partition.RealizationTarget;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Set;
import java.util.Map;
import java.util.Optional;

/**
 * What looking for a row that tells this line from the line beside it came to, at each reading of
 * the line.
 *
 * <p>Beside the points of the border rather than among them. A row at a point shows the line has
 * not moved; this one shows it has not turned, which takes an input the two lines answer
 * differently at — so it is looked for under a condition the points know nothing about
 * ({@link AnotherLineTheRowsAllow.Stands#onTheRefusedSide},
 * {@link AnotherLineTheRowsAllow.Stands#onTheKeptSide}) and comes back as its own answer.
 *
 * <p><b>One answer per line of the family standing, at each reading.</b> A row ruling one of them
 * out need not rule out another, so each is looked for on its own and kept under the line it is for
 * ({@link AtOneReading#direction}).
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
     * What one reading's search for a row ruling out one line of the family came to, on one side of
     * the model's line, and the input it composed its row at.
     *
     * <p>One entry per side searched: a row the model refuses within reach of the rows it keeps, and
     * a row it keeps at or past the rows it refuses ({@link AnotherLineTheRowsAllow.Stands}). Each is
     * kept whatever the other came to, so a line nothing was composed for says what was tried on
     * both sides, and a line with a candidate on each hands both to the offering.
     *
     * @param reading    the line as that reading met it, which is what says at which positions
     *                   {@code composedAt} is written and where a row is read back
     * @param direction  the line of the family the row is for
     * @param composedAt the input this search composed a row at, in the positions the line is drawn
     *                   on at this reading, or null where nothing was composed. What the realizer
     *                   asked for, which is what the row was built from — and so the one thing
     *                   there is to name for a row nothing read back
     * @param searches   what each search made at this reading came to
     */
    public record AtOneReading(Border reading, QuantityKey direction,
                               Map<NumericTerm, Place> composedAt, SearchOutcomes searches) {

        public AtOneReading {
            composedAt = composedAt == null ? null
                    : Collections.unmodifiableMap(new LinkedHashMap<>(composedAt));
            if (reading == null || direction == null || searches == null) {
                throw new IllegalArgumentException(
                        "a search is of a line against a line beside it, and says what it came to: "
                                + reading + " " + direction);
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
     * One reading's search for one line of the family, with the place it composed at where it
     * composed one.
     *
     * <p>The realization and the outcomes together, because they are one answer. Taken apart, a
     * caller could hand over the place one asking reached beside the row another one composed.
     */
    static AtOneReading of(Border reading, QuantityKey direction, Realization.Found composed,
                           SearchOutcomes searches) {
        if (composed == null || searches.rowToOffer().isEmpty()) {
            return new AtOneReading(reading, direction, null, searches);
        }
        Map<NumericTerm, Place> byTerm = new HashMap<>();
        composed.fixing().forEach((target, place) -> {
            switch (target) {
                case RealizationTarget.OfANumber number -> byTerm.put(number.term(), place);
                // How many elements meet a statement, or that they meet one together, is no number
                // of the row, so there is no term to say the row was composed at it; the row's
                // elements say it.
                case RealizationTarget.ACount _, RealizationTarget.ElementsMeetingTogether _ -> { }
            }
        });
        // A linked map answers in the order it was filled, so it is filled in the terms' own order
        // and not in the order the fixing happened to be walked.
        Map<NumericTerm, Place> at = new LinkedHashMap<>();
        for (Map.Entry<NumericTerm, Place> each : NumericTerms.entriesInOrder(byTerm)) {
            at.put(each.getKey(), each.getValue());
        }
        return new AtOneReading(reading, direction, at, searches);
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
     * Every search for a row ruling out {@code direction} that composed one, at every reading and on
     * either side of the line, in the order they were made.
     *
     * <p><b>Candidates and never what a person is handed.</b> Which row goes out for this line is
     * settled two stages later — every offered row is read back and asked what it would answer, and
     * a row whose going costs the offering nothing goes — so one candidate may end up answering this
     * line and the rest be dropped. What is offered is the offering's answer
     * ({@link Offering#shownAt}). Narrowed to one here, the choice would be made before the row was
     * read back: a candidate that comes back unread or settles nothing would stand where another
     * that does was never offered.
     */
    public List<AtOneReading> composed(QuantityKey direction) {
        return each.stream()
                .filter(one -> one.direction().equals(direction) && one.composed().isPresent())
                .toList();
    }

    /**
     * What a generation can say about one line of the family this was looked for against.
     *
     * <p>Read off what happened and never off which kind of finding raised it. Searches that
     * composed a row hand every one of those rows over; searches that ran and came back with nothing
     * say what they met, in the words the searches themselves came back in; and a line nobody looked
     * at is one this run was not asked about.
     *
     * <p>Over every reading and both sides, because a search that composed none has still said
     * something about its own region. A reader asking what would let the search go further is owed
     * what each of them met.
     *
     * <p>Reachable from the package and no further. What a generation can do about a finding is
     * read where the dispositions are made, and a report asks the reading itself — handed this, a
     * report would reach every word a generation has for a finding through a value it holds for
     * another reason.
     */
    GenerationOutcome outcome(QuantityKey direction) {
        List<AtOneReading> made = composed(direction);
        if (!made.isEmpty()) {
            return new GenerationOutcome.Generated(made.stream()
                    .map(one -> one.composed().orElseThrow().row()).toList());
        }
        List<CameToNothing> why = new ArrayList<>();
        for (AtOneReading one : each) {
            if (!one.direction().equals(direction)) {
                continue;
            }
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
    static CameToNothing cameToNothing(ItemAssessment.Attempt attempt) {
        return switch (attempt) {
            // A row was composed, which is the answer above rather than a search that came to
            // nothing. And nothing could be built to look with, which is not the line's answer
            // either: no search ran, so none of them said anything about it.
            case ItemAssessment.Attempt.Certified _, ItemAssessment.Attempt.Unverified _,
                 ItemAssessment.Attempt.Unavailable _ -> null;
            case ItemAssessment.Attempt.Unresolved it -> CameToNothing.metNothing(it.why());
            case ItemAssessment.Attempt.Stopped it -> new CameToNothing(it.why(),
                    CompositionShortfall.of(it.stoppedBy().written(), it.notAllOf().written(),
                            it.unheld().written()), Set.of());
            case ItemAssessment.Attempt.Unexhausted it -> new CameToNothing(it.why(),
                    CompositionShortfall.of(List.of(), it.notAllOf().written(),
                            it.unheld().written()), Set.of());
            // What limited it cut the plan it ran over short, which it did not meet on the way;
            // what it wrote some of and could not hold, it did.
            case ItemAssessment.Attempt.Limited it -> new CameToNothing(it.why(),
                    CompositionShortfall.of(List.of(), it.notAllOf().written(),
                            it.unheld().written()), Set.copyOf(it.limitedBy().written()));
            case ItemAssessment.Attempt.Unplanned it -> new CameToNothing(it.why(),
                    CompositionShortfall.NONE, Set.copyOf(it.limitedBy().written()));
        };
    }
}
