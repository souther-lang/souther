package souther.compiler.query;

import souther.compiler.partition.BorderObligationPoint;
import souther.compiler.partition.GenerationOutcome;
import souther.compiler.partition.Generator;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.SequencedMap;

/**
 * The rows a module's declarations are owed: one answer per point of each authored line.
 *
 * <p><b>The authority on how many points a line is resolved at, and not on how many rows go out.</b>
 * A point is one piece of work however many positions carry the type, and that is a rule about what
 * is owed rather than about how a block is laid out — so it is settled here, where the search is
 * resolved, and every reader below is a projection of this map. Left to the block, one authored line
 * came out as up to four answers because each reading composed its own (issue #1076), and a block
 * written another way would have brought it back.
 *
 * <p>How many rows a person is offered is another count and is made further down: two points can be
 * answered by one row, and a block offers a row once per set of inputs ({@code GeneratedRows}). One
 * resolution per point does not mean one row per point.
 *
 * <p>In the order the lines were read, so that what a block prints is read against the one before
 * it.
 *
 * @param scope    which readings the request was about, which is also what settles the lines it is
 *                 about: a line no reading of the request's carries is not a question this was put.
 *                 Carried rather than left to each reader, because a reader deciding it a second
 *                 time is a reader that can decide it differently
 * @param resolved one answer per point of each line the scope admits
 */
public record BorderAccount(GenerationScope scope,
        SequencedMap<BorderObligationPoint, Answer> resolved) {

    /**
     * What a generation came to at one point, and what that point asks of a row.
     *
     * <p>The words beside the answer because every reader of the answer needs them, and they are the
     * declaration's rather than any reading's: a reading names the position it met the line at, and
     * a subject taken from one would say the row is about that position. Worked out where the search
     * was, so that a reader with the answer never has to go back to the line for what it was about.
     *
     * @param owedBy who owes a row here — the declarations that drew the line, or the body that
     *               did. Where a note about it goes, and the whole of what tells two lines apart
     *               that a reader would otherwise see written the same way: what a newtype wraps is
     *               spelled {@code value} in every declaration. Kept as the subject rather than as
     *               its name, because what it is decides where a row is offered as well as what the
     *               note says ({@link #rowsByCarrier})
     */
    public record Answer(String said, FindingSubject owedBy, PointResolution resolution) {

        public Answer {
            if (said == null || owedBy == null || resolution == null) {
                throw new IllegalArgumentException("an answer is to something, and is an answer");
            }
        }

        /** Whether a row here is the body's own to write, which is what a block offers first. */
        boolean owedByTheBody() {
            return owedBy instanceof FindingSubject.OfABehavior;
        }
    }

    public BorderAccount {
        resolved = java.util.Collections.unmodifiableSequencedMap(new LinkedHashMap<>(resolved));
    }

    /**
     * The rows themselves, under the behavior each was composed for.
     *
     * <p>Where a row goes and not who owes it. A row is written in one behavior's terms, so it
     * belongs in that behavior's block; what it settles is the declaration's line, which is what the
     * words over it say.
     *
     * <p>A projection and nothing more — no row is chosen here and none is dropped. Which reading
     * composed the row was settled by the search, and a renderer that grouped differently would
     * still be handed the same row for each point. Two points answered by one row are two entries
     * here and one row where the block is written, which is where that count is made.
     *
     * <p><b>The body's own lines first, and the declarations' after them.</b> An order, because what
     * is offered turns on one: a reduction keeps the earlier of two rows that answer the same
     * thing, so that an edit further down the model does not move what is offered above it
     * ({@link Settlements#keeping}). That order was the two searches being asked in turn, and it
     * survives the two becoming one account here rather than being left to the order the points
     * happened to be gathered in — which is a fact about a walk and about nothing a reader can see.
     *
     * <p>Which is why it is here and not in what the account holds. What is owed and what became of
     * it are the same whichever way they are listed; this is the listing.
     */
    public SequencedMap<String, List<Generator.GeneratedRow>> rowsByCarrier() {
        SequencedMap<String, List<Generator.GeneratedRow>> out = new LinkedHashMap<>();
        take(out, true);
        take(out, false);
        return java.util.Collections.unmodifiableSequencedMap(out);
    }

    /** The rows of the points the body owes, or of the rest, under the behavior that composed each. */
    private void take(SequencedMap<String, List<Generator.GeneratedRow>> out, boolean theBodys) {
        resolved.forEach((_, answer) -> {
            if (answer.owedByTheBody() == theBodys
                    && answer.resolution() instanceof PointResolution.Generated(var by, var row)) {
                out.computeIfAbsent(by, _ -> new ArrayList<>()).add(row);
            }
        });
    }

    /**
     * What a block may say about each line nothing composed a row for, whether or not a finding
     * names the point.
     *
     * <p>Beside {@link #dispositions} and not through it. A finding stands where the point was
     * measured and missed <em>and</em> something showed a row can be written there, so a line the
     * search failed at with nothing yet promising a row raises none — and a block that said only
     * what the findings said would go quiet about work it had just tried and failed to do.
     *
     * <p><b>The conclusion is drawn here and handed over, not left to be drawn again.</b> What a
     * search of one reading came to is a fact about that reading; that no row can be written at the
     * line is a claim about every one of them, and which of the two a reader is holding was
     * something the reader had to know. Handed on as a flat list of what the readings said, the one
     * sentence a reader may act on (ADR-0091) was printed under the declaration's own name for a
     * line one reading had merely refused.
     */
    public SequencedMap<BorderObligationPoint, Unmet> unmet() {
        SequencedMap<BorderObligationPoint, Unmet> out = new LinkedHashMap<>();
        resolved.forEach((at, answer) -> {
            if (answer.resolution() instanceof PointResolution.Unresolved _) {
                out.put(at, unmet(answer));
            }
        });
        return java.util.Collections.unmodifiableSequencedMap(out);
    }

    /**
     * What is left to say about one point nothing composed a row for.
     *
     * <p>The one place the gate is passed. Every reader of this holds an answer whose shape says
     * what it may be spelled as, so none of them carries a copy of the rule.
     *
     * <p>Reachable from the package for the same reason: what it decides is held directly, rather
     * than through a rendering of it or a compilation arranged to produce the evidence.
     *
     * <p>The coverage is read off the answer rather than handed in beside it. Taken as a second
     * argument, a caller could pass one walk's evidence beside another walk's answer, and the two
     * would have to be kept in step by whoever called.
     */
    static Unmet unmet(Answer answer) {
        if (!(answer.resolution() instanceof PointResolution.Unresolved(var coverage))) {
            throw new IllegalStateException(
                    "what is left to say about a point a row was composed at, or none was looked"
                            + " for at: " + answer.resolution());
        }
        List<At> came = new ArrayList<>();
        coverage.came().forEach((reading, search) -> {
            switch (search) {
                case SearchCoverage.ReadingSearch.Attempted(var why) ->
                        came.add(new At.Searched(reading, why));
                // Kept and not skipped. A reading this run could not search is something that
                // happened to it, and dropping it here would put back the absence the coverage was
                // made total to take out: a reader would see the readings that answered and no sign
                // that another was asked.
                case SearchCoverage.ReadingSearch.Unavailable _ ->
                        came.add(new At.CouldNotBeSearched(reading));
                // The request never asked about it, so nothing was spent on it and there is
                // nothing to report. Its absence from this is what the scope already says.
                case SearchCoverage.ReadingSearch.OutOfScope _ -> { }
            }
        });
        String owedBy = answer.owedBy().named();
        if (came.isEmpty()) {
            return new Unmet.NothingWasSearched(owedBy, answer.said());
        }
        return coverage.provesTheLineCannotBeWritten()
                ? new Unmet.TheLineCannotBeWritten(owedBy, answer.said(), List.copyOf(came))
                : new Unmet.WhatTheReadingsCameTo(owedBy, answer.said(), List.copyOf(came));
    }

    /**
     * What one reading of the line came to, and which reading it was.
     *
     * <p>Two shapes, because a search that ran and a search that could not be made are different
     * news and only the first says anything about the point. Held as one with a reason that might
     * be missing, the second reads as a search that came back empty.
     */
    public sealed interface At {

        /** Which reading this is about. */
        BorderObligationPointAssessment.Reading reading();

        /** The search ran and no row came of it, in its own words. */
        record Searched(BorderObligationPointAssessment.Reading reading,
                        Generator.UnresolvedCombination why) implements At {}

        /** The search of this reading had no answer to give, so nothing was looked for at it. A
         *  fact about this run, and never about the point. */
        record CouldNotBeSearched(BorderObligationPointAssessment.Reading reading) implements At {}
    }

    /**
     * What is left to say about a line no row was composed at.
     *
     * <p>Three shapes because they license three different sentences, and a reader that had one
     * shape for all of them would be choosing which. Only the first is about the line.
     */
    public sealed interface Unmet {

        /** The declaration that drew the line. */
        String owedBy();

        /** What the point asks of a row, in the words the declaration wrote it in. */
        String said();

        /**
         * Every reading was walked and every one of them proves there is nothing at the point.
         *
         * <p>The one arm a sentence about the line may be written from. What each reading said is
         * kept beside it rather than folded, because they prove it of different positions.
         *
         * <p>Every entry here is a search that ran: the gate this arm passes is every reading having
         * been walked, so a reading this run could not search cannot be in one.
         */
        record TheLineCannotBeWritten(String owedBy, String said, List<At> proving)
                implements Unmet {}

        /**
         * What the readings came to, which is not a claim about the line.
         *
         * <p>Some of them may say the rules leave nothing at their own position — and that is what
         * it says: of that position, whose bounds every other rule reaching it takes part in. Said
         * of the line, a reader is told a row cannot be written where another reading writes one.
         */
        record WhatTheReadingsCameTo(String owedBy, String said, List<At> came) implements Unmet {}

        /** The request walked no reading of it, so nothing was looked for and nothing is known. */
        record NothingWasSearched(String owedBy, String said) implements Unmet {}
    }

    /**
     * What the generator can do about each finding a declaration's line raised.
     *
     * <p>Read off the same resolutions the rows are, so the two cannot disagree. Asked separately,
     * a block printed a row two lines above a sentence saying nothing offers one.
     *
     * <p>Findings whose point this holds no resolution for, and findings at a point the resolution
     * says needed no search, are both refused rather than skipped. A finding stands where the point
     * was measured and missed and something showed a row can be written there; a resolution saying a
     * row already stands at it, or that nothing measured it, is the two disagreeing about one point —
     * and a walk that quietly passed over such a finding would leave an author told nothing about it
     * while the rows above read as though they filled everything (issue #1062).
     */
    public List<Adequacy.GenerationDisposition> dispositions(List<Adequacy.Finding> findings) {
        // Which lines this request was about, read off what it answered rather than asked of the
        // scope again. The domain was settled where the search was; re-derived here, the resolver
        // and the projection are two authorities on one question and are free to answer it
        // differently the day either moves.
        java.util.Set<souther.compiler.partition.BorderObligationId> asked = resolved.keySet()
                .stream().map(BorderObligationPoint::line)
                .collect(java.util.stream.Collectors.toUnmodifiableSet());
        List<Adequacy.GenerationDisposition> out = new ArrayList<>();
        for (Adequacy.Finding finding : findings) {
            if (!(finding.about() instanceof About.APointOfADeclaredBorder(var debt))) {
                continue;
            }
            if (!asked.contains(debt.id())) {
                continue;   // a line this request was not put a question about
            }
            BorderObligationPoint at = debt.point();
            out.add(new Adequacy.GenerationDisposition(finding,
                    java.util.Optional.of(new OfferItem.APointOfALine(at)), outcomeAt(at)));
        }
        return List.copyOf(out);
    }

    /**
     * What a generation can do about the point at {@code at}.
     *
     * <p>The one reading of a resolution as an outcome, whoever owes the point. A row a search
     * composed is the row that answers it; a search that composed none says what every reading of
     * the point came to; and a point the measurement says needs nothing looked for is not one a
     * finding stands at.
     *
     * <p>Refused rather than answered where this holds no resolution, or holds one saying no search
     * was called for. A finding stands where the point was measured and missed and something showed
     * a row can be written there, so either is the finding and the account disagreeing about one
     * point — and a caller that quietly passed over it would leave an author told nothing while the
     * rows beside it read as though they filled everything.
     */
    GenerationOutcome outcomeAt(BorderObligationPoint at) {
        Answer answer = resolved.get(at);
        if (answer == null) {
            throw new IllegalStateException(
                    "a finding about a line this generation was asked about and holds no answer"
                            + " for: " + at);
        }
        return switch (answer.resolution()) {
            case PointResolution.Generated(var _, var row) ->
                    new GenerationOutcome.Generated(List.of(row));
            case PointResolution.Unresolved _ -> cannot(unmet(answer));
            case PointResolution.NoSearch(var cause) -> throw new IllegalStateException(
                    "a finding at a point nothing was looked for at, which the measurement says"
                            + " needs nothing looked for: " + at + " " + cause);
        };
    }

    /** Whether this account holds an answer at {@code at}, for a caller that has findings from
     *  beyond what this request asked about. */
    boolean holds(BorderObligationPoint at) {
        return resolved.containsKey(at);
    }

    /**
     * What a walk that composed nothing says, as an outcome beside a finding.
     *
     * <p>Read off the same answer the block's sentences are, so the two cannot come apart. Every
     * reading that was walked, and never the weakest or the first of them: they come to different
     * things and none of those orders against the rest, so a single one carried here would be
     * carrying the order the walk happened to take.
     *
     * <p>Where the walk searched no reading at all there is nothing any of them said, and the run
     * says that about itself. Read as a search that came back empty, a request that could not look
     * at the one reading it was about would have reported it as the line refusing a row.
     */
    private static GenerationOutcome.CannotGenerate cannot(Unmet unmet) {
        List<Generator.UnresolvedCombination> said = switch (unmet) {
            case Unmet.TheLineCannotBeWritten(var _, var _, var proving) -> whys(proving);
            case Unmet.WhatTheReadingsCameTo(var _, var _, var came) -> whys(came);
            case Unmet.NothingWasSearched(var _, var _) -> List.of();
        };
        // Where no reading was searched there is nothing any of them said, and the run says that
        // about itself. Read as a search that came back empty, a request that could look at none of
        // the readings it was about would have reported it as the line refusing a row.
        return new GenerationOutcome.CannotGenerate(said.isEmpty()
                ? List.of(new Generator.UnresolvedCombination(List.of(unmet.said()),
                        Generator.UnresolvedCombination.Reason
                                .NO_READING_OF_THE_LINE_COULD_BE_SEARCHED))
                : said);
    }

    /** What the readings that were searched came to, which is what a reason can be read from. */
    private static List<Generator.UnresolvedCombination> whys(List<At> came) {
        return came.stream()
                .filter(At.Searched.class::isInstance)
                .map(each -> ((At.Searched) each).why()).toList();
    }
}
