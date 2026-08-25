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
 * <p><b>The authority on how many rows a line is offered.</b> A line is one piece of work however
 * many positions carry the type, and that is a rule about what is owed rather than about how a block
 * is laid out — so it is settled here, where the search is resolved, and every reader below is a
 * projection of this map. Left to the block, one authored line came out as up to four rows because
 * each reading composed its own (issue #1076), and a block written another way would have brought it
 * back.
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
public record DeclaredRows(GenerationScope scope,
        SequencedMap<BorderObligationPoint, Answer> resolved) {

    /**
     * What a generation came to at one point, and what that point asks of a row.
     *
     * <p>The words beside the answer because every reader of the answer needs them, and they are the
     * declaration's rather than any reading's: a reading names the position it met the line at, and
     * a subject taken from one would say the row is about that position. Worked out where the search
     * was, so that a reader with the answer never has to go back to the line for what it was about.
     *
     * @param owedBy the declaration that drew the line. Where a note about it goes, and the whole of
     *               what tells two lines apart that a reader would otherwise see written the same
     *               way: what a newtype wraps is spelled {@code value} in every declaration
     */
    public record Answer(String said, String owedBy, DeclarationResolution resolution) {

        public Answer {
            if (said == null || owedBy == null || resolution == null) {
                throw new IllegalArgumentException("an answer is to something, and is an answer");
            }
        }
    }

    public DeclaredRows {
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
     * still be handed the same one row per point.
     */
    public SequencedMap<String, List<Generator.GeneratedRow>> rowsByCarrier() {
        SequencedMap<String, List<Generator.GeneratedRow>> out = new LinkedHashMap<>();
        resolved.forEach((_, answer) -> {
            if (answer.resolution() instanceof DeclarationResolution.Generated(var by, var row)) {
                out.computeIfAbsent(by, _ -> new ArrayList<>()).add(row);
            }
        });
        return java.util.Collections.unmodifiableSequencedMap(out);
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
    public List<Unmet> unmet() {
        List<Unmet> out = new ArrayList<>();
        resolved.forEach((_, answer) -> {
            if (answer.resolution() instanceof DeclarationResolution.Unresolved(var coverage)) {
                out.add(unmet(answer, coverage));
            }
        });
        return List.copyOf(out);
    }

    /**
     * What is left to say about one point nothing composed a row for.
     *
     * <p>The one place the gate is passed. Every reader of this holds an answer whose shape says
     * what it may be spelled as, so none of them carries a copy of the rule.
     */
    private static Unmet unmet(Answer answer, SearchCoverage coverage) {
        List<At> came = new ArrayList<>();
        coverage.came().forEach((reading, search) -> {
            if (search instanceof SearchCoverage.ReadingSearch.Attempted(var why)) {
                came.add(new At(reading, why));
            }
        });
        if (came.isEmpty()) {
            return new Unmet.NothingWasSearched(answer.owedBy(), answer.said());
        }
        return coverage.provesTheLineCannotBeWritten()
                ? new Unmet.TheLineCannotBeWritten(answer.owedBy(), answer.said(), List.copyOf(came))
                : new Unmet.WhatTheReadingsCameTo(answer.owedBy(), answer.said(),
                        List.copyOf(came));
    }

    /** What one reading of the line came to, and which reading it was. */
    public record At(BorderObligationAssessment.Reading reading,
                     Generator.UnresolvedCombination why) {}

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
            if (!(finding.about()
                    instanceof About.APointOfADeclaredBorder(var debt, var role))) {
                continue;
            }
            if (!asked.contains(debt.id())) {
                continue;   // a line this request was not put a question about
            }
            BorderObligationPoint at = new BorderObligationPoint(debt.id(), role);
            Answer answer = resolved.get(at);
            if (answer == null) {
                throw new IllegalStateException(
                        "a finding about a line this generation was asked about and holds no answer"
                                + " for: " + at);
            }
            out.add(new Adequacy.GenerationDisposition(finding, switch (answer.resolution()) {
                case DeclarationResolution.Generated(var _, var row) ->
                        new GenerationOutcome.Generated(List.of(row));
                case DeclarationResolution.Unresolved(var coverage) ->
                        cannot(unmet(answer, coverage));
                case DeclarationResolution.NoSearch(var cause) -> throw new IllegalStateException(
                        "a finding at a point nothing was looked for at, which the measurement says"
                                + " needs nothing looked for: " + at + " " + cause);
            }));
        }
        return List.copyOf(out);
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
        return new GenerationOutcome.CannotGenerate(switch (unmet) {
            case Unmet.TheLineCannotBeWritten(var _, var _, var proving) ->
                    proving.stream().map(At::why).toList();
            case Unmet.WhatTheReadingsCameTo(var _, var _, var came) ->
                    came.stream().map(At::why).toList();
            case Unmet.NothingWasSearched(var _, var said) ->
                    List.of(new Generator.UnresolvedCombination(List.of(said),
                            Generator.UnresolvedCombination.Reason
                                    .NO_READING_OF_THE_LINE_COULD_BE_SEARCHED));
        });
    }
}
