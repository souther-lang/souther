package souther.compiler.diag;


import souther.compiler.diag.msg.FindingRegion;
import souther.compiler.diag.msg.Supporting;
import souther.compiler.diag.msg.Reported;
import souther.compiler.diag.msg.MessageCodes;
import souther.compiler.diag.msg.Message;

import java.util.ArrayList;
import java.util.List;

/**
 * A compile diagnostic as data, not a pre-formatted string. A renderer turns it into human text
 * (Elm-style, with a source snippet) or JSON (for tools and agents).
 *
 * <p>What it says is a {@link Message}: a record whose components are the values it is about, which
 * names the catalog entry it renders through and the rule it reports. A site chooses neither of
 * those as a string, so a diagnostic cannot name an entry that says nothing about the values it
 * carries. The one thing built without a message is {@link #literal}, which is not a diagnostic a
 * check raises: it wraps text the compiler was handed.
 *
 * <p>The {@code code} (e.g. {@code E1301}) and the {@link TypeComparison} types are
 * locale-independent — the stable identity a tool keys on. Everything else (title, message, hints,
 * secondary labels) follows the locale.
 */
public final class Diagnostic {

    private final Severity severity;
    private final DiagnosticCode code;
    private final Primary primary;
    private final List<LabeledRegion> secondary;
    private final String literalMessage;
    private final Message said;
    private final TypeComparison diff;
    private final List<Note> notes;
    private final String suggestion;

    private Diagnostic(Severity severity, DiagnosticCode code, Primary primary,
                       List<LabeledRegion> secondary, String literalMessage,
                       TypeComparison diff, List<Note> notes, String suggestion, Message said) {
        this.severity = severity;
        this.code = code;
        this.primary = primary;
        this.secondary = secondary;
        this.literalMessage = literalMessage;
        this.diff = diff;
        this.notes = notes;
        this.suggestion = suggestion;
        this.said = said;
    }

    /** What this says, as the values it is about, or null for a {@link #literal}. */
    public Message said() {
        return said;
    }

    /**
     * The values this is about, by the names its catalog entry writes them under.
     *
     * <p>What a reader is shown and what a caller reads are the same values under the same names —
     * a test asking which helper was reported asks for `helper`, rather than looking for it inside a
     * sentence or at a position in an array.
     */
    public java.util.Map<String, Object> values() {
        return said == null ? java.util.Map.of() : souther.compiler.diag.msg.MessageValues.of(said);
    }

    public Severity severity() {
        return severity;
    }

    /** The public identity, as the string a tool and a reader see, or null for a {@link #literal}. */
    public String code() {
        return code == null ? null : code.name();
    }

    /**
     * The category this is shown under, read off the code rather than held beside it — so two
     * diagnostics reporting one rule cannot be shown under two titles, and there is no constructor
     * that could put them there.
     */
    public String titleKey() {
        return code == null ? null : code.titleKey();
    }

    /** Where this points, or null where it points nowhere. A report that has something to say
     *  instead says it through {@link #primary()}; every surface that only wanted a region reads
     *  this and is told the same nothing it was told before. */
    public Region region() {
        return Primary.regionOf(primary);
    }

    /** What this points at, which is a region or is nowhere and where the code is. */
    public Primary primary() {
        return primary;
    }

    /**
     * What this report already says about where its code is written, or null where it says nothing.
     *
     * <p>Two ways of knowing and one answer. A report with nowhere to point carries it outright; one
     * pointing at a position carries it in what that position says, and a position in a module's
     * published text or copied out of one says it as surely as the first does. Split, they became two
     * questions with the same answer, and whoever was reading only the first had to work the second
     * out again from whatever was to hand — which is the shape this whole change is about.
     *
     * <p>Null where the report is about code the reader is looking at, and where it points at nothing
     * at all. Neither of those is an answer to be preferred over a caller's; both are the absence of
     * one.
     */
    public SourceProvenance whereItsCodeIsWritten() {
        return switch (primary) {
            case null -> null;
            case Primary.Unavailable(SourceProvenance from) -> from;
            case Primary.AtARegion(Region region) ->
                    Citation.of(region.start()) instanceof Citation.Elsewhere elsewhere
                            ? elsewhere.provenance() : null;
        };
    }

    public List<LabeledRegion> secondary() {
        return secondary;
    }

    public String literalMessage() {
        return literalMessage;
    }

    public TypeComparison diff() {
        return diff;
    }

    public List<Note> notes() {
        return notes;
    }

    public String suggestion() {
        return suggestion;
    }

    /** The primary source position (the region's start). */
    public SourcePos pos() {
        Region region = region();
        return region == null ? null : region.start();
    }

    /**
     * The same finding, said at {@code where} instead — for one about code this compile has no
     * source for.
     *
     * <p>A coordinate read from a text nobody holds is not a place a reader can be sent, and every
     * surface that quotes a line quotes it from a file: given one, a run with a single source quotes
     * whatever happens to sit at those numbers in the file the author is looking at, and one with
     * several drops the report for having nowhere to file it. Both are worse than saying where the
     * code is in words, which is what this does — {@code where} is where this compile met the
     * declaration, and the coordinate it is given says it stands in for code written in
     * {@code provenance} ({@link Citation}).
     *
     * <p>The one way to move a caret. Everything else about the finding is what it was, so the rule
     * it reports and the values it says it about do not change with how far away the code turned out
     * to be.
     *
     * <p>Every place, not the first. Two files may reach one declaration, and the problem is not
     * readable from either of them alone — neither import is the premise the other is measured by,
     * and an author editing the second is looking at a file that is fine while the build fails. So
     * the rest are labelled {@code alsoHere}, which says they are part of what is found wrong
     * ({@link souther.compiler.diag.msg.FindingRegion}) and is what puts the report in front of each
     * of those authors.
     *
     * <p>The labels this already had come along unchanged. Each of them says where it is on its own
     * ({@link DiagnosticPlace}), so none of them meant anything different while the caret was
     * elsewhere. They used to be filtered here, because one that named no source was read in the
     * diagnostic's file and the diagnostic's file was what this changes — a dependency between a
     * label and where it ends up that no label has any more.
     *
     * @throws IllegalArgumentException where {@code where} is empty. There is no such thing as
     *         reaching code from nowhere: a caller with no place to send a reader has a report to
     *         leave as it is, not one to move
     */
    public <M extends Message & FindingRegion> Diagnostic reachedFrom(List<SourcePos> where,
                                                                     SourceProvenance provenance,
                                                                     M alsoHere) {
        if (where.isEmpty()) {
            throw new IllegalArgumentException(
                    "code out of sight is reached from somewhere or the report stays where it is");
        }
        SourceProvenance known = whereItsCodeIsWritten();
        if (known != null && !known.equals(provenance)) {
            throw new MovedSomewhereElsesCode(known, provenance);
        }
        DeclaringCode declaring = new DeclaringCode(provenance);
        List<LabeledRegion> also = new ArrayList<>(secondary);
        for (SourcePos other : where.subList(1, where.size())) {
            also.add(new LabeledRegion(Region.point(other.standingInFor(declaring)), alsoHere));
        }
        return new Diagnostic(severity, code,
                new Primary.AtARegion(Region.point(where.get(0).standingInFor(declaring))),
                List.copyOf(also),
                literalMessage, diff, notes, suggestion, said);
    }

    /**
     * A report told its code was written somewhere other than where it already says.
     *
     * <p>Moving a report is a change to where a reader is sent and is not a change to what the
     * report is about. A caller supplies where the code is because a report with nothing pointed at
     * has no answer of its own to read; one that has an answer is not asking, and being handed a
     * different one means somebody worked it out again from what was to hand.
     *
     * <p>Marked, for the reason {@code DiagnosticPlace.NotAPlace} is: what raises this runs where an
     * analysis may fall open, and an unmarked refusal would be swallowed there.
     */
    public static final class MovedSomewhereElsesCode extends IllegalArgumentException
            implements TheCompilerDisagreesWithItself {

        private static final long serialVersionUID = 1L;

        MovedSomewhereElsesCode(SourceProvenance known, SourceProvenance given) {
            super("this report says its code is written in " + known + " and was moved as though it"
                    + " were written in " + given);
        }
    }

    /**
     * What makes two diagnostics one problem: everything this one says, compared by what it says.
     *
     * <p>{@code said} is in here because it is what carries the values. Two diagnostics of one rule
     * at one place, about different values, are told apart by nothing else. What reads this is the
     * store's own de-duplication, which keeps one report per identity — so leaving the values out
     * drops a real diagnostic rather than a repeat of one.
     */
    public record Identity(Severity severity, String code, String titleKey, Primary primary,
                           List<LabeledRegion> secondary, String literalMessage,
                           TypeComparison diff, List<Note> notes, String suggestion, Message said) {}

    public Identity identity() {
        return new Identity(severity, code(), titleKey(), primary,
                secondary == null ? List.of() : secondary, literalMessage, diff,
                notes == null ? List.of() : notes, suggestion, said);
    }

    /** A pre-formatted English message wrapped verbatim — the compatibility path for a site that
     * has not yet been moved onto a catalog key. It carries no code and no title: a site with
     * either of those has a catalog key by now. {@code pos} may be null for a position-less error. */
    public static Diagnostic literal(SourcePos pos, String message) {
        return new Diagnostic(Severity.ERROR, null,
                pos == null ? null : new Primary.AtARegion(Region.point(pos)),
                List.of(), message, null, List.of(), null, null);
    }

    /**
     * A diagnostic saying {@code message}, which {@link Builder#at} then gives a place. The rule it
     * reports and the title it is shown under are read off the message, so every site reporting one
     * rule agrees about both and neither is given here.
     */
    public static <M extends Message & Reported> Builder say(M message) {
        return new Builder().say(message);
    }

    /** A diagnostic about a place, which {@link Builder#say} then gives what it says. */
    public static Builder at(Region region) {
        return new Builder().at(region);
    }

    /** A diagnostic about a position, which {@link Builder#say} then gives what it says. */
    public static Builder at(SourcePos pos) {
        return new Builder().at(pos);
    }

    /** A diagnostic with nowhere to point, about code written in {@code from} — which
     *  {@link Builder#say} then gives what it says. */
    public static Builder atCodeWrittenOutOfSight(SourceProvenance from) {
        return new Builder().atCodeWrittenOutOfSight(from);
    }

    /** The same, over the {@code width} UTF-16 code units from {@code pos} — the length of the text
     * it is about, which is what a {@link Region} is measured in. Not a width on a screen: how much
     * room that text takes is the renderer's to work out, from the line it is quoting. */
    public static Builder at(SourcePos pos, int width) {
        return new Builder().at(pos, width);
    }


    public static final class Builder {
        private DiagnosticCode code;
        private Message said;
        private Primary primary;
        private final List<LabeledRegion> secondary = new ArrayList<>();
        private TypeComparison diff;
        private final List<Note> notes = new ArrayList<>();
        private String suggestion;

        private Builder() {
        }

        /**
         * What this diagnostic says. The rule it reports and the catalog entry it renders through
         * are read off {@code message}: neither is a string this site chooses.
         */
        public <M extends Message & Reported> Builder say(M message) {
            this.said = message;
            this.code = MessageCodes.of(message);
            return this;
        }

        /** A hint written as a message of its own. */
        public <M extends Message & Supporting> Builder hint(M hint) {
            this.notes.add(new Note(hint));
            return this;
        }

        public Builder at(SourcePos pos) {
            this.primary = pos == null ? null : new Primary.AtARegion(Region.point(pos));
            return this;
        }

        /**
         * The report points nowhere, and the code it is about is written in {@code from}.
         *
         * <p>What a finding about code inside a module's published text says. The position it was
         * found at is a line of a text no reader holds, so there is nothing to offer — and saying so
         * with no region at all would drop the one thing that is known, which is which module wrote
         * it. The same thing {@link #secondaryOutOfSight} says of a label.
         */
        public Builder atCodeWrittenOutOfSight(SourceProvenance from) {
            this.primary = new Primary.Unavailable(from);
            return this;
        }

        /**
         * The place, over the {@code width} units of text it is about — and over none of them where
         * the place only stands in for code written out of sight.
         *
         * <p>The width is measured on the text the report is about, and where the code was copied
         * here the position is somewhere else: a call in the caller's file, whose own text is
         * whatever length it happens to be. A position in a published module's own text is not that
         * — the numbers are that text's, and its width is the code's — so what this asks is whether
         * the position was borrowed, not whether a reader can be sent to it. Underlining a construction's width from there covers
         * however many characters of the call the two numbers happen to agree on — three columns
         * sized for {@code Yen} landing on {@code atL}. A point claims what is true, which is that
         * this is where the code was reached from.
         */
        public Builder at(SourcePos pos, int width) {
            if (pos == null) {
                this.primary = null;
            } else {
                this.primary = new Primary.AtARegion(
                        pos.wasCopiedHere() ? Region.point(pos) : Region.ofWidth(pos, width));
            }
            return this;
        }

        public Builder at(Region region) {
            this.primary = region == null ? null : new Primary.AtARegion(region);
            return this;
        }

        /**
         * A second thing to say, about wherever {@code region} is
         * ({@link DiagnosticPlace#of}) — a place a reader can be sent to, or a note about code this
         * compile holds no file for.
         *
         * <p>The region is the whole of what settles it. There used to be a second entry taking a
         * source beside a region that carries one, which is two authorities for one fact and is the
         * defect this closes said in an API: a caller that passed a name and a region read from
         * somewhere else put a marker in one file and quoted a line from another.
         *
         * @throws IllegalArgumentException where the region names no source and claims the code is
         *         written at it — a position made by hand and never placed. It used to be read in
         *         whichever file the diagnostic ended up filed under; a caller reaching here has a
         *         place to name and has not named it
         */
        public <M extends Message & Supporting> Builder secondary(Region region, M label) {
            this.secondary.add(new LabeledRegion(region, label));
            return this;
        }

        /** A second thing to say about code this compile holds no file for: where it came from, in
         *  place of somewhere to point. */
        public <M extends Message & Supporting> Builder secondaryOutOfSight(
                SourceProvenance provenance, M label) {
            this.secondary.add(
                    new LabeledRegion(new DiagnosticPlace.Unavailable(provenance), label));
            return this;
        }

        public Builder diff(String actualType, String expectedType) {
            this.diff = new TypeComparison(actualType, expectedType);
            return this;
        }

        public Builder suggestion(String suggestion) {
            this.suggestion = suggestion;
            return this;
        }

        public Diagnostic build() {
            if (code == null) {
                throw new IllegalStateException("a diagnostic reports a rule; call `say`");
            }
            return new Diagnostic(code.severity(), code, primary, List.copyOf(secondary), null,
                    diff, List.copyOf(notes), suggestion, said);
        }
    }
}
