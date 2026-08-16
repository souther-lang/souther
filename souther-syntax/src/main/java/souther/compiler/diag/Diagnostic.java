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
    private final Region region;
    private final List<LabeledRegion> secondary;
    private final String literalMessage;
    private final Message said;
    private final TypeComparison diff;
    private final List<Note> notes;
    private final String suggestion;

    private Diagnostic(Severity severity, DiagnosticCode code, Region region,
                       List<LabeledRegion> secondary, String literalMessage,
                       TypeComparison diff, List<Note> notes, String suggestion, Message said) {
        this.severity = severity;
        this.code = code;
        this.region = region;
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

    public Region region() {
        return region;
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
        DeclaringCode declaring = new DeclaringCode(provenance);
        List<LabeledRegion> also = new ArrayList<>(secondary);
        for (SourcePos other : where.subList(1, where.size())) {
            also.add(new LabeledRegion(Region.point(other.standingInFor(declaring)), alsoHere));
        }
        return new Diagnostic(severity, code,
                Region.point(where.get(0).standingInFor(declaring)), List.copyOf(also),
                literalMessage, diff, notes, suggestion, said);
    }

    /**
     * What makes two diagnostics one problem: everything this one says, compared by what it says.
     *
     * <p>{@code said} is in here because it is what carries the values. Two diagnostics of one rule
     * at one place, about different values, are told apart by nothing else. What reads this is the
     * store's own de-duplication, which keeps one report per identity — so leaving the values out
     * drops a real diagnostic rather than a repeat of one.
     */
    public record Identity(Severity severity, String code, String titleKey, Region region,
                           List<LabeledRegion> secondary, String literalMessage,
                           TypeComparison diff, List<Note> notes, String suggestion, Message said) {}

    public Identity identity() {
        return new Identity(severity, code(), titleKey(), region,
                secondary == null ? List.of() : secondary, literalMessage, diff,
                notes == null ? List.of() : notes, suggestion, said);
    }

    /** A pre-formatted English message wrapped verbatim — the compatibility path for a site that
     * has not yet been moved onto a catalog key. It carries no code and no title: a site with
     * either of those has a catalog key by now. {@code pos} may be null for a position-less error. */
    public static Diagnostic literal(SourcePos pos, String message) {
        return new Diagnostic(Severity.ERROR, null, pos == null ? null : Region.point(pos),
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

    /** The same, over the {@code width} UTF-16 code units from {@code pos} — the length of the text
     * it is about, which is what a {@link Region} is measured in. Not a width on a screen: how much
     * room that text takes is the renderer's to work out, from the line it is quoting. */
    public static Builder at(SourcePos pos, int width) {
        return new Builder().at(pos, width);
    }


    public static final class Builder {
        private DiagnosticCode code;
        private Message said;
        private Region region;
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
            this.region = pos == null ? null : Region.point(pos);
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
                this.region = null;
            } else {
                this.region = pos.wasCopiedHere() ? Region.point(pos) : Region.ofWidth(pos, width);
            }
            return this;
        }

        public Builder at(Region region) {
            this.region = region;
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
            return new Diagnostic(code.severity(), code, region, List.copyOf(secondary), null,
                    diff, List.copyOf(notes), suggestion, said);
        }
    }
}
