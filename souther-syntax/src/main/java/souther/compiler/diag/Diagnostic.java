package souther.compiler.diag;


import souther.compiler.diag.msg.Code;
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
    public static Builder say(Message message) {
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

    /** The same, underlining {@code width} columns from {@code pos}. */
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
        public Builder say(Message message) {
            this.said = message;
            this.code = message.reports();
            return this;
        }

        /** A hint written as a message of its own. */
        public Builder hint(Message hint) {
            this.notes.add(new Note(hint));
            return this;
        }

        public Builder at(SourcePos pos) {
            this.region = pos == null ? null : Region.point(pos);
            return this;
        }

        public Builder at(SourcePos pos, int width) {
            this.region = pos == null ? null : Region.ofWidth(pos, width);
            return this;
        }

        public Builder at(Region region) {
            this.region = region;
            return this;
        }

        /** A second place to point at, saying what it says as the values it is about. */
        public Builder secondary(Region region, Message label) {
            this.secondary.add(new LabeledRegion(region, null, label));
            return this;
        }

        /** A second place to point at, in {@code sourceId}, saying what it says as a message. */
        public Builder secondaryIn(String sourceId, Region region, Message label) {
            this.secondary.add(new LabeledRegion(region, sourceId, label));
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
