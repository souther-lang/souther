package souther.compiler.diag;


import souther.compiler.diag.msg.Code;
import souther.compiler.diag.msg.Message;

import java.util.ArrayList;
import java.util.Objects;
import java.util.List;

/**
 * A compile diagnostic as data, not a pre-formatted string. A renderer turns it into human text
 * (Elm-style, with a source snippet) or JSON (for tools and agents). Two message forms coexist:
 *
 * <ul>
 *   <li>a catalog {@code messageKey} plus {@code args}, resolved against the selected locale — the
 *       target form for migrated sites;</li>
 *   <li>a {@code literalMessage} already in English — the compatibility form, so the ~180 existing
 *       throw sites render through the same pipeline before they are migrated.</li>
 * </ul>
 *
 * The {@code code} (e.g. {@code E1301}) and the {@link TypeComparison} types are locale-independent
 * — the stable identity a tool keys on. Everything else (title, message, hints, secondary labels)
 * follows the locale.
 *
 * <p>Every diagnostic built through {@link #of} carries a {@link DiagnosticCode}, which carries its
 * own {@code titleKey} — so a code and a title cannot disagree between two sites reporting one rule,
 * and there is no way to build a diagnostic a reader cannot look up. What is left without one is
 * {@link #literal}, which is not a diagnostic a check raises: it wraps a message the compiler was
 * handed.
 */
public final class Diagnostic {

    private final Severity severity;
    private final DiagnosticCode code;
    private final Region region;
    private final List<LabeledRegion> secondary;
    private final String messageKey;
    private final Object[] args;
    private final String literalMessage;
    private final Message said;
    private final TypeComparison diff;
    private final List<Note> notes;
    private final String suggestion;

    private Diagnostic(Severity severity, DiagnosticCode code, Region region,
                       List<LabeledRegion> secondary, String messageKey, Object[] args,
                       String literalMessage, TypeComparison diff, List<Note> notes,
                       String suggestion, Message said) {
        this.severity = severity;
        this.code = code;
        this.region = region;
        this.secondary = secondary;
        this.messageKey = messageKey;
        this.args = args;
        this.literalMessage = literalMessage;
        this.diff = diff;
        this.notes = notes;
        this.suggestion = suggestion;
        this.said = said;
    }

    /**
     * What this says, as the values it is about, or null for a site not yet written that way.
     *
     * <p>A renderer reads this rather than the key and the arguments: the entry names each value,
     * so the text is filled by name.
     */
    public Message said() {
        return said;
    }

    /**
     * The values this is about, by the names its catalog entry writes them under, or empty for a
     * site not yet written as a message.
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

    public String messageKey() {
        return messageKey;
    }

    public Object[] args() {
        return args;
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
     * <p>Written out rather than left to the record because {@code args} is an array, and a record
     * compares an array component by identity — so two diagnostics built the same way from the same
     * values are never equal. The arguments are the difference between "expected A, found B" and
     * "expected C, found B", which is two problems and not one, so they are in here.
     *
     * <p>{@code said} is here for the same reason and is the one that matters now: a message carries
     * its values as record components rather than in {@code args}, so two diagnostics of one rule at
     * one place, about different values, are told apart by nothing else. What reads this is the
     * store's own de-duplication, which keeps one report per identity — so leaving the values out
     * drops a real diagnostic rather than a repeat of one.
     */
    public record Identity(Severity severity, String code, String titleKey, Region region,
                           List<LabeledRegion.Of> secondary, String messageKey, List<Object> args,
                           String literalMessage, TypeComparison diff, List<Note.Of> notes,
                           String suggestion, Message said) {}

    public Identity identity() {
        List<LabeledRegion.Of> labels = new ArrayList<>();
        for (LabeledRegion label : secondary == null ? List.<LabeledRegion>of() : secondary) {
            labels.add(label.identity());
        }
        List<Note.Of> hints = new ArrayList<>();
        for (Note note : notes == null ? List.<Note>of() : notes) {
            hints.add(note.identity());
        }
        return new Identity(severity, code(), titleKey(), region, labels, messageKey,
                args == null ? List.of() : java.util.Arrays.asList(args), literalMessage, diff,
                hints, suggestion, said);
    }

    /** A pre-formatted English message wrapped verbatim — the compatibility path for a site that
     * has not yet been moved onto a catalog key. It carries no code and no title: a site with
     * either of those has a catalog key by now. {@code pos} may be null for a position-less error. */
    public static Diagnostic literal(SourcePos pos, String message) {
        return new Diagnostic(Severity.ERROR, null, pos == null ? null : Region.point(pos),
                List.of(), null, null, message, null, List.of(), null, null);
    }

    /**
     * A builder for a diagnostic that reports a known rule. The code carries the title, so the two
     * agree at every site reporting that rule and neither is given here.
     */
    /** A diagnostic saying {@code message}, which {@link Builder#at} then gives a place. */
    public static Builder say(Message message) {
        return new Builder(null, null).say(message);
    }

    /** A diagnostic about a place, which {@link Builder#say} then gives what it says. */
    public static Builder at(Region region) {
        return new Builder(null, null).at(region);
    }

    /** A diagnostic about a position, which {@link Builder#say} then gives what it says. */
    public static Builder at(SourcePos pos) {
        return new Builder(null, null).at(pos);
    }

    /** The same, underlining {@code width} columns from {@code pos}. */
    public static Builder at(SourcePos pos, int width) {
        return new Builder(null, null).at(pos, width);
    }

    public static Builder of(DiagnosticCode code, String messageKey) {
        return new Builder(Objects.requireNonNull(code, "a diagnostic reports a rule, and a rule has"
                + " a code; `literal` is the one path without one"), messageKey);
    }


    public static final class Builder {
        private DiagnosticCode code;
        private String messageKey;
        private Message said;
        private Region region;
        private final List<LabeledRegion> secondary = new ArrayList<>();
        private Object[] args = new Object[0];
        private TypeComparison diff;
        private final List<Note> notes = new ArrayList<>();
        private String suggestion;

        private Builder(DiagnosticCode code, String messageKey) {
            this.code = code;
            this.messageKey = messageKey;
        }

        /**
         * What this diagnostic says. The rule it reports and the catalog entry it renders through
         * are read off {@code message}: neither is a string this site chooses.
         */
        public Builder say(Message message) {
            Code reports = message.getClass().getAnnotation(Code.class);
            if (reports == null) {
                throw new IllegalArgumentException("a message reports a rule, and "
                        + message.getClass().getName() + " names no code");
            }
            this.said = message;
            this.code = reports.value();
            this.messageKey = message.key();
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

        public Builder args(Object... args) {
            this.args = args;
            return this;
        }

        /** A second place to point at, saying what it says as the values it is about. */
        public Builder secondary(Region region, Message label) {
            this.secondary.add(new LabeledRegion(region, null, label));
            return this;
        }

        /** A second place to point at, in the same file as the primary region. */
        public Builder secondary(Region region, String labelKey, Object... labelArgs) {
            this.secondary.add(new LabeledRegion(region, null, labelKey, labelArgs));
            return this;
        }

        /** A second place to point at, in {@code sourceId}, saying what it says as a message. */
        public Builder secondaryIn(String sourceId, Region region, Message label) {
            this.secondary.add(new LabeledRegion(region, sourceId, label));
            return this;
        }

        /** A second place to point at, in {@code sourceId} — for a problem written in two files,
         * where quoting the second against the first would draw a caret under the wrong text. */
        public Builder secondaryIn(String sourceId, Region region, String labelKey,
                                   Object... labelArgs) {
            this.secondary.add(new LabeledRegion(region, sourceId, labelKey, labelArgs));
            return this;
        }

        public Builder diff(String actualType, String expectedType) {
            this.diff = new TypeComparison(actualType, expectedType);
            return this;
        }

        public Builder hint(String hintKey, Object... hintArgs) {
            this.notes.add(new Note(hintKey, hintArgs));
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
            return new Diagnostic(code.severity(), code, region, List.copyOf(secondary),
                    messageKey, args, null, diff, List.copyOf(withMessageArgs(notes)), suggestion,
                    said);
        }

        /** A hint's text is written against the same numbered arguments as the message it follows
         * ({@code Add `constructs {1}` to `{0}`}), so a site that names the hint without repeating
         * them takes the message's. A hint given arguments of its own keeps them. */
        private List<Note> withMessageArgs(List<Note> notes) {
            if (args.length == 0) {
                return notes;
            }
            List<Note> filled = new ArrayList<>(notes.size());
            for (Note n : notes) {
                filled.add(n.args().length == 0 ? new Note(n.messageKey(), args) : n);
            }
            return filled;
        }
    }
}
