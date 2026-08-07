package souther.compiler.diag;


import java.util.ArrayList;
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
public record Diagnostic(Severity severity,
                         String code,
                         String titleKey,
                         Region region,
                         List<LabeledRegion> secondary,
                         String messageKey,
                         Object[] args,
                         String literalMessage,
                         TypeComparison diff,
                         List<Note> notes,
                         String suggestion) {

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
     */
    public record Identity(Severity severity, String code, String titleKey, Region region,
                           List<LabeledRegion.Of> secondary, String messageKey, List<Object> args,
                           String literalMessage, TypeComparison diff, List<Note.Of> notes,
                           String suggestion) {}

    public Identity identity() {
        List<LabeledRegion.Of> labels = new ArrayList<>();
        for (LabeledRegion label : secondary == null ? List.<LabeledRegion>of() : secondary) {
            labels.add(label.identity());
        }
        List<Note.Of> hints = new ArrayList<>();
        for (Note note : notes == null ? List.<Note>of() : notes) {
            hints.add(note.identity());
        }
        return new Identity(severity, code, titleKey, region, labels, messageKey,
                args == null ? List.of() : java.util.Arrays.asList(args), literalMessage, diff,
                hints, suggestion);
    }

    /** A pre-formatted English message wrapped verbatim — the compatibility path for a site that
     * has not yet been moved onto a catalog key. It carries no code and no title: a site with
     * either of those has a catalog key by now. {@code pos} may be null for a position-less error. */
    public static Diagnostic literal(SourcePos pos, String message) {
        return new Diagnostic(Severity.ERROR, null, null, pos == null ? null : Region.point(pos),
                List.of(), null, null, message, null, List.of(), null);
    }

    /**
     * A builder for a diagnostic that reports a known rule. The code carries the title, so the two
     * agree at every site reporting that rule and neither is given here.
     */
    public static Builder of(DiagnosticCode code, String messageKey) {
        return new Builder(code.name(), messageKey, code.titleKey());
    }


    public static final class Builder {
        private final String code;
        private final String messageKey;
        private final String titleKey;
        private Region region;
        private final List<LabeledRegion> secondary = new ArrayList<>();
        private Object[] args = new Object[0];
        private TypeComparison diff;
        private final List<Note> notes = new ArrayList<>();
        private String suggestion;
        private Severity severity = Severity.ERROR;

        private Builder(String code, String messageKey, String titleKey) {
            this.code = code;
            this.messageKey = messageKey;
            this.titleKey = titleKey;
        }

        /** Marks this a warning: it is reported but does not fail the build. */
        public Builder warning() {
            this.severity = Severity.WARNING;
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

        /** A second place to point at, in the same file as the primary region. */
        public Builder secondary(Region region, String labelKey, Object... labelArgs) {
            this.secondary.add(new LabeledRegion(region, null, labelKey, labelArgs));
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
            return new Diagnostic(severity, code, titleKey, region, List.copyOf(secondary),
                    messageKey, args, null, diff, List.copyOf(withMessageArgs(notes)), suggestion);
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
