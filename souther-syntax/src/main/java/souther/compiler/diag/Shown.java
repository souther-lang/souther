package souther.compiler.diag;

import souther.compiler.diag.msg.Message;

import java.util.Objects;

/**
 * One place a report puts in front of a reader, and what it is doing there.
 *
 * <p>The role and not the place. Whether a stretch of text is what the message is about or is a
 * second place shown to explain it is a fact about the report, and it used to be a note held on the
 * place itself with null meaning "this is the one the message is about". Every reader of a place had
 * to know that, and a place with a note and a place without were the same type.
 *
 * <p>Which of these is the anchor depends on which file is being read, so both arms reach both
 * positions: a problem written in two files has the label as the anchor on the file the label is in
 * ({@link DiagnosticView}).
 */
public sealed interface Shown {

    /** Where this is. */
    Spot spot();

    /**
     * The place the message is about.
     *
     * <p>At most one of these in a view, and exactly one wherever the report's primary resolved to a
     * place. Where it did not — a report about a module rather than a stretch of text, one whose
     * code is out of sight, one in a text the surface did not name — there is none, and the reason
     * is {@link DiagnosticView#primary()}.
     */
    record ItsSubject(Spot spot) implements Shown {

        public ItsSubject {
            Objects.requireNonNull(spot, "the place a message is about is a place");
        }
    }

    /** A second place, with what it says about being pointed at. */
    record ALabel(Spot spot, Message said) implements Shown {

        public ALabel {
            Objects.requireNonNull(spot, "a second place a reader is sent to is somewhere");
            Objects.requireNonNull(said, "a second place says why it is pointed at");
        }
    }
}
