package souther.compiler.diag;

import souther.compiler.diag.msg.FindingRegion;
import souther.compiler.diag.msg.Message;

/**
 * A second thing a diagnostic says, and where it says it about. Used when one error is about more
 * than one place — the left behavior's output and the right behavior's input of a failed
 * composition, the two branches of an {@code if} that disagree, the clause a construction is judged
 * against. {@code said} is what the label says, and carries the values it names.
 *
 * <p>{@code place} is the whole of where it is ({@link DiagnosticPlace}), settled when the label is
 * made. It used to be a region and a source that might be null, and null answered two questions at
 * once: a hand-made position meant "read it in the diagnostic's file", and a position read from a
 * text this compile has no file for meant the label had nowhere to go. Nothing downstream could tell
 * them apart, so a label about a published module's clause was read as a line of the file the caller
 * was compiling — and the readers that noticed dropped it instead, each in its own way.
 *
 * <p>So a label naming nothing quotable is not dropped and not placed: it is
 * {@link DiagnosticPlace.Unavailable}, and says where the code came from in words.
 */
public record LabeledRegion(DiagnosticPlace place, Message said) {

    public LabeledRegion {
        java.util.Objects.requireNonNull(place, "a secondary region is somewhere or says why not");
        java.util.Objects.requireNonNull(said, "a secondary region says why it is pointed at");
    }

    /** A label over {@code region}, wherever {@link DiagnosticPlace#of} says that is. */
    public LabeledRegion(Region region, Message said) {
        this(DiagnosticPlace.of(region), said);
    }

    /**
     * Whether the diagnostic finds this region wrong too, rather than showing it so that a reader
     * can see why the primary is — which is what the label says ({@link FindingRegion}), and is read
     * off nothing else.
     *
     * <p>What reads it is the decision about which files a report is said in. A report is said
     * wherever it is written, so an author editing any of those files is told; the rule a subject
     * was judged against is not one of those files, however necessary reading it is.
     */
    public boolean belongsToFinding() {
        return said instanceof FindingRegion;
    }
}
