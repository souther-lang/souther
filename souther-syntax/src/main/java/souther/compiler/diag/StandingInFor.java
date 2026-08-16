package souther.compiler.diag;

import souther.compiler.source.SourceId;

import java.util.Objects;

/**
 * A file this compile holds, whose positions stand in for code written where {@code provenance}
 * says — the call a body was spliced into, the import line a report was moved to.
 *
 * <p>The quadrant that makes the two questions two questions. The reader holds this file and can be
 * shown the line; the code the line names is somewhere this compile has no file for. Read off either
 * question alone, this is the other quadrant.
 *
 * <p>Reached only through {@link Placement#standingInFor}, so a caller can say that a position stands
 * in for a body and cannot say it about a text it is parsing. Whether code is out of sight is settled
 * where a text becomes positions; this carries an answer already given, to a position somewhere
 * else.
 */
final class StandingInFor extends Placement {

    private final SourceId sourceId;
    private final SourceProvenance provenance;

    StandingInFor(SourceId sourceId, SourceProvenance provenance) {
        this.sourceId = Objects.requireNonNull(sourceId,
                "a position standing in for code out of sight is one a reader holds the file for");
        this.provenance = Objects.requireNonNull(provenance,
                "code out of sight came from somewhere");
    }

    @Override
    boolean namedByThisCompile() {
        return true;
    }

    @Override
    boolean codeIsWrittenHere() {
        return false;
    }

    @Override
    SourceId sourceId() {
        return sourceId;
    }

    @Override
    SourceProvenance codeIsWrittenIn() {
        return provenance;
    }

    @Override
    Placement withCodeWrittenIn(SourceProvenance written) {
        return new StandingInFor(sourceId, written);
    }

    @Override
    Citation cite(SourcePos at) {
        return new OutOfSightCitation(provenance, at);
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof StandingInFor that && sourceId.equals(that.sourceId)
                && provenance.equals(that.provenance);
    }

    @Override
    public int hashCode() {
        return Objects.hash(sourceId, provenance);
    }

    @Override
    public String toString() {
        return "In[" + sourceId + " standingInFor " + provenance + "]";
    }
}
