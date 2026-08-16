package souther.compiler.diag;

import souther.compiler.source.SourceId;

/** A file this compile holds, whose positions are where the code they name is written. */
final class InAFileOfThisCompile extends Placement {

    private final SourceId sourceId;

    InAFileOfThisCompile(SourceId sourceId) {
        this.sourceId = sourceId;
    }

    @Override
    boolean namedByThisCompile() {
        return true;
    }

    @Override
    boolean codeIsWrittenHere() {
        return true;
    }

    @Override
    SourceId sourceId() {
        return sourceId;
    }

    @Override
    SourceProvenance codeIsWrittenIn() {
        throw new NotWrittenElsewhere(this);
    }

    @Override
    Placement withCodeWrittenIn(SourceProvenance provenance) {
        return new StandingInFor(sourceId, provenance);
    }

    @Override
    Citation cite(SourcePos at) {
        return new WrittenCitation(at);
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof InAFileOfThisCompile that && sourceId.equals(that.sourceId);
    }

    @Override
    public int hashCode() {
        return sourceId.hashCode();
    }

    @Override
    public String toString() {
        return "In[" + sourceId + "]";
    }
}
