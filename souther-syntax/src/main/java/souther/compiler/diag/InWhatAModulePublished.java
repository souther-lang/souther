package souther.compiler.diag;

import souther.compiler.source.SourceId;

import java.util.Objects;

/**
 * A text put back together out of what a module published, which this compile has no file for and
 * whose positions are not where a reader can be sent.
 *
 * <p>Line 4 of such a text exists — a parser really did read a character there — and it is a line of
 * nothing anybody holds. Both of the two questions answer no here, and the position is honest about
 * each: there is nothing to quote, and the code is written where {@code provenance} says.
 */
final class InWhatAModulePublished extends Placement {

    private final SourceProvenance provenance;

    InWhatAModulePublished(SourceProvenance provenance) {
        this.provenance = Objects.requireNonNull(provenance,
                "code out of sight came from somewhere");
    }

    @Override
    boolean namedByThisCompile() {
        return false;
    }

    @Override
    boolean codeIsWrittenHere() {
        return false;
    }

    @Override
    SourceId sourceId() {
        return null;
    }

    @Override
    SourceProvenance codeIsWrittenIn() {
        return provenance;
    }

    @Override
    Placement withCodeWrittenIn(SourceProvenance written) {
        return new InWhatAModulePublished(written);
    }

    @Override
    Citation cite(SourcePos at) {
        return new OutOfSightCitation(provenance, at);
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof InWhatAModulePublished that && provenance.equals(that.provenance);
    }

    @Override
    public int hashCode() {
        return provenance.hashCode();
    }

    @Override
    public String toString() {
        return "InWhatAModulePublished[" + provenance + "]";
    }
}
