package souther.compiler.diag;

import souther.compiler.source.SourceId;

/**
 * A text this compile is reading and cannot name, whose positions are where the code they name is
 * written.
 *
 * <p>Not a leftover. An editor holds a buffer before it is a file of any compile and asks what is
 * wrong with it; a caller parses a snippet to look at the tree. What such a position says is true —
 * somebody wrote that line, at that column — and what it cannot say is which file, so nothing built
 * from it reaches a reader without the caller saying where it is being read.
 *
 * <p>One instance. It holds nothing, so two of them would be the same value with two identities, and
 * what holds it is compared by the incremental engine.
 */
final class InAnUnnamedText extends Placement {

    static final InAnUnnamedText IT = new InAnUnnamedText();

    private InAnUnnamedText() {
    }

    @Override
    boolean namedByThisCompile() {
        return false;
    }

    @Override
    boolean codeIsWrittenHere() {
        return true;
    }

    @Override
    SourceId sourceId() {
        return null;
    }

    @Override
    SourceProvenance codeIsWrittenIn() {
        throw new NotWrittenElsewhere(this);
    }

    @Override
    Placement withCodeWrittenIn(SourceProvenance provenance) {
        return new InWhatAModulePublished(provenance);
    }

    @Override
    Citation cite(SourcePos at) {
        return new WrittenCitation(at);
    }

    @Override
    public String toString() {
        return "InAnUnnamedText";
    }
}
