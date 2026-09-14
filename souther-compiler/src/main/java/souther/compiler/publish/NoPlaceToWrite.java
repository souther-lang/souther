package souther.compiler.publish;

import souther.compiler.diag.Citation;

/**
 * A place a document was asked to write that names no file.
 *
 * <p>The shipped schema says a place has a source, a line and a column, and there are two ways to
 * arrive here without one. A position in a text this compilation cannot name, in a document about a
 * compile whose every source is named, is a position a pass minted rather than read — the open
 * question about whether such a position is a place at all. And a position inside a module's own
 * published text is a real place in a text no reader holds, which the contract has no shape for:
 * not a source, a line and a column, and not nothing either, since what a reader is owed there is
 * which module the code is in.
 *
 * <p>A refusal rather than a document with the fields left out or filled in from whatever file was
 * to hand. Both of those are documents the shipped schema forbids, written silently and read by a
 * build that trusted the version on them. Widening what a consumer must handle is a decision about
 * the contract, and it is not one to take by writing a field.
 *
 * <p>So what this says is that the decision has not been taken. It is loud on purpose: over this
 * compiler's own suite the places written here are eight, all of them in files it holds, which is
 * far too few to read as "this cannot happen".
 *
 * <p>Beside the projection that raises it rather than beside the writer, because it is a statement
 * about the contract and not about one surface. What a document may point at is one answer however
 * many surfaces go on to say it.
 */
public final class NoPlaceToWrite extends IllegalArgumentException {

    private static final long serialVersionUID = 1L;

    public NoPlaceToWrite(Citation where) {
        super("an adequacy document writes places in files this compile holds, and was given "
                + where);
    }

    /** The same, said of the fact rather than of one of the places it was met at — because there
     *  were several and naming whichever came to hand would say a different one each run. */
    public NoPlaceToWrite(souther.compiler.observe.Incompleteness.Fact about) {
        super("an adequacy document writes places in files this compile holds, and every place "
                + about + " was met at is in a text it cannot name");
    }
}
