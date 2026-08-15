package souther.compiler.diag;

import java.util.Objects;

/**
 * What a parse is reading, as the positions it makes will say it: which source of this compile the
 * lines and columns are in, and whether that is where the code is.
 *
 * <p>The two components of a {@link SourcePos} that are not the line and the column, held together
 * so that a caller cannot supply one and leave the other to a default. They are separate questions —
 * {@link WrittenAt} says so — and they are settled by one caller at one moment: whoever handed the
 * text over is the only thing that knows what the text is. Threaded as two parameters, a caller that
 * knew it was reading a published module could still name a source and get "the code is here" for
 * free, which is the shape this closes.
 *
 * <p>Three ways to build one, because there are three kinds of text this compiler parses. There is
 * deliberately no way to say "reassembled, and here is its source id": a text put back together out
 * of what a module published is in no file, and a caller with a file for it is reading a file.
 */
public record TextRead(String sourceId, WrittenAt writtenAt) {

    public TextRead {
        Objects.requireNonNull(writtenAt, "a parse says whether what it reads is where the code is");
    }

    /** A file this compile holds, under the identity it holds it by. Its positions are where the
     *  code is, and they say which file they are in. */
    public static TextRead aFileOfThisCompile(String sourceId) {
        return new TextRead(Objects.requireNonNull(sourceId, "a file of this compile is named"),
                WrittenAt.HERE);
    }

    /**
     * A text nobody has named — a snippet a caller parsed to look at the tree, a document being read
     * before the compile knows what to call it.
     *
     * <p>Its positions are where the code is: what was read is what somebody wrote. What they do not
     * say is which file, so nothing built from them reaches a reader on its own, and a report made
     * against one is a report the caller has to place.
     */
    public static TextRead aTextWithNoIdentity() {
        return new TextRead(null, WrittenAt.HERE);
    }

    /**
     * A text put back together out of what a module published, which this compile has no file for.
     *
     * <p>The positions are real positions in that text and are not where a reader can be sent, so
     * they say so from the moment they are made. Everything downstream — a body spliced into a
     * caller, a clause a construction is judged against, a guard that drew a line — reads the answer
     * rather than working it out from the source being absent.
     */
    public static TextRead whatAModulePublished(SourceProvenance provenance) {
        return new TextRead(null, WrittenAt.outOfSight(provenance));
    }

    /** The position of {@code line} and {@code column} in this text. */
    public SourcePos at(int line, int column) {
        return new SourcePos(line, column, sourceId, writtenAt);
    }
}
