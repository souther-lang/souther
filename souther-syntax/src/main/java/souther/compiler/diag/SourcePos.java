package souther.compiler.diag;

/**
 * A place in a source: a 1-based line and column, and the source they were read from. Every AST node
 * and token carries one so that compile errors can point at the source (spec section 28).
 *
 * <p>A line and a column are enough while one file is being read and not enough afterwards. A
 * module's {@code example} rows, fake tables and values are written in the module's own source and
 * in any number of attached {@code examples for} files, and once they are gathered under one name a
 * coordinate on its own no longer says which file it came from — so what is quoted is whatever
 * happens to sit at those numbers in the file the reader guessed at.
 *
 * <p>Which is why the source is part of the position and part of what makes two positions the same
 * one. Line 25 of two files is the same coordinate and is not the same place; a value whose identity
 * denied one of its components would leave "the same position" meaning something different in every
 * container that held one. Where a caller wants coordinates compared without a file — an editor
 * asking what is under a cursor — it compares the coordinates, which is what
 * {@code Names.spans} does.
 *
 * @param sourceId the source this was read from, or null for a position that was read from none: a
 *        node the compiler synthesized, or a module read off the module path, which is in no source
 *        of the compile that is reading it
 */
public record SourcePos(int line, int column, String sourceId) {

    public SourcePos {
        if (sourceId != null && sourceId.isBlank()) {
            throw new IllegalArgumentException("a source id names a source or is absent, never blank");
        }
    }

    /** A position read from no source. */
    public SourcePos(int line, int column) {
        this(line, column, null);
    }

    @Override
    public String toString() {
        return line + ":" + column;
    }
}
