package souther.compiler.diag;

import java.util.Objects;

/**
 * Where a node is placed in this compile, and whether that is where its code is written: a 1-based
 * line and column, the source they were read from, and {@link WrittenAt}. Every AST node and token
 * carries one so that compile errors can point at the source (spec §non-functional).
 *
 * <p>The coordinate is <b>where this compile places the node</b>, which is where the code is written
 * for everything a source was read for and is not for a copy that could not keep its own positions.
 * So this answers where to send a reader and never, on its own, where the code is written. What
 * answers that is a {@link Citation}, which a report holds instead of a coordinate; a pass that
 * wants only to know whether the place is a stand-in asks {@link #isOutOfSight()}. Neither is
 * inferred from the line: inferring it is what {@code BottomInfer} did, by comparing an argument's
 * coordinate with its call's, and what {@code HelperInliner} did, by comparing the declaring module
 * with its own.
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
 * <p>{@link #writtenAt()} is the other half of the same question and the reason it is here rather
 * than beside it: an expansion gives a copy the call site where it cannot give it its own positions,
 * and after that the coordinate is a place in the caller's file which is not where the code is. That
 * is a fact about this coordinate, so it travels with it — through every pass that rebuilds a node
 * keeping its position, which is all of them. It is part of what makes two positions the same one
 * for that reason: two coordinates that differ in it are read differently by every surface, so an
 * answer that changed only here has changed and two diagnostics that differ only here are two
 * problems.
 *
 * @param line the 1-based line this node is placed at
 * @param column the 1-based column this node is placed at, in UTF-16 code units
 * @param sourceId the source the coordinate is in, or null for a position that is in none: a node
 *        the compiler synthesized, or a module read off the module path, which is in no source of
 *        the compile that is reading it
 * @param writtenAt whether the code this names is written at the coordinate, or the coordinate
 *        stands in for code written out of sight ({@link WrittenAt})
 */
public record SourcePos(int line, int column, String sourceId, WrittenAt writtenAt) {

    public SourcePos {
        if (sourceId != null && sourceId.isBlank()) {
            throw new IllegalArgumentException("a source id names a source or is absent, never blank");
        }
        Objects.requireNonNull(writtenAt, "a position says whether the code it names is written at it");
    }

    /** A place a source was read for, where the code it names is written. */
    public SourcePos(int line, int column, String sourceId) {
        this(line, column, sourceId, WrittenAt.HERE);
    }

    /** A position read from no source. */
    public SourcePos(int line, int column) {
        this(line, column, null, WrittenAt.HERE);
    }

    /**
     * This coordinate, standing in for code written out of sight — what an expansion gives a copy it
     * cannot give its own positions.
     *
     * <p>Set here and nowhere else that a source is read: a coordinate a parser made is where the
     * code is, by construction, and one that says otherwise was made by a pass that put code
     * somewhere it was not written.
     *
     * @throws IllegalArgumentException where {@code out} is not a stand-in. Standing in for code
     *         written at this very coordinate is not a thing to say, and a caller that reached here
     *         with {@link WrittenAt#HERE} was branching on something other than the question
     */
    public SourcePos standingInFor(WrittenAt out) {
        if (!out.isOutOfSight()) {
            throw new IllegalArgumentException(
                    "a coordinate stands in only for code written out of sight");
        }
        return new SourcePos(line, column, sourceId, out);
    }

    /** The same place, {@code units} along the same line — the other end of a region of that width.
     *  It stands in for whatever this stands in for: the two ends are one place. */
    public SourcePos along(int units) {
        return new SourcePos(line, column + units, sourceId, writtenAt);
    }

    /** Whether the code this names is written somewhere this compile cannot show, this coordinate
     *  being where it was reached from instead. */
    public boolean isOutOfSight() {
        return writtenAt.isOutOfSight();
    }

    @Override
    public String toString() {
        return line + ":" + column;
    }
}
