package souther.compiler.diag;

import souther.compiler.source.SourceId;

import java.util.Objects;

/**
 * Where a node is placed in this compile: a 1-based line and column, and the text they are in
 * ({@link Placement}). Every AST node and token carries one so that compile errors can point at the
 * source (spec §non-functional).
 *
 * <p>The line and the column are <b>where this compile placed the node</b>, which is where the code
 * is written for everything a source was read for and is not for a copy that could not keep its own
 * positions. So this answers where to send a reader and never, on its own, where the code is
 * written. What answers that is a {@link Citation}, which a report holds instead of a position; a
 * pass that wants only to know whether the place is a stand-in asks {@link #isOutOfSight()}. Neither
 * is inferred from the line: inferring it is what {@code BottomInfer} did, by comparing an
 * argument's position with its call's, and what {@code HelperInliner} did, by comparing the
 * declaring module with its own.
 *
 * <p>A line and a column are enough while one file is being read and not enough afterwards. A
 * module's {@code example} rows, fake tables and values are written in the module's own source and
 * in any number of attached {@code examples for} files, and once they are gathered under one name a
 * line and a column on their own no longer say which file they came from — so what is quoted is
 * whatever happens to sit at those numbers in the file the reader guessed at.
 *
 * <p>Which is why the text is part of the position and part of what makes two positions the same
 * one. Line 25 of two files is the same pair of numbers and is not the same place; a value whose
 * identity denied one of its components would leave "the same position" meaning something different
 * in every container that held one. Where a caller wants the numbers compared without the text — an
 * editor asking what is under a cursor — it compares the numbers, which is what {@code Names.spans}
 * does.
 *
 * <p>One component and not two. Which file this is in and whether the code is written here are two
 * questions, and only four of their nine combinations are places this compiler makes: the pair is
 * what is legal, so the pair is what is held. Kept apart, every reader worked the classification out
 * again from whichever half it had, and a null source meant "out of sight" to one of them, "the
 * diagnostic's own file" to another and "drop this" to two more.
 *
 * @param line the 1-based line this node is placed at
 * @param column the 1-based column this node is placed at, in UTF-16 code units
 * @param placement the text these numbers are in, and what this compilation knows about it
 */
public record SourcePos(int line, int column, Placement placement) {

    public SourcePos {
        Objects.requireNonNull(placement, "a position is in some text and says which");
    }

    /** A place a source was read for, where the code it names is written — or a text with no
     *  identity where {@code sourceId} is none. */
    public SourcePos(int line, int column, SourceId sourceId) {
        this(line, column, sourceId == null ? Placement.aTextWithNoIdentity()
                : Placement.aFileOfThisCompile(sourceId));
    }

    /** A position read from no source. */
    public SourcePos(int line, int column) {
        this(line, column, Placement.aTextWithNoIdentity());
    }

    /** The source this is in, or null where the text it is in has no identity in this compilation.
     *  A {@link SourceId} rather than a name, so that what a caller chose to call a module cannot
     *  arrive here instead. */
    SourceId sourceId() {
        return placement.sourceId();
    }

    /**
     * Which source of this compilation this is read from, and what to say where it is none.
     *
     * <p>The one way to ask which file a position is in. What used to be asked of a source identity
     * that could be null, by five consumers that each read the absence as an answer to a question of
     * their own — {@link QuotedFrom} says why there is no file, and leaves what to do about it where
     * it belongs.
     */
    public QuotedFrom quotedFrom() {
        return placement.quotedFrom();
    }

    /** Whether this is a position in {@code source}. */
    public boolean isIn(SourceId source) {
        return source.equals(placement.sourceId());
    }

    /** Whether this and {@code other} are in the same text — the same file, or neither of them a
     *  file this compilation has named. Said of the text and not of what is written in it: a body
     *  spliced into a file is in that file. */
    public boolean isInTheSameTextAs(SourcePos other) {
        return placement.isTheSameTextAs(other.placement);
    }

    /**
     * This position, standing in for code written where {@code declaring} says — what an expansion
     * gives a copy it cannot give its own positions, and what moving a report's caret gives the
     * place it moved to.
     *
     * <p>Not where a stand-in is first decided. Whether code is out of sight is settled where a text
     * becomes positions, by the caller that knows what the text was, and a position a parser made
     * says so from the start — a text put back together out of what a module published is read by a
     * parser like any other, and line 4 of it is a line of nothing anybody holds. What this does is
     * carry an answer already given to a position somewhere else: the call a body was spliced into,
     * the import line a report was moved to.
     *
     * <p>What it keeps is which text this is in, and what it replaces is what the code in it is. The
     * two are the two questions a {@link Placement} answers, and a splice moves exactly one of them.
     *
     * @throws Placement.NotWrittenElsewhere where {@code declaring} says its code is written at it.
     *         Standing in for code written at this very position is not a thing to say, and a caller
     *         that reached here was branching on something other than the question
     */
    public SourcePos standingInFor(Placement declaring) {
        return new SourcePos(line, column, placement.standingInFor(declaring));
    }

    /**
     * What this says about where its code is written, reached by {@code name} instead — what a
     * splice writes when it learns the name the call reaches, a parse of a published module having
     * known only the module.
     *
     * @throws Placement.NotWrittenElsewhere where the code this names is written at it
     */
    public Placement reachedBy(String name) {
        return placement.reachedBy(name);
    }

    /** The same place, {@code units} along the same line — the other end of a region of that width.
     *  It stands in for whatever this stands in for: the two ends are one place. */
    public SourcePos along(int units) {
        return new SourcePos(line, column + units, placement);
    }

    /** Whether the code this names is written somewhere this compile cannot show, this position
     *  being where it was reached from instead. */
    public boolean isOutOfSight() {
        return !placement.codeIsWrittenHere();
    }

    @Override
    public String toString() {
        return line + ":" + column;
    }
}
