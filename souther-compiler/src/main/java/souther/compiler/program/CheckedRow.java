package souther.compiler.program;

import souther.compiler.diag.SourcePos;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.Position;
import souther.compiler.observe.RowIdentity;
import souther.compiler.observe.RowStatement;
import souther.compiler.observe.ValueTypes;
import souther.compiler.observe.Verdict;

/**
 * One {@code example} row of a behavior, for an output that lives outside this compiler.
 *
 * <p>A behavior's rows are what the language says it answers, and running them is not a test of the
 * compiler: a program whose rows do not hold is not accepted. So an output holding one of these
 * holds an obligation the language already checked as far as it can be checked without something to
 * apply the behavior — and what it can do with it is apply its own emission and ask whether the row
 * holds.
 *
 * <p>Asking is {@link #holds}, and it is asked here rather than answered by the reader. Whether an
 * answer is the value a row states is a question the language settles — a written
 * {@code Set.fromList([1])} at a {@code List} is not the sequence a list is, and two values differ
 * when their types differ as much as when their contents do. An output free to answer it for itself
 * would be a second reading of what a row means, and two outputs of one program would then agree
 * about it only as far as whoever wrote the second one agreed with the first.
 *
 * <p>What it carries to answer that is the question and not the answerer: what this program's
 * declarations say stands inside a value, and where this behavior's answer stands. It holds no
 * program, no module and no declaration of its own — a row is a row of the program it was read
 * from, and it is that program's reading of the declarations that it asks.
 */
public final class CheckedRow {

    private final RowIdentity identity;
    private final SourcePos at;
    private final RowStatement statement;
    private final ValueTypes types;
    private final Position answers;

    CheckedRow(RowIdentity identity, SourcePos at, RowStatement statement, ValueTypes types,
               Position answers) {
        if (identity == null || at == null || statement == null || types == null
                || answers == null) {
            throw new IllegalArgumentException("a row is what it names itself, where it is written,"
                    + " what it states, and what reads the values it is about");
        }
        this.identity = identity;
        this.at = at;
        this.statement = statement;
        this.types = types;
        this.answers = answers;
    }

    /**
     * What the row names itself.
     *
     * <p>A name where it was written with one, and which of its behavior's rows it is where it was
     * not. What a report writes and what a generated test is named after; not a key, since a row
     * written without a name answers to nothing outside its file.
     */
    public RowIdentity identity() {
        return identity;
    }

    /** Where the row is written, which says the source as well as the line: a behavior exampled in
     *  its module and in an attached file has rows in both. */
    public SourcePos at() {
        return at;
    }

    /** What the row states, which is not always values ({@link RowStatement}). */
    public RowStatement statement() {
        return statement;
    }

    /**
     * Whether {@code answered} is what this row states the behavior answers.
     *
     * @throws IllegalStateException where the row states no values to hold an answer to. What it
     *     states says so in advance ({@link #statement()}), so a reader that asked without looking
     *     is told rather than given a verdict about a row that made no claim about a value
     */
    public Verdict holds(ObservedValue answered) {
        if (!(statement instanceof RowStatement.Stated stated)) {
            throw new IllegalStateException("this row states no values to hold an answer to: "
                    + statement);
        }
        if (answered == null) {
            throw new IllegalArgumentException("a row is held against an answer");
        }
        return stated.expects().compare(answered, types, answers);
    }

    @Override
    public String toString() {
        return identity.shown();
    }
}
