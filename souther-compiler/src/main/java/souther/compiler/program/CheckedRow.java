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
 * <p>Asking is {@link Reproducible#holds}, and it is asked of the language rather than answered by
 * the reader. Whether an answer is the value a row states is a decision the language makes — a
 * written {@code Set.fromList([1])} at a {@code List} is not the sequence a list is, and two values
 * differ when their types differ as much as when their contents do. An output free to answer it for
 * itself would be a second reading of what a row means, and two outputs of one program would then
 * agree about it only as far as whoever wrote the second one agreed with the first.
 */
public final class CheckedRow {

    private final RowIdentity identity;
    private final SourcePos at;
    private final Statement statement;

    CheckedRow(RowIdentity identity, SourcePos at, Statement statement) {
        if (identity == null || at == null || statement == null) {
            throw new IllegalArgumentException("a row is what it names itself, where it is written,"
                    + " and what it states");
        }
        this.identity = identity;
        this.at = at;
        this.statement = statement;
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

    /** What the row states, and whether an answer can be held against it. */
    public Statement statement() {
        return statement;
    }

    /**
     * What a row states, as a reader of a checked program may act on it.
     *
     * <p>Two arms, because there are two things a reader can do. A row that hands over values can be
     * asked whether an answer keeps it; one that does not says why, and there is nothing to ask.
     * Said as arms rather than as a question that refuses to be asked, so that a reader which never
     * looked cannot get a verdict about a row that stated no values — the type is what stops it,
     * rather than a rule it has to have read.
     */
    public sealed interface Statement {

        /** What the row states, whichever of the two this is. */
        RowStatement states();
    }

    /**
     * A row an output can put to its own emission: the inputs it hands over, and what it states of
     * the answer.
     *
     * <p>What it carries to answer {@link #holds} is the question and not an answerer: what this
     * program's declarations say stands inside a value, and where this behavior's answer stands.
     * It holds no program, no module and no declaration of its own — a row is a row of the program
     * it was read from, and it is that program's reading of the declarations that it asks.
     */
    public static final class Reproducible implements Statement {

        private final RowStatement.Stated stated;
        private final ValueTypes types;
        private final Position answers;

        Reproducible(RowStatement.Stated stated, ValueTypes types, Position answers) {
            if (stated == null || types == null || answers == null) {
                throw new IllegalArgumentException("a row that can be asked states values, and is"
                        + " read with what the declarations say and where its answer stands");
            }
            this.stated = stated;
            this.types = types;
            this.answers = answers;
        }

        @Override
        public RowStatement.Stated states() {
            return stated;
        }

        /** Whether {@code answered} is what this row states the behavior answers. */
        public Verdict holds(ObservedValue answered) {
            if (answered == null) {
                throw new IllegalArgumentException("a row is held against an answer");
            }
            return souther.compiler.observe.Comparisons.verdict(stated.expects(), answered, types,
                    answers);
        }

        @Override
        public String toString() {
            return stated.toString();
        }
    }

    /**
     * A row that hands over no values, and what it says instead.
     *
     * <p>Here rather than left out. A row an output cannot reproduce is still a row someone wrote,
     * and one arriving as no row at all would have a reader count a set it never walked as one it
     * walked and found empty.
     */
    public record NotReproducible(RowStatement.NotStated why) implements Statement {

        public NotReproducible {
            if (why == null) {
                throw new IllegalArgumentException("a row that states no values says why");
            }
        }

        @Override
        public RowStatement states() {
            return why;
        }
    }

    @Override
    public String toString() {
        return identity.shown();
    }
}
