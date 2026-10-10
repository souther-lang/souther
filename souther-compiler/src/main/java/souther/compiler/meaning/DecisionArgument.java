package souther.compiler.meaning;

import souther.compiler.numeric.ExactRatio;

/**
 * What a dependency was asked about, as what tells two askings apart.
 *
 * <p>Beside {@link DecisionSubject} and not the same question. A subject is what a row controls —
 * what it writes a value at, or stands a dependency in for — and that is what makes a distinction
 * one an author can write a row against. An argument does not have to be controlled to be known: a
 * body asking one dependency about a number it wrote asks one question, however many times it
 * writes it, and the answer is the same answer.
 *
 * <p>Held as one type, a call about anything a row does not control had no identity at all, so two
 * askings about one written number were two columns of a table that tells them apart nowhere — the
 * occurrence doing identity's work, which is what a decision column exists to stop.
 *
 * <p>And an argument that is neither is a value the model works out, named by how it is worked out
 * ({@link WorkedOut}). The answer is one a row stands in all the same: a row asks the dependency
 * the same thing however that value was spelled, and the evaluation is what tells it from every
 * other answer.
 */
public sealed interface DecisionArgument {

    /** What this argument is, as an identity spells it. */
    String spelled();

    /** Something a row controls: a position it writes at, or an answer it stands in for. */
    record OfASubject(DecisionSubject subject) implements DecisionArgument {

        public OfASubject {
            if (subject == null) {
                throw new IllegalArgumentException("an argument of a subject is some subject");
            }
        }

        @Override
        public String spelled() {
            return subject.spelled();
        }

        @Override
        public String toString() {
            return spelled();
        }
    }

    /**
     * A value the model works out of what a row controls and what the source wrote, named by how it
     * is worked out: the expression, with each name in it written as what it stands for where the
     * dependency was asked — a position or an answer as the subject it is, a value handed or given as
     * that value.
     *
     * <p>A row stands the dependency in whatever it was asked, and which evaluation it is tells the
     * answer from every other ({@link InjectedAnswer}); so what this has to do is name the question
     * and not tell evaluations apart. Two askings in one evaluation that are two questions — a closure
     * handed each of the values a list was written with — differ in a value a name stands for, and
     * so in how it is spelled here.
     */
    record WorkedOut(String spelled) implements DecisionArgument {

        public WorkedOut {
            if (spelled == null || spelled.isEmpty()) {
                throw new IllegalArgumentException("a value worked out is worked out some way");
            }
        }

        @Override
        public String toString() {
            return spelled;
        }
    }

    /**
     * A number the model settles, whoever runs it.
     *
     * <p>The value and not what was written: {@code 42} and an expression this compiler folds to
     * {@code 42} ask one question, and a column apiece for them would be the spelling telling them
     * apart.
     */
    record OfANumber(ExactRatio value) implements DecisionArgument {

        public OfANumber {
            if (value == null) {
                throw new IllegalArgumentException("a number argument is some number");
            }
            // The value as the arithmetic compares it, which an exact ratio already is: it is kept
            // in lowest terms, so `42` and `42.0` are one argument for the reason they are one
            // number.
        }

        @Override
        public String spelled() {
            return value.spelled();
        }

        @Override
        public String toString() {
            return spelled();
        }
    }
}
