package souther.compiler.regex;

import java.util.List;

/**
 * A pattern of the subset this compiler reads, as what it says rather than as how it is written.
 *
 * <p>What is kept is what the language depends on and nothing else. A reading that dropped an arm of
 * a choice, an upper bound of a repetition, or the far end of a class would be a tree that answers
 * for a narrower language than the pattern names — and the answer would be wrong in the direction
 * nothing catches, since a narrower set still accepts the values somebody wrote.
 *
 * <p><b>No node for a literal.</b> One written character is one symbol, which is a set of one, and a
 * second shape for it would be two spellings of a thing that is compared. {@link Symbols} is where a
 * literal, a class, a negated class, a shorthand and {@code .} all arrive, told apart only by which
 * symbols they hold — which is the whole of what they say.
 *
 * <p>Nothing here is about matching. Where a repetition is greedy, whether a group captures, and
 * where an anchor is written say what an engine does and not which strings are accepted, so they
 * leave no trace: a whole-string match has nothing for an anchor to add, and a reluctant marker
 * changes the walk rather than the set.
 */
public sealed interface PatternSyntax {

    /** The one string of no symbols, which is what an empty branch of a choice accepts. */
    record Nothing() implements PatternSyntax {}

    /**
     * One symbol out of a set of them.
     *
     * <p>Every way of writing one character arrives here. `.` is the universe less the line
     * terminators, `[^a]` is the universe less one symbol, `\d` is the ten digits — what tells them
     * apart is the set, and a reader of this needs nothing else about how it was spelled.
     */
    record Symbols(CodePoints held) implements PatternSyntax {

        public Symbols {
            if (held == null) {
                throw new IllegalArgumentException("one symbol comes out of some set of them");
            }
        }
    }

    /** One after another. */
    record InTurn(List<PatternSyntax> parts) implements PatternSyntax {

        public InTurn {
            parts = List.copyOf(parts);
        }
    }

    /**
     * Any one of them.
     *
     * <p>Every arm and not the first. A reading that kept one arm answers for a language the author
     * did not write, and the ones it dropped are exactly the values a row may carry.
     */
    record EitherOf(List<PatternSyntax> arms) implements PatternSyntax {

        public EitherOf {
            arms = List.copyOf(arms);
            if (arms.size() < 2) {
                throw new IllegalArgumentException("a choice is between two or more");
            }
        }
    }

    /**
     * The same thing some number of times over.
     *
     * <p>Both ends carried. {@code {2,6}} is not {@code {2}} with something forgotten: the strings
     * of length three to six are in the language and a reading holding the floor alone leaves them
     * out. {@link #NO_CEILING} is what {@code *}, {@code +} and {@code {n,}} put there, which is a
     * bound nothing reaches rather than a large one.
     */
    record Repeated(PatternSyntax what, int least, int most) implements PatternSyntax {

        /** What an unbounded repetition has instead of a ceiling. */
        public static final int NO_CEILING = -1;

        public Repeated {
            if (what == null) {
                throw new IllegalArgumentException("something is repeated");
            }
            if (least < 0) {
                throw new IllegalArgumentException("a repetition happens at least no times");
            }
            if (most != NO_CEILING && most < least) {
                throw new IllegalArgumentException(
                        "a repetition's ceiling is not below its floor: " + least + ".." + most);
            }
        }

        public boolean unbounded() {
            return most == NO_CEILING;
        }
    }
}
