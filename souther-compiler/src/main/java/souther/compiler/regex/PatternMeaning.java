package souther.compiler.regex;

import java.util.List;

/**
 * What a pattern means: the set of strings it accepts, as regular-language operations over sets of
 * scalar values.
 *
 * <p>The one form a pattern takes past its reader. {@link PatternParser} is the only thing that
 * reads a pattern's text, and what it hands on is this; the analysis, the compiler's own folds and
 * every output lower this and never read the text again. A second reader of the text would be a
 * second answer to which strings a pattern accepts, and the outputs would agree with each other only
 * as far as their readers happened to.
 *
 * <p>What is kept is what the language depends on and nothing else. A reading that dropped an arm of
 * a choice, an upper bound of a repetition, or the far end of a class would be a tree that answers
 * for a narrower language than the pattern names — and the answer would be wrong in the direction
 * nothing catches, since a narrower set still accepts the values somebody wrote.
 *
 * <p><b>No node for how it was written.</b> One written character is one symbol, which is a set of
 * one, and a second shape for it would be two spellings of a thing that is compared. {@link Symbols}
 * is where a literal, a class, a negated class, a shorthand and {@code .} all arrive, told apart only
 * by which symbols they hold. An anchor is gone too: whole-string matching settles what each one
 * comes to where the pattern is read, so none arrives here. Whether a repetition is greedy, whether a
 * group captures, and whether a marker is reluctant say what an engine does on the way rather than
 * which strings come out, so none of them is here either.
 *
 * <p>Which is why an output can take this as a contract. A new way of writing a set of symbols is a
 * change to the reader and arrives here as {@link Symbols}; nothing that lowers this learns of it.
 */
public sealed interface PatternMeaning {

    /** The one string of no symbols, which is what an empty branch of a choice accepts. */
    record Nothing() implements PatternMeaning {}

    /**
     * No string at all, which is not the same as the empty one.
     *
     * <p>What an anchor nobody can satisfy leaves. {@code a^b} asks for a position that is both
     * after an {@code a} and at the start of the string, and there is none — so the sequence
     * holding it accepts nothing, and a choice holding that sequence is its other arms.
     */
    record Never() implements PatternMeaning {}

    /**
     * One symbol out of a set of them.
     *
     * <p>Every way of writing one character arrives here. `.` is the universe less the line
     * terminators, `[^a]` is the universe less one symbol, `\d` is the ten digits — what tells them
     * apart is the set, and a reader of this needs nothing else about how it was spelled.
     */
    record Symbols(CodePoints held) implements PatternMeaning {

        public Symbols {
            if (held == null) {
                throw new IllegalArgumentException("one symbol comes out of some set of them");
            }
        }
    }

    /** One after another. */
    record InTurn(List<PatternMeaning> parts) implements PatternMeaning {

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
    record EitherOf(List<PatternMeaning> arms) implements PatternMeaning {

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
    record Repeated(PatternMeaning what, int least, int most) implements PatternMeaning {

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

    /**
     * The one string {@code written} is.
     *
     * <p>By code point and not by char, so a symbol outside the basic plane is one symbol here as
     * it is everywhere else in this package. Written as a sequence of one-symbol sets, which is
     * what a literal is ({@link Symbols}) — there is no node for a run of characters, and inventing
     * one would be a second spelling of a thing that is compared.
     */
    static PatternMeaning text(String written) {
        List<PatternMeaning> symbols = written.codePoints()
                .mapToObj(point -> (PatternMeaning) new Symbols(CodePoints.of(point)))
                .toList();
        return symbols.isEmpty() ? new Nothing() : new InTurn(symbols);
    }

    /**
     * Every string there is.
     *
     * <p>Every symbol and not what {@code .} holds. A dot is the universe less the line
     * terminators, which is a fact about how a pattern is written; what stands on either side of
     * text somebody looked for is any string at all, newlines included.
     */
    static PatternMeaning anything() {
        return ofAnySymbols(0, Repeated.NO_CEILING);
    }

    /**
     * Every string of between {@code least} and {@code most} symbols.
     *
     * <p>What a rule counting a string's characters leaves, said in the one vocabulary a language is
     * written in. A rule about how many there are and a rule about which they are reach one position
     * and are read by different things, and a value has to clear both — so whoever holds the count
     * puts it here and meets the two.
     *
     * <p>{@link Repeated#NO_CEILING} for a count nothing caps, which is the bound nothing reaches
     * rather than a large one.
     */
    static PatternMeaning ofAnySymbols(int least, int most) {
        return new Repeated(new Symbols(CodePoints.EVERYTHING), least, most);
    }
}
