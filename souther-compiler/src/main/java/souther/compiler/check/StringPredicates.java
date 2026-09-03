package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.core.Kernel;
import souther.compiler.regex.PatternParser;
import souther.compiler.regex.PatternRead;
import souther.compiler.regex.PatternSyntax;
import souther.compiler.types.ValueName;

import java.util.List;

/**
 * A library predicate over a string, as the strings it accepts.
 *
 * <p>The one place a call is read as a set of strings. What {@code String.contains("市", value)}
 * says about the position it names is which strings stand there — the same kind of answer
 * {@code String.matches} gives and the same kind this compiler already knows how to hold, since a
 * language over code points is what {@link souther.compiler.regex} is. Read one spelling at a time
 * instead, {@code matches} was a set of strings and the predicates beside it were forms nothing
 * took apart, so a position an author had written a rule for admitted every string there is — and a
 * value nobody could compose there took its siblings' obligations down with it.
 *
 * <p><b>Keyed by what the operation means and not by how a rule is written.</b> Each entry says
 * which argument carries the position, which carries the text, and what the strings around that
 * text may be. A predicate added to the library is a row here or is named as one this does not
 * answer for ({@code EveryPredicateOverAStringIsReadAsASetOfStringsTest}), so a new one does not become
 * a rule that quietly says nothing.
 *
 * <p><b>One clause, one reading, handed on.</b> What a clause states is worked out once, by the
 * entry point its tree has, and comes back as a {@link Reading} that holds what became of it — the
 * strings, or what stopped the reading short of them. A caller takes that value rather than going
 * back to the clause to establish a second time what it already has: asking twice is one question
 * with two derivations, and the day either the fold or the parser learns a form is the day they
 * part.
 *
 * <p><b>And what it says about a position is nobody's answer here.</b> The strings are a fact about
 * a language. Whether the position those strings stand at is restricted, divided, or left where it
 * was found turns on what the rule is written in, and it is settled by the reading that holds every
 * rule reaching the position — so this hands over the strings and stops. Answered here, the same
 * language would mean one thing under an invariant, whose other side is refused at construction, and
 * another under a behavior, where both sides stand.
 *
 * <p>{@code String.isEmpty} is not here, and is not missing. It is written in the library as
 * {@code String.length(s) == 0} and arrives as that comparison, which is a question about a number
 * and is answered where numbers are.
 */
public enum StringPredicates {

    /**
     * The strings a written pattern accepts.
     *
     * <p>The one entry whose text is not text: it is a pattern, and what it accepts is what reading
     * it comes to rather than anything composed here. So it has no shape below, and it is the only
     * entry a reading can stop short of, which is where a pattern this compiler cannot take apart is
     * said to be one.
     */
    MATCHES(Kernel.STRING_MATCHES, null),

    /** The strings that hold the written one somewhere. */
    CONTAINS(Kernel.STRING_CONTAINS, written -> new PatternSyntax.InTurn(List.of(
            PatternSyntax.anything(), PatternSyntax.text(written), PatternSyntax.anything()))),

    /** The strings that begin with it. */
    STARTS_WITH(Kernel.STRING_STARTS_WITH, written -> new PatternSyntax.InTurn(List.of(
            PatternSyntax.text(written), PatternSyntax.anything()))),

    /** The strings that end with it. */
    ENDS_WITH(Kernel.STRING_ENDS_WITH, written -> new PatternSyntax.InTurn(List.of(
            PatternSyntax.anything(), PatternSyntax.text(written))));

    /** What the strings around the written text may be, or null where the text is a pattern. */
    private interface Around {
        PatternSyntax accepting(String written);
    }

    private final Kernel kernel;
    private final Around around;

    StringPredicates(Kernel kernel, Around around) {
        this.kernel = kernel;
        this.around = around;
    }

    /** Which library operation this is. */
    public Kernel kernel() {
        return kernel;
    }

    /**
     * How many arguments the call has.
     *
     * <p>All four take the text first and the subject second, which is the library's own order
     * ({@code String.contains(sub, s)}). Written per entry it would be four chances to disagree
     * with the library about a signature nothing here declares.
     */
    public int arity() {
        return 2;
    }

    /** Which argument names the position the rule is about. */
    public int subject() {
        return 1;
    }

    /** Which argument carries what the author wrote. */
    public int written() {
        return 0;
    }

    /** Whether what is written is a pattern rather than text to be looked for. */
    public boolean takesAPattern() {
        return around == null;
    }

    /**
     * The strings this predicate accepts of a position, given the text written in it.
     *
     * <p>Never asked of {@link #MATCHES}: what a pattern accepts is what reading the pattern comes
     * to, and a caller holding one has already read it.
     */
    public PatternSyntax accepting(String written) {
        if (around == null) {
            throw new IllegalStateException(
                    this + " states a pattern, and what it accepts is the pattern's");
        }
        return around.accepting(written);
    }

    /** The one this kernel is, or null where it is no predicate over strings read here. */
    public static StringPredicates of(Kernel kernel) {
        for (StringPredicates each : values()) {
            if (each.kernel == kernel) {
                return each;
            }
        }
        return null;
    }

    /**
     * What became of reading one predicate as the strings it admits.
     *
     * <p>Kept whole because the reading has readers that want different parts of it. What a rule
     * admits is one answer; that the reading stopped, and at what, is another; and a reader handed
     * only the first would ask for the second by reading the clause again. Which of these
     * distinctions reaches an author is the reader's to settle — what is settled here is that
     * nothing was thrown away before it could.
     */
    public sealed interface Reading {

        /** The strings the predicate admits at the position it is about. */
        record Accepting(PatternSyntax accepts) implements Reading {

            public Accepting {
                if (accepts == null) {
                    throw new IllegalArgumentException(
                            "a reading that finished says which strings it accepts");
                }
            }
        }

        /**
         * A pattern it states that this reads no further into, and what stopped the reading.
         *
         * <p>Only an entry whose text is a pattern arrives here. One that composes what it accepts
         * out of text has nothing in that to be stopped by.
         */
        record PatternNotRead(PatternRead.Unsupported why) implements Reading {

            public PatternNotRead {
                if (why == null) {
                    throw new IllegalArgumentException(
                            "a pattern nothing read was stopped by something");
                }
            }
        }

        /**
         * The predicate is one of these, and what the author wrote in it is not a string this
         * compiler works out.
         *
         * <p>A rule read as far as the call and no further, which is not the same as a clause that
         * is no predicate of this kind — there a reader has nothing to say, and here it has a
         * position with a rule on it that nothing here turned into strings.
         */
        record WrittenArgumentNotKnown() implements Reading {}
    }

    /**
     * A checked clause's predicate: the argument the rule is about, and what reading it came to.
     *
     * @param subject the argument the rule is about, for a caller that resolves it to a position
     * @param reading what this compiler made of the strings the predicate states there
     */
    public record Stated(Core subject, Reading reading) {

        public Stated {
            if (subject == null || reading == null) {
                throw new IllegalArgumentException(
                        "a predicate that was stated is about something and was read");
            }
        }
    }

    /**
     * What this predicate says, given the text written in it.
     *
     * <p>The whole of the reading, and the one copy of it. What each tree does for itself is reach
     * the call and work out the text — {@code ConstEval} on one side, {@link Terms#folded} on the
     * other — and from that text onwards there is a single answer, so a construct the subset learns
     * is learned by both at once.
     */
    private Reading readingOf(String written) {
        if (!takesAPattern()) {
            return new Reading.Accepting(accepting(written));
        }
        return switch (PatternParser.read(written)) {
            case PatternRead.Read read -> new Reading.Accepting(read.syntax());
            case PatternRead.NotRead not -> new Reading.PatternNotRead(not.why());
        };
    }

    /**
     * What one written clause says about the value it is about, or null where it is no predicate of
     * this kind.
     *
     * <p>Off the written tree, for the readers that hold one — what a declaration's rules propose a
     * value from is walked before a body is checked, and there is no {@link Core} there to ask. What
     * it is <em>not</em> is a second table: which operations are predicates over strings and what
     * each says is above, and both readers take that from there.
     *
     * <p>About the value the newtype carries and not about any position: a caller here is looking at
     * the clauses of one declaration, where {@code value} is what the rule is about, so which
     * argument carries the subject is checked and nothing is resolved through it.
     *
     * <p>A call of another number of arguments is no statement of this kind, the same as a call of
     * another operation. This reads the tree a body is checked from, where an application is typed
     * against what it names but a malformed one has not yet been refused.
     */
    public static Reading statedByWritten(Hir.Expr clause, Symbols symbols) {
        if (!(clause instanceof Hir.Apply call) || call.answered() == null) {
            return null;
        }
        StringPredicates predicate = call.answered().denotes()
                instanceof ValueName.Stdlib.Operation operation
                ? of(symbols.kernelOf(operation)) : null;
        if (predicate == null || call.args().size() != predicate.arity()) {
            return null;
        }
        String written = ConstEval.against(symbols)
                .evalString(call.args().get(predicate.written())).orElse(null);
        return written == null
                ? new Reading.WrittenArgumentNotKnown() : predicate.readingOf(written);
    }

    /**
     * The same off a checked clause, or null where it is no predicate of this kind.
     *
     * <p>Beside {@link #statedByWritten} and in the same file on purpose. One question — which
     * operations say which strings stand at a position — and two trees to ask it of: a declaration's
     * rules are walked before a body is checked and hold no {@link Core}, and the reading of what a
     * position admits holds nothing else. Two entry points and one table, so a predicate learned is
     * learned by both.
     *
     * <p><b>Two folds, and that is the whole of the difference.</b> What the author wrote is reached
     * through the folder each tree has, and they are not the same code — so a written argument one of
     * them folds and the other does not is a rule one reader takes in and the other passes over,
     * which is the shape this arrangement exists to stop. They are adjacent here so that the next
     * person to change one sees the other. Everything past the text they hand over is
     * {@link #readingOf} and is one.
     *
     * <p>A call of another number of arguments is refused rather than read as no predicate. A call
     * standing for one of these operations is an application that was typed against the signature
     * it names, where its arity was settled, so one arriving here with another number of arguments
     * says the table above and the library have come to disagree — read as no predicate, that
     * disagreement would go on quietly costing every rule written with this operation.
     */
    public static Stated statedByChecked(Core clause, Symbols symbols) {
        if (!(clause instanceof Core.PreservedCall call)
                || !(call.operation() instanceof ValueName.Stdlib.Operation operation)) {
            return null;
        }
        StringPredicates predicate = of(symbols.kernelOf(operation));
        if (predicate == null) {
            return null;
        }
        if (call.args().size() != predicate.arity()) {
            throw new IllegalStateException(predicate + " is read as a call of " + predicate.arity()
                    + " arguments and the library declares one of " + call.args().size());
        }
        Core subject = call.args().get(predicate.subject());
        return Terms.folded(call.args().get(predicate.written()), symbols) instanceof String written
                ? new Stated(subject, predicate.readingOf(written))
                : new Stated(subject, new Reading.WrittenArgumentNotKnown());
    }

}
