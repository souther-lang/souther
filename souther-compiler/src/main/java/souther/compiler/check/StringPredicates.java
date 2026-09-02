package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.core.Kernel;
import souther.compiler.regex.PatternSyntax;

import java.util.List;

/**
 * A library predicate over a string, as the strings it accepts.
 *
 * <p>The one place a call is read as a set of strings. What {@code String.contains("市", value)}
 * says about the position it names is which strings stand there — the same kind of answer
 * {@code String.matches} gives and the same kind this compiler already knows how to hold, since a
 * language over code points is what {@link souther.compiler.regex} is. Read one spelling at a time
 * instead, {@code matches} was a set of strings and the four beside it were forms nothing took
 * apart, so a position an author had written a rule for admitted every string there is — and a
 * value nobody could compose there took its siblings' obligations down with it (issue #1249).
 *
 * <p><b>Keyed by what the operation means and not by how a rule is written.</b> Each entry says
 * which argument carries the position, which carries the text, and what the strings around that
 * text may be. A predicate added to the library is a row here or is named as one this does not
 * answer for ({@code EveryPredicateOverAStringIsReadAsASetOfStringsTest}), so a new one does not become
 * a rule that quietly says nothing.
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
     * it comes to rather than anything composed here. So it has no shape below and the caller reads
     * it, which is also where a pattern this compiler cannot take apart is said to be one.
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
     * The strings one written clause admits at the value it is about, or null where it is no
     * predicate of this kind or what it names could not be read.
     *
     * <p>Off the written tree, for the readers that hold one — what a declaration's rules propose a
     * value from is walked before a body is checked, and there is no {@link souther.compiler.core.Core}
     * there to ask. What it is <em>not</em> is a second table: which operations are predicates over
     * strings and what each says is above, and both readers take that from there.
     *
     * <p>About the value the newtype carries and not about any position: a caller here is looking at
     * the clauses of one declaration, where {@code value} is what the rule is about, so which
     * argument carries the subject is checked and nothing is resolved through it.
     */
    public static souther.compiler.regex.PatternSyntax statedByWritten(Hir.Expr clause,
                                                                     Symbols symbols) {
        if (!(clause instanceof Hir.Apply call) || call.answered() == null) {
            return null;
        }
        StringPredicates predicate = call.answered().denotes()
                instanceof souther.compiler.types.ValueName.Stdlib.Operation operation
                ? of(symbols.kernelOf(operation)) : null;
        if (predicate == null || call.args().size() != predicate.arity()) {
            return null;
        }
        String written = ConstEval.against(symbols)
                .evalString(call.args().get(predicate.written())).orElse(null);
        if (written == null) {
            return null;
        }
        if (!predicate.takesAPattern()) {
            return predicate.accepting(written);
        }
        return souther.compiler.regex.PatternParser.read(written)
                instanceof souther.compiler.regex.PatternRead.Read read ? read.syntax() : null;
    }

    /**
     * What one checked clause says, and about which of its arguments.
     *
     * @param subject the argument the rule is about, for a caller that resolves it to a position
     * @param accepts the strings the predicate admits there, or null where the pattern it states is
     *                one this compiler reads no further into
     */
    public record Stated(Core subject, souther.compiler.regex.PatternSyntax accepts) {}

    /**
     * The same off a checked clause, or null where it is no predicate of this kind.
     *
     * <p>Beside {@link #statedByWritten} and in the same file on purpose. One question —
     * which operations say which strings stand at a position — and two trees to ask it of: a
     * declaration's rules are walked before a body is checked and hold no {@link Core}, and the
     * reading of what a position admits holds nothing else. Two entry points and one table, so a
     * predicate learned is learned by both.
     *
     * <p><b>Two folds, and that is the part to watch.</b> What the author wrote is read through the
     * folder each tree has, and they are not the same code — so a written argument one of them folds
     * and the other does not is a rule one reader takes in and the other passes over, which is the
     * shape this whole arrangement exists to stop. They are adjacent here so that the next person to
     * change one sees the other.
     */
    public static Stated statedByChecked(Core clause, Symbols symbols) {
        if (!(clause instanceof Core.PreservedCall call)
                || !(call.operation() instanceof souther.compiler.types.ValueName.Stdlib.Operation
                        operation)) {
            return null;
        }
        StringPredicates predicate = of(symbols.kernelOf(operation));
        if (predicate == null || call.args().size() != predicate.arity()) {
            return null;
        }
        if (!(Terms.folded(call.args().get(predicate.written()), symbols) instanceof String written)) {
            return null;
        }
        Core subject = call.args().get(predicate.subject());
        if (!predicate.takesAPattern()) {
            return new Stated(subject, predicate.accepting(written));
        }
        // A pattern written more deeply than this reads is a limit of the reading and not a shape it
        // has no word for, so the caller is handed the subject with nothing accepted and says that
        // as itself. Left to look like no predicate at all, an author would go looking for the
        // construct that was the trouble, when every construct in it is one this reads.
        souther.compiler.regex.PatternRead said =
                souther.compiler.regex.PatternParser.read(written);
        return new Stated(subject, said instanceof souther.compiler.regex.PatternRead.Read read
                ? read.syntax() : null);
    }

    /**
     * What a predicate's strings come to at the position it is about.
     *
     * <p>Read and divides are two questions, and one had been standing in for the other. A rule is
     * read as a set of strings whether that set is some of them, all of them or none — and only the
     * first is a division, so only the first is a position divided in a way no order carries. Asked
     * as "was it read", {@code String.contains("", value)} came out as a position divided into
     * values this measure draws no line between, and it makes no distinction at all.
     *
     * <p>Off the set and never off what was written. Whether the strings are all of them is a fact
     * about the language, and a caller looking at the text for an empty one would be back to
     * deciding meaning from a spelling — the thing that made {@code contains} unreadable in the
     * first place (issue #1249).
     */
    public sealed interface Divides {

        /** Some strings and not others, which is a division and is not one an order holds. */
        record IntoTwo() implements Divides {}

        /** Every string there is, so the rule tells no value here from another. */
        record NothingIsRuledOut() implements Divides {}

        /** No string at all, so the rules leave no value here — which is not a division either. */
        record NothingIsLeft() implements Divides {}

        /**
         * This compiler could not build the machine, so it could not tell which of the three.
         *
         * <p>Its own answer and never one of the others. A limit read as "no division" would be a
         * claim about the model made out of an allowance running down, which is the shape this
         * whole reading exists to stop.
         */
        record CouldNotTell() implements Divides {}
    }

    /**
     * What {@code clause} divides the position it is about into, or null where it is no predicate
     * of this kind or where the reading of it did not finish.
     *
     * <p>The machine is built here because the question is about the strings and there is no other
     * way to ask it. What it costs is one language per clause of this kind, under the allowance one
     * value is written from — the shapes composed above are a few states, and a pattern larger than
     * that allowance is the one case that comes back unable to tell.
     */
    public static Divides divides(Core clause, Symbols symbols) {
        Stated stated = statedByChecked(clause, symbols);
        if (stated == null || stated.accepts() == null) {
            return null;
        }
        souther.compiler.regex.Language strings = souther.compiler.regex.PatternPlan
                .of(stated.accepts())
                .compile(souther.compiler.regex.PatternPlan.Budget.OF_A_WITNESS);
        if (strings == null) {
            return new Divides.CouldNotTell();
        }
        if (strings.isEmpty()) {
            return new Divides.NothingIsLeft();
        }
        return strings.isEverything() ? new Divides.NothingIsRuledOut() : new Divides.IntoTwo();
    }

    /**
     * Whether a pattern this could not take apart is one it read too little of rather than one it
     * has no word for.
     *
     * <p>Asked of the same reading the caller's {@link Stated} came from, so that the two answers
     * are one reading of one pattern.
     */
    public static boolean readTooLittleOf(Core clause, Symbols symbols) {
        if (!(clause instanceof Core.PreservedCall call)
                || !(call.operation() instanceof souther.compiler.types.ValueName.Stdlib.Operation
                        operation)) {
            return false;
        }
        StringPredicates predicate = of(symbols.kernelOf(operation));
        return predicate != null && predicate.takesAPattern()
                && call.args().size() == predicate.arity()
                && Terms.folded(call.args().get(predicate.written()), symbols) instanceof String it
                && souther.compiler.regex.PatternParser.read(it)
                        instanceof souther.compiler.regex.PatternRead.NotRead why
                && why.why() == souther.compiler.regex.PatternRead.Unsupported.NESTED_TOO_DEEPLY;
    }
}
