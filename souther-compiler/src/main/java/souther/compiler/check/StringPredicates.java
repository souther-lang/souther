package souther.compiler.check;

import souther.compiler.ast.Hir;
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
 * answer for ({@code EveryStringPredicateIsReadAsASetOfStringsTest}), so a new one does not become
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
    public static souther.compiler.regex.PatternSyntax statedBy(Hir.Expr clause, Symbols symbols) {
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
}
