package souther.compiler.check;

/**
 * What the invariant-discharge check calls a value, or why it calls it nothing.
 *
 * <p>Every expression gets one of these. The check used to answer with a term or with {@code null},
 * and the null said two things at once: that the value is one a guard could never be written about,
 * and that this compiler has no term for the shape it was written in. The first is what the check
 * is; the second is what it has not finished being, and reading it as the first is how a construction
 * over a recursive helper's answer came out silent — the same construction over the same helper
 * written without recursion was a warning, because that one was expanded and this one was a call
 * nothing here had a case for (#722).
 *
 * <p>A third silence is beside these and not among them. Whether an analysis ran to the end is a
 * fact about the analysis and not about any value in it ({@link InvariantChecker.Status}), so it is
 * held where analyses are and not here: an answer about a value and an answer about a walk are not
 * two values of one question, and folding them together is how one of them stops being asked.
 *
 * <p>So the two are apart. {@link Opaque} is this check's own semantics: what an injected behavior
 * answered is a different value each time it is asked, and a function value a body applies may be
 * one. {@link Unsupported} is not a state a compile should reach — the classification is a
 * {@code switch} over {@link souther.compiler.core.Core} with no default, so a shape added later
 * stops the build rather than arriving here — and where it does arrive it says which shape, so that
 * what is missing is a name and not a silence.
 */
sealed interface Naming {

    /** The term, or {@code null} where this names nothing. */
    Term term();

    /** The value, as the term standing for it. */
    record Named(Term term) implements Naming {

        public Named {
            // A name and no term is the state this type exists to make unwritable: it is what the
            // `null` this replaced meant at one of the places it was returned from.
            java.util.Objects.requireNonNull(term, "a named value is named by a term");
        }
    }

    /** Everything that is not a name. */
    sealed interface Unnamed extends Naming {

        @Override
        default Term term() {
            return null;
        }
    }

    /** A value this check cannot name, and the reason it cannot. */
    record Opaque(Reason reason) implements Unnamed {}

    /** A shape this check has no term for, which is this compiler being unfinished rather than a
     * value being unnameable. {@code form} names the shape. */
    record Unsupported(String form) implements Unnamed {}

    /** Why a value is one nothing here can name. */
    enum Reason {

        /** What a behavior answered (spec §invariant-discharge-terms). Where the behavior is one
         * injected from outside, its implementation is not the language's and may read the outside
         * world, so two asks are two answers (spec §injected-behavior). */
        A_BEHAVIOR_ANSWERED,

        /** What applying a function value answered. What is applied is whatever the binding holds,
         * and a body may be handed an injected behavior as one (spec §depends-on). */
        A_FUNCTION_VALUE_WAS_APPLIED,

        /** An expression that answers with no value at all. */
        NOTHING_IS_ANSWERED,

        /** A binding nothing entered: a value the walk never reached, so there is nothing it stands
         * for here. */
        A_BINDING_STANDS_FOR_NOTHING,

        /** A part of it is one of these. Which part and why is the part's own answer; a value is
         * named all the way down or not at all. */
        A_PART_NAMES_NOTHING
    }

    /** {@code term}, or the reason there is none. */
    static Naming of(Term term, Reason absent) {
        return term == null ? new Opaque(absent) : new Named(term);
    }

    /**
     * Whether what a name answers is a value two writings of it share, and why it is not where it is
     * not.
     *
     * <p>Apart from {@link Naming} because it is asked of a name rather than of an expression: what
     * a call to a nameable one is called is built from the call's arguments, which the name knows
     * nothing about. Answering this with a {@link Named} holding no term would be the state {@link
     * Named} exists to rule out, and answering it with a {@code boolean} would drop the reason the
     * other side of it carries.
     */
    sealed interface OfAName {

        /** It answers one value wherever it is written with the same arguments. */
        record Answers() implements OfAName {}

        /** It does not, for {@code reason}. */
        record AnswersNothing(Reason reason) implements OfAName {}
    }
}
