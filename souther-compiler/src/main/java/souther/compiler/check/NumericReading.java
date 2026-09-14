package souther.compiler.check;

import souther.compiler.numeric.LinearForm;
import souther.compiler.semantics.NumericResult;
import souther.compiler.semantics.TakenAs;

/**
 * A representation that reads the number an operation answers.
 *
 * <p>What is read and not who reads it. Each of these stands for an account under which the number
 * a call answers is understood, and the account is what a reader of any kind takes: a partition
 * drawing a boundary and a discharge procedure keying an atom take the same one, which is what
 * makes two of them at one call a disagreement rather than two opinions.
 *
 * <p>Sealed, and the arms are the accounts there are. A fifth is added here, and the exclusivity
 * between it and each of the four is then stated nowhere — {@link NumericReadings} counts what it
 * finds, so an operation carrying the new account beside an old one is two readings without anybody
 * writing the pair down. That is the whole of why this is a sum and not four predicates asked in
 * turn.
 */
sealed interface NumericReading {

    /** What this reads the number as, for a message naming the readings an operation has. */
    String describes();

    /**
     * The number is taken of the one value the operation is given, and {@code how} is the account of
     * what is taken.
     *
     * <p>Carried whole rather than as the fact that there is one. What holds a declaration of this
     * kind has to say that the account it is holding is the account that was found, and an arm that
     * said only "a term" could not: the two would be compared by there being one of each.
     */
    record AsATermTakenOfItsArgument(TakenAs how) implements NumericReading {

        public AsATermTakenOfItsArgument {
            java.util.Objects.requireNonNull(how, "this one says what the number is taken as");
        }

        @Override
        public String describes() {
            return "a term of what it answers";
        }
    }

    /** The number is arithmetic over what the arguments are counted as, and {@code form} is that
     *  arithmetic. */
    record AsAFormOfItsArguments(LinearForm<DeclaredArgument> form)
            implements NumericReading {

        public AsAFormOfItsArguments {
            java.util.Objects.requireNonNull(form, "this one says what it answers");
        }

        @Override
        public String describes() {
            return "a form of its arguments";
        }
    }

    /** The number is the arithmetic the operation computes, and {@code result} says which and where
     *  it is answered. */
    record AsTheArithmeticItComputes(NumericResult<DeclaredArgument> result)
            implements NumericReading {

        public AsTheArithmeticItComputes {
            java.util.Objects.requireNonNull(result, "this one says what it computes");
        }

        @Override
        public String describes() {
            return "the arithmetic it computes";
        }
    }

    /**
     * The operation is written in the language, so what it answers is read by reading its body.
     *
     * <p>Nothing to carry: the body is the library's and is read where the call is. What this says
     * is that reading it is already an account of the number, so a second one written beside it
     * would be two readings of one call — {@code Int.abs} is an ordinary {@code let} over
     * {@code <} and {@code -}, and a term standing for the call would draw a line the definition
     * already draws.
     *
     * <p>Derived and not declared, which is what keeps it from going stale. An operation rewritten
     * from a {@code let} into an intrinsic loses this reading in the same commit that rewrites it,
     * rather than when somebody remembers a table.
     */
    record ByTheBodyTheLanguageWritesOut() implements NumericReading {

        @Override
        public String describes() {
            return "the body the language writes out";
        }
    }
}
