package souther.compiler.partition;

/**
 * Why a generation did not offer everything it might have.
 *
 * <p>Apart from {@code Incompleteness}, which says what a measurement could not read. These say what
 * the generator did about that, and the two are not the same taxonomy: a value that could not be read
 * is a fact about the rows, and a position left out of the offer is a decision taken because of it.
 * Held as one vocabulary, the decision borrowed the name of the cause and a reader could not tell a
 * generation that ended from one that went on without a position.
 *
 * <p>That difference is the whole of what a reader of a generated block needs and could not get. A
 * block that says it stopped, above rows it is offering, is telling an author both that there is work
 * here and that there is none.
 */
public sealed interface GenerationReason {

    /** Whether the generation ended here, as against carrying on with less. */
    boolean stopped();

    /**
     * A position no work was offered at, because some row's value there could not be read.
     *
     * <p>The generation went on without it. A row written for a class at a position nothing is known
     * about may be a row that is already there, and telling an author to write one is worse than
     * saying nothing: it is a specific piece of work that is already done.
     */
    record PositionWithheld(AxisId axis) implements GenerationReason {

        @Override
        public boolean stopped() {
            return false;
        }
    }

    /**
     * Rows exist that nothing read, so nothing was offered at all.
     *
     * <p>What is left uncovered cannot be worked out from rows that were not read, and a generated
     * row is a specific piece of work handed to a person — one that may already be sitting in the
     * file that could not be evaluated.
     *
     * <p>Carries what the measurement could not read, because that is the evidence this decision
     * rests on and a person holding only the generated block has nowhere else to find it. The
     * decision and the evidence are different things and this keeps them so.
     */
    record RowsNotRead(String behavior, java.util.List<souther.compiler.observe.Incompleteness> because)
            implements GenerationReason {

        public RowsNotRead {
            because = java.util.List.copyOf(because);
        }

        @Override
        public boolean stopped() {
            return true;
        }
    }

    /** The search ended before it had covered everything, with this many combinations left. */
    record SearchLimit(String behavior, int combinations) implements GenerationReason {

        @Override
        public boolean stopped() {
            return true;
        }
    }

    /**
     * Nothing could be built to try, so the generation never began.
     *
     * <p>Named for what the generator met and not for what raised it: the classes it would have put
     * candidates through would not link, and which of the things that raise a {@code LinkageError}
     * happened is not something anything here can tell.
     */
    record ClassesWouldNotLink(String behavior) implements GenerationReason {

        @Override
        public boolean stopped() {
            return true;
        }
    }
}
