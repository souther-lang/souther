package souther.compiler.program;

/**
 * What {@link CheckedProgram#declaration} answers: where the declaration an identity names is, and
 * — where this snapshot holds it — what a value of it is made of.
 *
 * <p>Two arms and two questions, kept apart. Whether the snapshot holds the declaration is this
 * sum; who declared it is {@link DeclaredBy}, under the arm that holds one. Answered as one they
 * were the same question for as long as every declaration a body could name was one this compile
 * checked, and the day the language's own had to be reached the reader was left choosing which
 * owner to ask.
 *
 * <p>No arm for a name nothing declares. An identity comes from a declaration world having said one
 * is at an address, so a reader that assembled one from two strings is asking about something that
 * is not a declaration — and {@link CheckedProgram#declaration} refuses rather than answering, for
 * the reason {@link CheckedData.Product#positionOf} does. An arm for it would be an output handling
 * a mistake of its own as one of the states a checked program is in.
 */
public sealed interface Declared {

    /**
     * The declaration is here, and this is what a value of it is made of.
     *
     * <p>One arm for both worlds, which is what makes a language-declared sum and a module-declared
     * sum read the same way rather than by two readers agreeing to. A reader that only lays values
     * out takes {@link #data} and never looks at {@link #declaredBy}.
     */
    record Available(CheckedData data, DeclaredBy declaredBy) implements Declared {

        public Available {
            if (data == null || declaredBy == null) {
                throw new IllegalArgumentException(
                        "an available declaration is what it is made of and who declared it");
            }
        }
    }

    /**
     * The declaration is in a module this compile read off the path, and this snapshot does not
     * hold it.
     *
     * <p>Said because the compile resolved the identity against a module it read off the path, and
     * not because nothing else answered: a fourth way for a declaration to arrive would fall
     * through to being refused rather than being taken for this one. What such a declaration is
     * made of was decided when that module was compiled, and is in that compile's own snapshot.
     *
     * <p>It carries nothing. Which module it is, is on the identity the reader asked with.
     */
    record OnThePath() implements Declared {}
}
