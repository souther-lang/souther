package souther.compiler.inputs;

/**
 * One number the rules reaching a behavior's input are about, in the words of the input rather than
 * of the value a rule was written on.
 *
 * <p>The rules relating a behavior's positions are read one parameter at a time, of the declaration
 * each parameter holds, and what they are about there are that declaration's own positions. Asked
 * about as rules of the input, they are about the same numbers under other names — so what is here
 * is the vocabulary those rules are carried into, and carrying them is a renaming
 * ({@link souther.compiler.numeric.NumericDomain#over}) rather than a second reading of them.
 *
 * <p><b>Two kinds, and the second is what keeps the carrying from widening.</b> A reading of a
 * declaration relates numbers the input has a term for and numbers it has none for, and a rule
 * reaching one of the latter still holds two of the former apart. Dropped on the way across, that
 * rule would be gone and what the rules leave would come back wider than it is — the one direction
 * nothing downstream can see. So a number the input cannot name is carried under a name of its own
 * and stays in the constraints, where it goes on relating what it relates and is never asked about.
 */
sealed interface InputAtom {

    /**
     * A number this input has a term for, which is what a caller asks about.
     *
     * <p>Held as where the number sits and which number of that place it is, and not as the term
     * itself. A term carries how the count was written — which standard-library measure was taken —
     * and that is a fact about the expression a rule was read out of rather than about the number:
     * held in the name, one number arriving from the declaration's reading and from a caller's form
     * would be two, and a rule about it would say nothing about the form that names it.
     *
     * @param parameter which of the behavior's inputs this sits under
     * @param path      the steps under that parameter, joined the way a coordinate joins them
     * @param measured  whether this is the count taken of the place rather than its own value. Two
     *                  numbers at one place, and a rule about one says nothing about the other
     */
    record Named(String parameter, String path, boolean measured) implements InputAtom {

        public Named {
            if (parameter == null || path == null) {
                throw new IllegalArgumentException("a named number sits somewhere");
            }
        }

        @Override
        public String toString() {
            String at = path.isEmpty() ? parameter : parameter + "." + path;
            return measured ? "|" + at + "|" : at;
        }
    }

    /**
     * A number one parameter's rules are about that this input has no term for.
     *
     * <p>Held by the reading's own subject, kept as something to be equal to and nothing more: what
     * makes two of these one number is what made the two subjects one, and that was settled where
     * the declaration was read. Nothing here reads it, and the type it is is not this layer's to
     * name — carried as anything else, two numbers of one reading would become one or one would
     * become two, and either way a rule would end up about a number nobody asked about.
     *
     * <p>The parameter is part of it because two parameters are read apart. One subject arriving
     * from two readings is two numbers, and without the parameter their rules would be put together
     * as rules about one.
     */
    record Anonymous(String parameter, Object subject) implements InputAtom {

        public Anonymous {
            if (parameter == null || subject == null) {
                throw new IllegalArgumentException(
                        "a number with no term of this input is still one parameter's");
            }
        }

        @Override
        public String toString() {
            return parameter + ":<" + subject + ">";
        }
    }
}
