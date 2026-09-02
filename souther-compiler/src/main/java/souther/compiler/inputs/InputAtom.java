package souther.compiler.inputs;

import souther.compiler.check.BoundaryClaim;
import souther.compiler.check.RuleKey;

/**
 * One subject the rules reaching a behavior's input are about, in the words of the input rather than
 * of the value a rule was written on.
 *
 * <p>A subject and not a number. What a rule is filed under reaches whichever reading has a word for
 * it — a relation between numbers, a bound on an order, the values a position may take, a predicate
 * about one — and all of those are carried across together, so what is here is the vocabulary of the
 * whole of what a reading came to. The distinctions below are drawn where the arithmetic needs them
 * and hold of the rest without being about it.
 *
 * <p>The rules relating a behavior's positions are read one parameter at a time, of the declaration
 * each parameter holds, and what they are about there are that declaration's own positions. Asked
 * about as rules of the input, they are about the same subjects under other names — so what is here
 * is the vocabulary those rules are carried into, and carrying them is a renaming
 * ({@link souther.compiler.check.ConstraintState#renamed}) rather than a second reading of them.
 *
 * <p><b>Two parameters cannot collide here, and that is this type's to guarantee.</b> Every one of
 * these carries the parameter it sits under, in both kinds, so two subjects arriving from two
 * parameters are two of these whatever the declarations called them — {@code x} of one record and
 * {@code x} of another are {@code p.x} and {@code q.x} and nothing has to check it. Which matters
 * because the readings are renamed one parameter at a time, each under a renaming of its own: what
 * holds inside one of them is that renaming's to refuse, and what holds between two of them is held
 * by these constructors and by nothing else.
 *
 * <p><b>Two kinds, and the second is what keeps the carrying from widening.</b> A reading of a
 * declaration is about subjects the input has a term for and subjects it has none for, and a rule
 * reaching one of the latter still holds two of the former apart. Dropped on the way across, that
 * rule would be gone and what the rules leave would come back wider than it is — the one direction
 * nothing downstream can see. So a subject the input cannot name is carried under a name of its own
 * and stays in the constraints, where it goes on relating what it relates and is never asked about.
 */
sealed interface InputAtom {

    /**
     * A subject this input has a term for, which is what a caller asks about.
     *
     * <p>Spelled as a place, which is what the arithmetic needs of the subjects it counts. What a
     * position is bounded to on its order and which values it may take are filed under the position
     * itself, so those cross under this name as well and under the same one as the number at it.
     *
     * <p>A predicate does not, and that is not this kind falling short. What a predicate is settled
     * about is the call that states it — {@code List.allDistinctBy(xs)} rather than {@code xs} — so
     * it is its own subject and crosses as {@link Anonymous}, where it goes on settling what it
     * settles without anybody out here having a term for it.
     *
     * <p>Held as where the number sits and which number of that place it is, and not as the term
     * itself. A term carries how the count was written — which standard-library measure was taken —
     * and that is a fact about the expression a rule was read out of rather than about the number:
     * held in the name, one number arriving from the declaration's reading and from a caller's form
     * would be two, and a rule about it would say nothing about the form that names it.
     *
     * @param root     the value whose rules name the place, which is the parameter where no
     *                 narrowing was taken and the case where one was. A field the cases of a sum
     *                 share is one place named by two of those, and it is this one — the nearest,
     *                 whose rules can name it — so that the rules of both arrive about one subject
     * @param path     what that value's own rules call the place
     * @param kind     whether this is the count taken of the place rather than its own value. Two
     *                 numbers at one place, and a rule about one says nothing about the other
     */
    record Named(String root, RuleKey path,
                 BoundaryClaim.OfWhatNumber kind) implements InputAtom {

        public Named {
            if (root == null || path == null) {
                throw new IllegalArgumentException("a named number sits somewhere");
            }
            java.util.Objects.requireNonNull(kind, "and is some number of what is there");
        }

        /**
         * Where the number sits, as a reader of this input spells a place.
         *
         * <p>Read here and not assembled by whoever needs it. A proof that names a place and the
         * rendering of a subject are the same spelling, and two of them would be one place written
         * two ways the day a step wears something.
         */
        String place() {
            return path.isTheValueItself() ? root : root + "." + path;
        }

        @Override
        public String toString() {
            String at = place();
            return switch (kind) {
                case BoundaryClaim.OfWhatNumber.OfItsOwnValue _ -> at;
                case BoundaryClaim.OfWhatNumber.OfWhatAnOperationAnswers taken ->
                        taken.operation() instanceof souther.compiler.types.ValueName.Stdlib named
                                ? named.qualified() + "(" + at + ")" : "|" + at + "|";
            };
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
    record Anonymous(String root, Object subject) implements InputAtom {

        public Anonymous {
            if (root == null || subject == null) {
                throw new IllegalArgumentException(
                        "a number with no term of this input is still one reading's");
            }
        }

        @Override
        public String toString() {
            return root + ":<" + subject + ">";
        }
    }
}
