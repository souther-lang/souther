package souther.compiler.types;

/**
 * What a value turns out to be once a case has been selected: which carrier is tested for, and what
 * stands under it.
 *
 * <p>Written by whoever builds a {@link CaseSelector} and read by everything downstream. Which of
 * these a case takes is decided once, where the cases of a subject are worked out, so no later stage
 * asks whether a subject is an optional, whether an arm named one case or several, or whether a case
 * is a primitive. Those questions have one answer each and it is recorded here.
 *
 * <p>The arms are the carriers the language has, named as the carriers they are. An earlier reading
 * of this called them for what they hold — one that is the value, one that wraps it, one that holds
 * nothing — which reads as a general account of carriers and is not one: the wrapping arm is an
 * optional's present carrier and the empty arm is its absent one, and a reader emitting either
 * writes {@code Option}'s classes. Saying so is what keeps a second carrier, when the language gains
 * one, from arriving as a case of a word that already means something narrower.
 */
public sealed interface Refinement {

    /** What the case binds, or null where nothing readable stands under the carrier. */
    Type bound();

    /**
     * The carrier is the value: the case's own class is what is tested, and the value read is that
     * class's instance — a declared data as its own type, a primitive-named case (the {@code Int} of
     * {@code Int | DivisionByZero}) as that primitive.
     *
     * <p>{@code bound} is null for a case that denotes no type at all, which is what a name outside
     * the spelling table answers; nothing readable stands under such a carrier either.
     */
    record Direct(Type bound) implements Refinement {}

    /** An optional's present carrier, under which its element stands. */
    record OptionPresent(Type bound) implements Refinement {
        public OptionPresent {
            if (bound == null) {
                throw new IllegalArgumentException("a present optional holds its element");
            }
        }
    }

    /** An optional's absent carrier, which has nothing under it. */
    record OptionAbsent() implements Refinement {

        @Override
        public Type bound() {
            return null;
        }
    }
}
