package souther.compiler.inputs;

import souther.compiler.types.BindingId;

import java.util.Objects;

/**
 * What a walk over the binding graph may do at one binding, for the question it is asking.
 *
 * <p>Three answers and not a binding or nothing. Two of them leave the walk with nowhere to go on
 * to, and they license opposite things. Where nothing was recorded, what the binding holds is all
 * there is to read and reading it is how a container bound to a value is followed. Where an edge
 * says this binding's elements were made from another's, a walk after which position a value
 * <em>is</em> has been told to stop — and the value under such a name is the very thing it was told
 * to stop before, since a rewrite that joins two walks binds the second's element to what the
 * first's closure made.
 *
 * <p><b>Which is why the refusal is a value.</b> Answered as an absent binding beside the other, a
 * stop is read as "nothing here" and the walk looks elsewhere: it reaches the position the earlier
 * walk read, and a rule about a value made from a position comes back as a rule about that position.
 * There is no spelling of "no binding" that carries the difference, so it is carried by which answer
 * this is.
 */
public sealed interface ElementStep {

    /** Go on to {@code binding}: what this one's elements are, this question may read there. */
    record Through(BindingId binding) implements ElementStep {

        public Through {
            Objects.requireNonNull(binding, "a step goes to a binding");
        }
    }

    /**
     * There is an edge and this question does not cross it, so the walk stops here.
     *
     * <p>A fact about the model as much as a position that names none is: what was made from these
     * values is not these values, and no other road reaches them either.
     */
    record Refused() implements ElementStep {}

    /** Nothing was recorded of this binding's elements, which leaves what it holds to be read. */
    record NoEdge() implements ElementStep {}
}
