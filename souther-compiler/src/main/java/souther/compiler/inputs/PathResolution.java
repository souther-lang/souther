package souther.compiler.inputs;

import java.util.Objects;

/**
 * What a reading of where an expression stands came to.
 *
 * <p>A position reached is one. An expression that names none — arithmetic over a value, a branch
 * between two, something built — is the model saying there is nothing there, and a reader is told
 * so.
 *
 * <p><b>Two answers, and neither of them stands for what this compiler did not read.</b> That was a
 * third answer once, because the reading declined a shape and a reader could not tell "this
 * expression names no position" from "this walk did not follow that". What made it necessary was a
 * shape refused for being a shape; the walk now refuses a step for what a binding is, and a binding
 * that is nothing this can place is a fact about the model as much as arithmetic over one is.
 *
 * <p>So the ways an answer of neither kind could come back are shut where it would come from rather
 * than named here. Every shape a walk after a position meets is answered by an arm of its own, and
 * a shape added to {@link souther.compiler.core.Core} is one that walk does not compile without
 * saying what it names — where a shape swallowed by a default would come back as a model that
 * states nothing, which is the sentence this type exists to keep honest.
 *
 * <p><b>A sealed pair, read out arm by arm.</b> A caller says what it does with each where it asks,
 * and there is nothing here to say it with — a method that answered "the position, or nothing" would
 * be that decision made once for every caller, and an answer added later would arrive at all of them
 * as nothing without one of them being asked. What the arms cost a reader is that every one of those
 * decisions is visible, which is what they are: an answer added here does not compile until every
 * place that reads one has said what it means there.
 */
public sealed interface PathResolution {

    /**
     * Where the expression stands.
     *
     * <p>Somewhere, and refusing to be made without it. A position that is no position is what the
     * answer beside this one says, so a reader given one would be told a place was reached and find
     * the absence it is held apart from.
     */
    record At(TermPath path) implements PathResolution {

        public At {
            Objects.requireNonNull(path, "a position reached is somewhere");
        }
    }

    /**
     * The expression names no position of the input, which is a fact about the model.
     *
     * <p>What a rule about such a value comes to is a question elsewhere — it may have come from a
     * position, and where it did that is said ({@link InputReads#cameFrom}) — and this is the answer
     * that it does not stand at one.
     */
    record NotAPosition() implements PathResolution {}
}
