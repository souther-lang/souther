package souther.compiler.check;

import java.util.List;

/**
 * A behavior's input and output types.
 *
 * <p>{@code ins} is the whole parameter list. Only the first stage of a pipeline may have more
 * than one: {@code >->} hands a single value along, so every stage after the first takes one
 * input (spec 14.1). {@link #in} is for those.
 */
public record Sig(List<Type> ins, Type out) {
    public Sig(Type in, Type out) {
        this(List.of(in), out);
    }

    /** The sole input. Only call this for a stage after the first, which takes exactly one. */
    public Type in() {
        return ins.get(0);
    }
}
