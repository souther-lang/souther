package souther.compiler.examples;

/**
 * One value in the form a derived decoder reads, holding nothing that came from any loader's classes.
 *
 * <p>{@link NeutralForm} decides the form — which discriminator a case of a sum carries, when a unit
 * case travels as a bare name, whether a newtype wears the envelope — and this is a value standing in
 * it. Two names because they are two things: the rules are one reading and are asked wherever a value
 * has to be written or read back, and a value in that form is what crosses between a run and whatever
 * applies a behavior for it.
 *
 * <p>{@link #read} is what a derived decoder reads, and it is the only reading there is. Nothing here
 * says what the form is made of: a caller that took the vocabulary of the form itself would be a
 * second reader of rules that already have one, free to answer differently about the same value.
 *
 * <p>Made where a value is built. Nothing outside this package can produce one, because what makes it
 * a neutral form of some value is the walk that produced it and not the shape it happens to have.
 */
public final class NeutralValue {

    private final Object form;

    NeutralValue(Object form) {
        this.form = form;
    }

    /** What a derived decoder reads. */
    public Object read() {
        return form;
    }
}
