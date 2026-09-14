package souther.compiler.ast;

import souther.compiler.types.TypeSymbol;

import java.util.Objects;

/**
 * What a {@link ConstructionOrigin} is and what may be asked of one, in the package that holds the
 * forms an origin belongs to.
 *
 * <p>The arms are here because a record's canonical constructor is as accessible as the record:
 * declared on the interface they would be public, and minting an origin would be anyone's. The
 * questions and the crossings are here for the same kind of reason one step along — a member on the
 * interface is public too, so a pass holding an origin could ask it what it means, or make another
 * one out of it, without the form that holds it having anything to say. Outside this package an
 * origin is a token: it is held, handed on, and asked about by asking the form.
 *
 * <p>The transitions, of which carried by a value is the last word:
 *
 * <pre>
 * Own          --publishedIn(m)--&gt; Published(m)     --carriedByValue--&gt; ByValue
 * Published(_) --publishedIn(m)--&gt; Published(m)     --carriedByValue--&gt; ByValue
 * ByValue      --publishedIn(_)--&gt; ByValue          --carriedByValue--&gt; ByValue
 * </pre>
 *
 * <p>A construction a value carried stays the value's however many published bodies then carry it:
 * the definition of the value is where it was made, and a reader further along is no more the one
 * that made it than the first was. Answering {@code Published} there would put a construction back
 * under the authority of a body that only passed it on.
 */
final class Origins {

    private Origins() {}

    /**
     * Whether the body holding this construction of {@code built} was handed it rather than making
     * it, and so answers for none of it.
     */
    static boolean carried(ConstructionOrigin origin, TypeSymbol.AtModule built) {
        return switch (origin) {
            case Own _ -> false;
            case Published published -> published.module().equals(built.module());
            case ByValue _ -> true;
        };
    }

    /** Whether a value the body named is what carried the construction in. */
    static boolean viaValueReference(ConstructionOrigin origin) {
        return origin instanceof ByValue;
    }

    /** {@code origin}, carried into a reader by {@code module}'s published body. */
    static ConstructionOrigin publishedIn(ConstructionOrigin origin, String module) {
        return origin instanceof ByValue ? origin : new Published(module);
    }

    /** {@code origin}, carried into a body by a value that body named. */
    static ConstructionOrigin carriedByValue(ConstructionOrigin origin) {
        return origin instanceof ByValue kept ? kept : ByValue.IT_IS;
    }

    /** A construction written where it stands. */
    record Own() implements ConstructionOrigin {

        static final Own IT_IS = new Own();
    }

    /**
     * A construction carried into a reader by {@code module}'s published body.
     *
     * <p>The module is what this arm answers with, so there is no such thing as one that does not
     * name it: an origin that knew a construction had come from somewhere and not from where is a
     * fourth answer, and the arm that means "nowhere in particular" is {@link ByValue}.
     */
    record Published(String module) implements ConstructionOrigin {

        Published {
            Objects.requireNonNull(module, "a construction carried by a published body names it");
        }
    }

    /** A construction carried into a body by a value that body named. */
    record ByValue() implements ConstructionOrigin {

        static final ByValue IT_IS = new ByValue();
    }
}
