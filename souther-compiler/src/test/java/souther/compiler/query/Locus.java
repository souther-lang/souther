package souther.compiler.query;

import java.util.ArrayList;
import java.util.List;

/**
 * Where in an answer something sits, as the steps of the answer's own shape.
 *
 * <p>The shape and not the heap. A walk of two answers, or of one, gets from an answer to an object
 * by taking a component of a record, a field of a class, an element of a collection, a key or a
 * value of a map, or what an absence holds — and those are the steps, kept as what they are. Written
 * as text on the way, two of them come out the same: a component called {@code value} and the value
 * side of a map are both {@code .value}, and a reader of a path cannot tell which happened. Kept as
 * steps, they are two things and are rendered as two.
 *
 * <p><b>An occurrence and not an object.</b> One object under an answer is held by however many
 * paths hold it, and each of those is a place the answer exposes it. So a locus says which way down
 * was taken, and the same object reached twice is two loci rather than one — which is what lets a
 * register of what an answer holds be a register of places rather than of classes.
 *
 * <p>What is not here is a step into a case of a sum. Nothing walks one: a case is what an object's
 * class is, and the walk reaches it by being at the object. A step for it would be a word no walk
 * writes.
 */
record Locus(List<Locus.Step> steps) {

    /** One way down from a thing an answer holds to something it holds. */
    sealed interface Step {

        /** A component of a record, by the name the record gives it. */
        record Component(String name) implements Step {}

        /** A field of a class that is not a record, by its name. */
        record Field(String name) implements Step {}

        /** An element of an array. Which one is not kept: an answer is not more or less exposed at
         *  the third element than at the first, and the index would put the order of a walk into a
         *  register. */
        record ArrayElement() implements Step {}

        /** An element of a collection, on the same terms. */
        record Element() implements Step {}

        /** The key side of a map's entry. */
        record MapKey() implements Step {}

        /** The value side of one. */
        record MapValue() implements Step {}

        /** What an absence holds, where it holds something. */
        record Present() implements Step {}
    }

    /** The answer itself. */
    static final Locus ROOT = new Locus(List.of());

    Locus {
        steps = List.copyOf(steps);
    }

    /** The same locus with one more step at the end. */
    Locus then(Step step) {
        List<Step> out = new ArrayList<>(steps);
        out.add(step);
        return new Locus(out);
    }

    /** A component or a field of {@code owner}, whichever it declares them as. */
    Locus thenMemberOf(Class<?> owner, String name) {
        return then(owner.isRecord() ? new Step.Component(name) : new Step.Field(name));
    }

    /**
     * {@code inner} read as a locus under this one.
     *
     * <p>What a walk that remembers what it found under a pair needs. What was found there is kept
     * relative to it, and every path that reaches the pair again writes those out again from where it
     * stands — so the steps are joined rather than a rendered path being cut at a length.
     */
    Locus followedBy(Locus inner) {
        List<Step> out = new ArrayList<>(steps);
        out.addAll(inner.steps());
        return new Locus(out);
    }

    /**
     * This locus as one string.
     *
     * <p>The brace forms are what keep a map apart from a member. A record with a component called
     * {@code value} and the value side of a map are different steps and read differently here, which
     * is the whole reason the steps are kept.
     */
    String rendered() {
        StringBuilder out = new StringBuilder();
        for (Step step : steps) {
            out.append(switch (step) {
                case Step.Component(String name) -> "." + name;
                case Step.Field(String name) -> "." + name;
                case Step.ArrayElement _ -> "[]";
                case Step.Element _ -> "[]";
                case Step.MapKey _ -> "{key}";
                case Step.MapValue _ -> "{value}";
                case Step.Present _ -> "?";
            });
        }
        return out.toString();
    }

    @Override
    public String toString() {
        return rendered();
    }
}
