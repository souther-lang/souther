package souther.compiler.numeric;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

/**
 * What one vocabulary's positions are called in another, one-to-one.
 *
 * <p>A value rather than a function, because a function is not a naming. Two positions called by one
 * name is not a wider reading of the rules about them — it is a claim that they are one number, and
 * a claim nobody made: {@code x <= 0} and {@code y >= 1} say nothing against each other, and under
 * one name they say nothing at all. That is a domain holding something coming back holding nothing,
 * which no reader downstream can see and none would think to look for.
 *
 * <p><b>Whether it is one-to-one is a fact about the positions the rules speak of, so it is settled
 * where that set is known.</b> A rule knows its own positions and no others, so a rule asked to
 * check this catches a collision that happens to fall inside one of them and misses every collision
 * between two — which is exactly the shape a reading of two independent rules takes. Stated at the
 * finer unit, the obligation was written down where it could not be met.
 *
 * <p>So it is met once, here, and what comes out is something that cannot be anything else. A reader
 * handed one of these has nothing left to check and nothing left to forget, and a second reading of
 * rules — another domain, another algebra — takes the same value rather than remembering the same
 * rule.
 *
 * <p><b>And it is asked of each position once.</b> Applied where it is used, a naming would be asked
 * the same question several times and is under no obligation to answer alike; two answers would put
 * one rule's positions under names another rule's are not, which is the same identification arriving
 * by a different road.
 */
public final class Renaming<A, B> {

    private final Map<A, B> called;

    private Renaming(Map<A, B> called) {
        this.called = called;
    }

    /**
     * {@code naming} over {@code positions}, or a refusal where it is not one-to-one on them.
     *
     * <p>Every position named, and no two named alike. Both refusals rather than a widening: a
     * position with no name is one the rules about it cannot be carried across, and dropping those
     * rules leaves what the rules leave wider than it is; two positions with one name leaves it
     * narrower. Neither shows up anywhere near where the naming was written.
     */
    public static <A, B> Renaming<A, B> of(Set<A> positions, Function<A, B> naming) {
        Map<A, B> out = new LinkedHashMap<>();
        Map<B, A> back = new LinkedHashMap<>();
        for (A position : positions) {
            B name = naming.apply(position);
            if (name == null) {
                throw new IllegalArgumentException(
                        "no name in the vocabulary asked for was given to `" + position + "`");
            }
            A had = back.put(name, position);
            if (had != null && !had.equals(position)) {
                throw new IllegalArgumentException(
                        "`" + had + "` and `" + position + "` are both called `" + name
                                + "`, which says they are one number rather than naming two");
            }
            out.put(position, name);
        }
        return new Renaming<>(Map.copyOf(out));
    }

    /**
     * What {@code position} is called.
     *
     * <p>A refusal for one this was not made over, rather than a name made up on the spot. Such a
     * position is one the caller did not know its rules were about, and carrying its rules across
     * under an invented name — or dropping them — is answering a question nobody established the
     * terms of.
     */
    public B of(A position) {
        B name = called.get(position);
        if (name == null) {
            throw new IllegalArgumentException(
                    "`" + position + "` is not one of the positions this naming was made over");
        }
        return name;
    }
}
