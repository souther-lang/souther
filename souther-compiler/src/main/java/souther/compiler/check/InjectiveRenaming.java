package souther.compiler.check;

import java.util.HashMap;
import java.util.Map;
import java.util.function.Function;

/**
 * A change of vocabulary that keeps two things two things.
 *
 * <p><b>Not the same act as reading a form under new names.</b>
 * {@link souther.compiler.numeric.NumericDomain#over} is a fold: two atoms arriving at one name are
 * one number there, and their coefficients are added, because a caller writing
 * {@code List.length(xs) + Set.size(xs)} wrote two spellings of one count. That is right for a form
 * and wrong for a state. Two positions whose admissible values land under one name would hold each
 * other's values, and two positions whose orders land under one name would bound each other — which
 * is the reading saying something nobody wrote.
 *
 * <p>So the whole-state change of vocabulary is this, and it is a different type from a function for
 * that reason. What passes through here is checked as it goes, and a second source arriving at a
 * name some other source already has is refused rather than folded.
 *
 * <p><b>Checked across the whole vocabulary and not per domain.</b> A subject may sit in one domain
 * and no other — a predicate the numbers have no word for, a position only an ordering bounds — so a
 * naming that is injective on each domain read by itself can still put two subjects under one name.
 * One of these is threaded through every domain of one state, and it remembers what it has named, so
 * a collision between two domains is refused the same as a collision inside one.
 *
 * <p>Reused across states on purpose. Two readings renamed into one vocabulary and then met are one
 * state, so what may not collide is every subject of both — and passing one of these to both is what
 * says so.
 *
 * <p>The domains themselves take a plain function, because they sit below this package and may not
 * reach up to it. That costs nothing: each of them applies the naming to every subject it holds, so
 * every subject of the state passes through here, and {@link ConstraintState#renamed} is the only
 * thing in the compiler that hands a naming to a whole state.
 */
public final class InjectiveRenaming<A, B> {

    private final Function<A, B> naming;
    /** What each name has been given to, so that a second source arriving at one is seen. */
    private final Map<B, A> named = new HashMap<>();

    private InjectiveRenaming(Function<A, B> naming) {
        this.naming = java.util.Objects.requireNonNull(naming, "a renaming names things");
    }

    /** The renaming {@code naming} spells, held to naming two things two things. */
    public static <A, B> InjectiveRenaming<A, B> of(Function<A, B> naming) {
        return new InjectiveRenaming<>(naming);
    }

    /**
     * What {@code source} is called in the new vocabulary.
     *
     * @throws IllegalStateException where some other source is already called that, which is this
     *                               renaming saying two subjects are one
     */
    public B apply(A source) {
        B target = naming.apply(source);
        A had = named.putIfAbsent(target, source);
        if (had != null && !had.equals(source)) {
            throw new IllegalStateException("`" + had + "` and `" + source + "` are both called `"
                    + target + "`, so the renaming says they are one subject");
        }
        return target;
    }
}
