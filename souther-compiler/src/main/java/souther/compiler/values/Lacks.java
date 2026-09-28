package souther.compiler.values;

import souther.compiler.hash.ValueHash;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;

/**
 * What one argument about a relation showed, which is every lack it showed and not one of them.
 *
 * <p>Nothing here is in an order. An argument that walks the sets a count is taken of reaches them
 * in the order the pairs were written, and two writings of one relation are one relation — so what
 * these are equal to is settled by which lacks they are and how each was reached, and by nothing
 * about where in a walk each was found.
 *
 * <p>Each lack once, with every route that reached it. Two readings put together can show one lack
 * by taking a block's values through different rules, and both lots of rules are what an author has
 * to answer for.
 *
 * <p>And what a lack claims is what these are held under, which is a question asked of every lack
 * of one of these against every lack of another wherever two are put together. Asked by walking,
 * that is the square of a relation's sets on a relation admitted for as many of them as the bound
 * allows — so which of these claims what is a lookup rather than a search.
 *
 * <p><b>Which is the whole of what is inside.</b> Nothing here answers with an order and nothing
 * here holds one: a reader asks what was claimed, what a report may name, or whether every lack is
 * of some kind, and each of those is about what these hold rather than about where in a walk one of
 * them was found.
 *
 * @param <A> what a position is called
 */
public final class Lacks<A> {

    /** What an argument that refused nothing showed, which is one value however its positions are
     *  named — see {@link #none()}. */
    private static final Lacks<?> NONE = new Lacks<>(Map.of());

    /**
     * What was shown, under what each of them claims.
     *
     * <p><b>Held under the claim and not beside a place in a list.</b> These are equal by which
     * lacks they are and how each was reached, so where in a walk one was found is not something
     * one of these has — and a table from a claim to a place in a list is that place carried under
     * another name. Two of them that are equal were built two ways, and what the second was found
     * after is not the same there.
     */
    private final Map<RelationalLack<A>, Shown<A>> claiming;

    private Lacks(Map<RelationalLack<A>, Shown<A>> claiming) {
        this.claiming = Collections.unmodifiableMap(claiming);
    }

    /**
     * These, each claimed once.
     *
     * <p>Every claim made twice is named and not the first one met. What is handed in is a list
     * because a caller has one, and what a list of these is equal to is settled by which lacks are
     * in it — so a refusal that stopped at the first would tell two callers that wrote one argument
     * two ways two different things about the same mistake.
     */
    private static <A> Lacks<A> claimedOnce(Collection<Shown<A>> each) {
        Map<RelationalLack<A>, Shown<A>> claiming = new HashMap<>(each.size() * 2);
        Set<RelationalLack<A>> twice = new LinkedHashSet<>();
        for (Shown<A> shown : each) {
            if (claiming.put(shown.lack(), shown) != null) {
                twice.add(shown.lack());
            }
        }
        if (!twice.isEmpty()) {
            throw new IllegalArgumentException("a lack is claimed once, with every route that "
                    + "reached it: " + InOneOrder.of(twice));
        }
        return new Lacks<>(claiming);
    }

    /** These lacks, each of them claimed once. */
    static <A> Lacks<A> of(Collection<Shown<A>> each) {
        return claimedOnce(each);
    }

    /**
     * None of them, which is what an argument that refused nothing showed.
     *
     * <p>One value for every naming of a position. What these hold is what a caller put in them,
     * so what an empty one holds is nothing whatever its positions are called — and what it is
     * equal to, hashes as and is written as is settled by that alone. Which is why a reader on the
     * path where a relation shows nothing is handed the same one every time rather than a new one:
     * that path is walked once for every pair of two readings' alternatives.
     */
    @SuppressWarnings("unchecked")
    public static <A> Lacks<A> none() {
        return (Lacks<A>) NONE;
    }

    /** The one lack an argument showed, of the blocks it names and of nothing else. */
    public static <A> Lacks<A> of(RelationalLack<A> lack) {
        return new Lacks<>(Map.of(lack, Shown.of(lack)));
    }

    /** The one lack an argument showed, and how it reached it. */
    public static <A> Lacks<A> of(RelationalLack<A> lack, RelationalEvidence<A> reached) {
        return new Lacks<>(Map.of(lack, new Shown<>(lack, reached)));
    }

    /** Whether nothing was shown. */
    public boolean isEmpty() {
        return claiming.isEmpty();
    }

    /** How many of them there are, which is how many lots of blocks the argument was short of. */
    public int size() {
        return claiming.size();
    }

    /**
     * The one lack these are, where they are one.
     *
     * @throws IllegalStateException where they are not one, since a reader that asked this of
     *         several would be reading whichever arrived first
     */
    public Shown<A> only() {
        if (claiming.size() != 1) {
            throw new IllegalStateException("one lack was asked for, and these are " + this);
        }
        return claiming.values().iterator().next();
    }

    /** What each of them claims, less how any of them was reached. */
    public Set<RelationalLack<A>> claimed() {
        return claiming.keySet();
    }

    /** Every block a report may name: what the lacks are about, and what the routes to them read. */
    public Set<Sameness.Block<A>> blocks() {
        Set<Sameness.Block<A>> out = new LinkedHashSet<>();
        claiming.values().forEach(shown -> {
            out.addAll(shown.lack().blocks());
            out.addAll(shown.reached().restingOn(shown.lack().blocks()));
        });
        return Collections.unmodifiableSet(out);
    }

    /** Whether every lack is something, which is how a reader asks what argument refused. */
    public boolean all(Predicate<RelationalLack<A>> asked) {
        return claiming.keySet().stream().allMatch(asked);
    }

    /** Both of these: every lack either shows, each with every route that reached it. */
    public Lacks<A> and(Lacks<A> other) {
        Map<RelationalLack<A>, Shown<A>> out = new HashMap<>(claiming);
        other.claiming.forEach((lack, shown) -> out.merge(lack, shown, Shown::alsoReachedBy));
        return new Lacks<>(out);
    }

    /** The lacks both of these claim, each with the routes both of them reached it by. */
    public Lacks<A> sharedWith(Lacks<A> other) {
        Map<RelationalLack<A>, Shown<A>> out = new HashMap<>();
        claiming.forEach((lack, shown) -> {
            Shown<A> theirs = other.claiming.get(lack);
            if (theirs != null) {
                out.put(lack, shown.alsoReachedBy(theirs));
            }
        });
        return new Lacks<>(out);
    }

    /**
     * The same lacks about the blocks {@code naming} calls these.
     *
     * <p>A change of vocabulary and not a fold: the naming names two lacks two lacks, so what was
     * claimed once is claimed once under the new names too, and nothing here has to be told apart
     * again.
     */
    public <B> Lacks<B> renamed(Function<A, B> naming) {
        Map<RelationalLack<B>, Shown<B>> out = new HashMap<>(claiming.size() * 2);
        claiming.values().forEach(shown -> {
            Shown<B> under = shown.renamed(naming);
            out.put(under.lack(), under);
        });
        return new Lacks<>(out);
    }

    /** The same lacks, each reached the same way, whichever order they arrived in. */
    @Override
    public boolean equals(Object said) {
        return said instanceof Lacks<?> it && claiming.equals(it.claiming);
    }

    /** What was shown, in no order — see {@link ValueHash}. */
    @Override
    public int hashCode() {
        int summed = 0;
        for (Shown<A> shown : claiming.values()) {
            summed += shown.hashCode();
        }
        return ValueHash.ofWhatItHolds(Lacks.class, summed, claiming.size());
    }

    /** Written in one order whichever they arrived in — see {@link InOneOrder}. */
    @Override
    public String toString() {
        return InOneOrder.of(claiming.values());
    }
}
