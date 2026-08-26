package souther.compiler.query;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Where two answers to one question stop being the same thing, and why.
 *
 * <p>A pair walk and not a scan of one of them. What makes an answer fail to compare is not always
 * something with no {@code equals}: a record whose component is a way of reading a store has an
 * {@code equals} of its own and still says no, because the two stores are two objects. Only holding
 * the two side by side says which is which.
 *
 * @param at where in the answer the two came apart, as the steps of the answer's own shape
 * @param cause the class the two are of at that point, or the array type
 * @param kind whether the two say the same thing there, or different things
 */
record Divergence(Locus at, String cause, Divergence.Kind kind) {

    /** What a divergence means. */
    enum Kind {
        /**
         * The two are the same thing said twice and compare unequal anyway — an array, a class with
         * no {@code equals} of its own, one whose {@code equals} rests on something that is one
         * object per store, or a container that compares its members by address. Nothing downstream
         * of it can ever be kept.
         */
        THE_SAME_THING_TWICE,
        /**
         * The two say different things. One compile of one input answered differently from another,
         * which is not about equality at all.
         */
        DIFFERENT_THINGS
    }

    /** A walk of two whole answers is bounded, so a graph nobody meant to walk stops. */
    private static final int FAR_ENOUGH = 400_000;

    /** Where {@code a} and {@code b} come apart, and how much of them was looked at. */
    static Covered<Divergence> between(Object a, Object b) {
        return between(a, b, FAR_ENOUGH);
    }

    /**
     * The same, giving up after {@code budget} pairs.
     *
     * <p>For a test that is about what this says when it gives up. A model large enough to exhaust
     * the bound a compile is walked under is larger than anything here, so the path out would rot
     * unread and the arm reporting it would go with it.
     */
    static Covered<Divergence> between(Object a, Object b, int budget) {
        Walk walk = new Walk(budget);
        walk.at(a, b, Locus.ROOT);
        return Covered.of(walk.out, walk.gaps);
    }

    private static final class Walk {

        /**
         * What each pair already walked came to, as paths relative to that pair.
         *
         * <p>What is kept is the findings and not the fact of having been there. One object under an
         * answer is reached by however many paths hold it, and each of those is a place a capability
         * is exposed — so every one of them is reported, with the findings the first walk of the pair
         * established written out again under the path that reached it this time.
         *
         * <p>Which is also what keeps a holder from being named for its contents. A pair reached a
         * second time that reported nothing back would leave whoever holds it having found nothing
         * below and unequal itself, and the rule that names such a thing would name the holder for a
         * defect five levels under it.
         *
         * <p>A map that compares its members and not their addresses, because a pair is made where it
         * is asked about and is never the same object twice. What is compared is what {@link Pair}
         * says: the two sides by address, which is the question — whether these two objects have been
         * walked together — and not whether two objects are equal, which is what the walk is here to
         * find out.
         */
        private final Map<Pair, List<Divergence>> settled = new HashMap<>();
        /** The pairs on the way down, so a graph that holds itself is met rather than followed. */
        private final Set<Pair> walking = new HashSet<>();
        private final List<Divergence> out = new ArrayList<>();
        private final List<Gap> gaps = new ArrayList<>();
        private int budget;

        Walk(int budget) {
            this.budget = budget;
        }

        private static boolean opaque(Class<?> c) {
            return c == String.class || Number.class.isAssignableFrom(c) || c == Boolean.class
                    || c == Character.class || c.isEnum();
        }

        private void say(Locus at, Class<?> c, Kind kind) {
            // What it is called and not what a reader calls it, arrays included: two arrays of
            // same-named components in two packages are two types.
            out.add(new Divergence(at, c.getTypeName(), kind));
        }

        private void stopped(Gap.Why why, Locus at) {
            gaps.add(new Gap(why, at.toString()));
        }

        /**
         * Compares {@code a} with {@code b}, reporting what it finds under {@code path}.
         *
         * @return whether what is under the two was settled. False where the walk was cut short, so
         *     that finding nothing below is not read as there being nothing below
         */
        boolean at(Object a, Object b, Locus path) {
            if (a == b) {
                return true;
            }
            if (budget-- <= 0) {
                stopped(Gap.Why.BUDGET_EXHAUSTED, path);
                return false;
            }
            if (a == null || b == null) {
                say(path, (a == null ? b : a).getClass(), Kind.DIFFERENT_THINGS);
                return true;
            }
            // What they say before what they are. A concrete class is not what makes a value: a
            // `HashMap` and a `LinkedHashMap` holding one thing are one value by the contract both
            // of them answer to, and telling them apart by their class would call an answer that
            // reproduced a compile that did not.
            if (a.equals(b)) {
                return true;
            }
            if (a.getClass() != b.getClass()) {
                say(path, a.getClass(), Kind.DIFFERENT_THINGS);
                return true;
            }
            Class<?> c = a.getClass();
            if (opaque(c)) {
                if (!a.equals(b)) {
                    say(path, c, Kind.DIFFERENT_THINGS);
                }
                return true;
            }
            // The store itself is where a walk stops. Every answer in it is being compared already,
            // and an answer that holds it holds one object per store however deep the walk goes.
            if (a instanceof Db) {
                say(path, c, Kind.THE_SAME_THING_TWICE);
                return true;
            }
            Pair pair = new Pair(a, b);
            List<Divergence> already = settled.get(pair);
            if (already != null) {
                already.forEach(each -> out.add(new Divergence(
                        path.followedBy(each.at()), each.cause(), each.kind())));
                return true;
            }
            if (!walking.add(pair)) {
                stopped(Gap.Why.A_GRAPH_THAT_LOOPS, path);
                return false;
            }
            int before = out.size();
            boolean whole;
            try {
                whole = descend(a, b, c, path);
                // Nothing under the two explains them, so what is unequal is this. Asked only of a
                // descent that reached the end: one that was cut short found nothing where it did
                // not look, and naming this for that would name a holder for what it holds.
                if (whole && out.size() == before && !a.equals(b)) {
                    say(path, c, Kind.THE_SAME_THING_TWICE);
                }
            } finally {
                walking.remove(pair);
            }
            if (whole) {
                List<Divergence> mine = new ArrayList<>();
                for (Divergence each : out.subList(before, out.size())) {
                    mine.add(new Divergence(new Locus(each.at().steps()
                            .subList(path.steps().size(), each.at().steps().size())),
                            each.cause(), each.kind()));
                }
                settled.put(pair, List.copyOf(mine));
            }
            return whole;
        }

        private boolean descend(Object a, Object b, Class<?> c, Locus path) {
            if (c.isArray()) {
                int length = java.lang.reflect.Array.getLength(a);
                if (length != java.lang.reflect.Array.getLength(b)) {
                    say(path, c, Kind.DIFFERENT_THINGS);
                    return true;
                }
                boolean whole = true;
                for (int i = 0; i < length; i++) {
                    whole &= at(java.lang.reflect.Array.get(a, i),
                            java.lang.reflect.Array.get(b, i),
                            path.then(new Locus.Step.Element()));
                }
                // An array compares by identity, so where the elements agree the caller's own
                // check is what names it.
                return whole;
            }
            if (a instanceof Map<?, ?> left && b instanceof Map<?, ?> right) {
                return entries(left, right, c, path);
            }
            // What an absence may be hiding, read through rather than walked into. The field under
            // one of these belongs to `java.base`, which opens nothing here, so a pair of them
            // walked by their fields is a pair the walk cannot get inside — and read by their own
            // equality, a value that compares by address inside one names the absence that holds it
            // rather than itself.
            if (a instanceof java.util.Optional<?> mine && b instanceof java.util.Optional<?> yours) {
                if (mine.isPresent() != yours.isPresent()) {
                    say(path, c, Kind.DIFFERENT_THINGS);
                    return true;
                }
                return mine.isEmpty()
                        || at(mine.get(), yours.get(), path.then(new Locus.Step.Present()));
            }
            if (a instanceof Collection<?> left && b instanceof Collection<?> right) {
                return members(left, right, c, path);
            }
            if (a.equals(b)) {
                return true;
            }
            boolean whole = true;
            for (Class<?> k = c; k != null && k != Object.class; k = k.getSuperclass()) {
                for (Field f : k.getDeclaredFields()) {
                    if (Modifier.isStatic(f.getModifiers())) {
                        continue;
                    }
                    Object mine;
                    Object theirs;
                    try {
                        f.setAccessible(true);
                        mine = f.get(a);
                        theirs = f.get(b);
                    } catch (ReflectiveOperationException | RuntimeException | Error _) {
                        stopped(Gap.Why.A_FIELD_THAT_WOULD_NOT_OPEN,
                                path.thenMember(k, f.getName()));
                        whole = false;
                        continue;
                    }
                    whole &= at(mine, theirs, path.thenMember(k, f.getName()));
                }
            }
            return whole;
        }

        /**
         * Two collections compared over the correspondence their own contract gives them.
         *
         * <p>A list is equal to another list by position and a set to another set by membership, so
         * those are the two ways a pair of them line up. Lined up by the order an iterator gives, a
         * pair of sets holding one thing each in a different order comes back as two members that
         * differ — which is this saying a compile did not reproduce, about two answers that mean the
         * same. So the rule is read off the contract, and a collection answering to neither is where
         * this stops rather than where it guesses.
         *
         * <p>A set pairs by what its members say, so a member it pairs is equal to the other side
         * and there is nothing under it left to find. What the pairing is for is that it either
         * holds one to one or does not, and the second is worth saying.
         */
        private boolean members(Collection<?> left, Collection<?> right, Class<?> c, Locus path) {
            if (left instanceof List<?> mine && right instanceof List<?> yours) {
                if (mine.size() != yours.size()) {
                    say(path, c, Kind.DIFFERENT_THINGS);
                    return true;
                }
                boolean whole = true;
                for (int i = 0; i < mine.size(); i++) {
                    whole &= at(mine.get(i), yours.get(i), path.then(new Locus.Step.Element()));
                }
                return whole;
            }
            if (left instanceof Set<?> && right instanceof Set<?>) {
                if (left.size() != right.size()) {
                    say(path, c, Kind.DIFFERENT_THINGS);
                    return true;
                }
                if (!pairedOneToOne(left, right, path.then(new Locus.Step.Element()))) {
                    return false;
                }
                // Paired by what they say and still not equal, which is the container saying its
                // membership is not what its members mean.
                if (!left.equals(right)) {
                    say(path, c, Kind.THE_SAME_THING_TWICE);
                }
                return true;
            }
            // Said before the sizes are compared. That two containers of different sizes hold
            // different things is a container's own contract as much as how its members line up, and
            // this is where that contract is unknown.
            stopped(Gap.Why.A_CONTAINER_WITH_NO_RULE_FOR_PAIRING, path);
            return false;
        }

        /**
         * {@code right}'s members by what each of them says, or null where that is not one to one
         * with {@code left}'s.
         *
         * <p>Total and injective or nothing. A correspondence built by putting one side in a map of
         * its own members loses a member wherever two of them say the same thing — which is exactly
         * what a container comparing its members by address holds — and every member of the other
         * side then pairs with whatever survived. Counting what the map kept is what says the
         * correspondence is the one it looks like.
         */
        private boolean pairedOneToOne(Collection<?> left, Collection<?> right, Locus path) {
            Map<Object, Object> theirs = new HashMap<>();
            for (Object each : right) {
                theirs.put(each, each);
            }
            Map<Object, Object> mine = new HashMap<>();
            for (Object each : left) {
                mine.put(each, each);
            }
            if (theirs.size() != right.size() || mine.size() != left.size()
                    || !theirs.keySet().equals(mine.keySet())) {
                stopped(Gap.Why.MEMBERS_THAT_DO_NOT_PAIR, path);
                return false;
            }
            return true;
        }

        /**
         * The two maps compared entry by entry, over a correspondence built here.
         *
         * <p>Built here and never asked of the map. A map that compares its keys by address answers
         * no to every question about another store's however equal the keys are, so a walk that took
         * the map's own answer for the question would file a container nothing can keep as a compile
         * that did not reproduce. Paired through what the keys themselves say, such a map is walked
         * like any other and comes back unequal at the end, which is what it is.
         *
         * <p>An entry with nothing to pair it with is where this stops rather than where it decides.
         * Two maps of one size can hold keys that do not line up because a key carries an address, or
         * because the two hold different things, and nothing at this end tells those apart — so it is
         * said as a place the walk could not go.
         *
         * <p><b>The values, and the keys only as far as pairing them.</b> A key that pairs is a key
         * the other side holds one equal to, and two equal things are where this walk stops looking:
         * whatever an equal key carries, the answers above it compare the same either way. So a key
         * holding a way of reading a store is not this walk's to find — that is a defect in what the
         * answer holds rather than in what two of them come to, and it is found by walking one answer
         * and asking each object what it is.
         */
        private boolean entries(Map<?, ?> left, Map<?, ?> right, Class<?> c, Locus path) {
            if (left.size() != right.size()) {
                say(path, c, Kind.DIFFERENT_THINGS);
                return true;
            }
            if (!pairedOneToOne(left.keySet(), right.keySet(),
                    path.then(new Locus.Step.MapKey()))) {
                return false;
            }
            // Judged here and not from what the walk finds underneath. A container has an equality
            // of its own beside whatever its values hold, and the rule that names a thing for
            // finding nothing below it would let one wrap a defect that is already written down and
            // go unnamed. What says this one is its own is that its keys pair by what they say and
            // it says they do not.
            if (!left.keySet().equals(right.keySet())) {
                say(path, c, Kind.THE_SAME_THING_TWICE);
            }
            Map<Object, Object> theirs = new HashMap<>();
            for (Map.Entry<?, ?> each : right.entrySet()) {
                theirs.put(each.getKey(), each.getValue());
            }
            boolean whole = true;
            for (Map.Entry<?, ?> each : left.entrySet()) {
                whole &= at(each.getValue(), theirs.get(each.getKey()),
                        path.then(new Locus.Step.MapValue()));
            }
            return whole;
        }
    }

    /** Two objects walked together, by identity. */
    private record Pair(Object left, Object right) {
        @Override
        public boolean equals(Object other) {
            return other instanceof Pair pair && pair.left == left && pair.right == right;
        }

        @Override
        public int hashCode() {
            return System.identityHashCode(left) * 31 + System.identityHashCode(right);
        }
    }
}
