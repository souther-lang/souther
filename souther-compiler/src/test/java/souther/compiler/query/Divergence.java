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
        private final Map<Pair, Settled> settled = new HashMap<>();
        /** The pairs on the way down, so a graph that holds itself is met rather than followed. */
        private final Set<Pair> walking = new HashSet<>();
        private final List<Divergence> out = new ArrayList<>();
        private final List<Gap> gaps = new ArrayList<>();
        private int budget;

        Walk(int budget) {
            this.budget = budget;
        }

        /**
         * What the language says the meaning of, which is {@link AnswerShape}'s to say.
         *
         * <p>The same list as the walk of one store reads. Written again here, one of them had a
         * rule admitting whatever extends a number, so a thing whose equality is an address came
         * back from this walk as two compiles answering different things — true of the objects and
         * wrong about the compiler.
         */
        private static boolean opaque(Class<?> c) {
            return AnswerShape.isLeaf(c);
        }

        private void say(Locus at, Class<?> c, Kind kind) {
            // What it is called and not what a reader calls it, arrays included: two arrays of
            // same-named components in two packages are two types.
            out.add(new Divergence(at, c.getTypeName(), kind));
        }

        private void stopped(Gap.Why why, Locus at) {
            gaps.add(new Gap(why, at.asText()));
        }

        /**
         * What one pair came to: how much of it was seen, whether the two are the same thing, and
         * whether they say so.
         *
         * <p>Three answers because they are three questions, and the walk was answering the second
         * and third with stand-ins for each other. Whether two things are the same thing is read off
         * their shape — every part of one against the part of the other it corresponds to, down to
         * the leaves the language defines. Whether they say so is what {@code equals} answers, which
         * is the thing under test and never the evidence.
         *
         * <p>A defect is where the two disagree: the same thing said twice, said by something that
         * denies it. And it is this thing's own defect only where every part of it says yes — a
         * holder whose part denies its twin is a holder denying its twin for a reason, and nothing
         * here can tell whether it would have agreed had the part behaved.
         *
         * @param covered whether everything under the two was looked at
         * @param theSameThing whether the two are one thing, read off the shape
         * @param andSayIt whether the two say so, read off {@code equals}. Only asked where the
         *                 walk covered them: an {@code equals} of something that holds itself does
         *                 not come back, and the answer would be worth nothing anyway
         */
        record Came(boolean covered, boolean theSameThing, boolean andSayIt) {

            static final Came IDENTICAL = new Came(true, true, true);

            /** Cut short, so nothing under it was settled and nothing about it is claimed. */
            static Came cutShort() {
                return new Came(false, true, true);
            }
        }

        /** Compares {@code a} with {@code b}, reporting what it finds under {@code path}. */
        Came at(Object a, Object b, Locus path) {
            if (a == b) {
                return Came.IDENTICAL;
            }
            if (budget-- <= 0) {
                stopped(Gap.Why.BUDGET_EXHAUSTED, path);
                return Came.cutShort();
            }
            if (a == null || b == null) {
                say(path, (a == null ? b : a).getClass(), Kind.DIFFERENT_THINGS);
                return new Came(true, false, false);
            }
            Class<?> c = a.getClass();
            if (opaque(c) || opaque(b.getClass())) {
                // The leaves the language defines. What one of these says is what it is, so the two
                // questions are one question here and this is where the walk grounds out.
                boolean alike = a.equals(b);
                if (!alike) {
                    say(path, c, Kind.DIFFERENT_THINGS);
                }
                return new Came(true, alike, alike);
            }
            // The store itself is where a walk stops. Every answer in it is being compared already,
            // and an answer that holds it holds one object per store however deep the walk goes.
            if (a instanceof Db || b instanceof Db) {
                say(path, c, Kind.THE_SAME_THING_TWICE);
                return new Came(true, true, false);
            }
            Pair pair = new Pair(a, b);
            Settled already = settled.get(pair);
            if (already != null) {
                already.found().forEach(each -> out.add(new Divergence(
                        path.followedBy(each.at()), each.cause(), each.kind())));
                return already.came();
            }
            if (!walking.add(pair)) {
                stopped(Gap.Why.A_GRAPH_THAT_LOOPS, path);
                return Came.cutShort();
            }
            int before = out.size();
            Came came;
            try {
                came = judged(a, b, c, path);
            } finally {
                walking.remove(pair);
            }
            if (came.covered()) {
                List<Divergence> mine = new ArrayList<>();
                for (Divergence each : out.subList(before, out.size())) {
                    mine.add(new Divergence(new Locus(each.at().steps()
                            .subList(path.steps().size(), each.at().steps().size())),
                            each.cause(), each.kind()));
                }
                settled.put(pair, new Settled(came, List.copyOf(mine)));
            }
            return came;
        }

        /**
         * The two taken apart, and then judged on what the parts came to.
         *
         * <p>Where the rule that names a thing for itself lives, and the whole of it: the parts say
         * the two are one thing, every part of it agrees with its twin, and this denies it. Read off
         * what was found under it instead, a thing was named only where nothing else was — so
         * wrapping something already written down in a container that compares by address left the
         * container unnamed.
         */
        private Came judged(Object a, Object b, Class<?> c, Locus path) {
            Parts parts = new Parts();
            boolean known = takeApart(a, b, c, path, parts);
            if (!known) {
                return Came.cutShort();
            }
            if (!parts.covered) {
                return Came.cutShort();
            }
            if (!parts.theSameThing) {
                return new Came(true, false, false);
            }
            // Asked only of a pair the walk got to the end of. An `equals` of something that holds
            // itself does not come back, and one asked about a pair half of which went unread would
            // be answering about something nobody looked at.
            boolean andSayIt = a.equals(b);
            if (andSayIt || parts.alreadySaid) {
                return new Came(true, true, andSayIt);
            }
            switch (ownEqualityOf(a, c)) {
                // Nothing its parts did explains it, so it is its own however they came out.
                case ITS_ADDRESS -> say(path, c, Kind.THE_SAME_THING_TWICE);
                // Its parts', so a part denying is the explanation and there is nothing of its own
                // to report; where every part agreed, there is nothing else this could be.
                case ITS_PARTS -> {
                    if (parts.everyPartSaysIt) {
                        say(path, c, Kind.THE_SAME_THING_TWICE);
                    }
                }
                // Where every part agreed the answer is the same either way. Where one did not,
                // this is where the walk says it cannot tell whose denial this is.
                case NEITHER_COULD_BE_SHOWN -> {
                    if (parts.everyPartSaysIt) {
                        say(path, c, Kind.THE_SAME_THING_TWICE);
                    } else {
                        stopped(Gap.Why.WHOSE_DENIAL_THIS_IS_CANNOT_BE_TOLD, path);
                        return new Came(false, true, false);
                    }
                }
            }
            return new Came(true, true, false);
        }

        /**
         * Where a thing's own equality comes from, which is what says whose defect a denial is.
         *
         * <p>Two kinds and the difference is what a fix would move. Something whose equality is its
         * parts' denies because a part denied, so fixing the part fixes it and it is not a debt of
         * its own — a record holding something that compares by address is that. Something whose
         * equality is its address denies whatever its parts do, so fixing every part leaves it
         * exactly where it was, and it is a debt of its own beside them.
         *
         * <p>Read off what the language says and not off what the walk found. Judged on what was
         * found beneath it, a thing of the second kind disappears from the register for as long as
         * anything under it also fails — so putting an array around something already written down
         * would add no line, and the line would arrive only once somebody fixed the inner one.
         */
        private enum OwnEquality {
            /** Its parts', so a part denying explains it. */
            ITS_PARTS,
            /** Its address, so nothing its parts do explains it. */
            ITS_ADDRESS,
            /**
             * Neither could be shown.
             *
             * <p>Something that wrote its own equality answers alike either way while a part of it
             * is denying — an equality over the parts denies because the part did, and an equality
             * over the address denies whatever the part did. Nothing readable off the class tells
             * the two apart, so where a part is denying this is where the walk says it cannot tell
             * rather than picking one.
             */
            NEITHER_COULD_BE_SHOWN
        }

        /** What the parts of one pair came to, added up as they are walked. */
        private static final class Parts {
            private boolean covered = true;
            private boolean theSameThing = true;
            private boolean everyPartSaysIt = true;
            /** Whether the thing above has already been named for a half of its own equality, so
             *  that one defect is one line. */
            private boolean alreadySaid;

            void and(Came came) {
                covered &= came.covered();
                theSameThing &= came.theSameThing();
                everyPartSaysIt &= came.andSayIt();
            }
        }

        /** Which contract a thing answers to, which is what says how a pair of them line up. */
        private enum Contract {
            /** Equal to another by position. */
            A_LIST,
            /** Equal to another by what is in it. */
            A_SET,
            /** Equal to another by what it holds under what. */
            A_MAP,
            /** Equal to another by what is behind it. */
            AN_ABSENCE,
            /** A collection answering to none of the above, so nothing here says how two of them
             *  line up. */
            SOMETHING_ELSE_THAT_HOLDS_THINGS,
            /** Everything else, which is compared as what it is made of. */
            A_THING
        }

        /**
         * Where {@code c}'s equality comes from.
         *
         * <p>An array and nothing else, because that is what the language says: an array is equal to
         * another when it is the same array, whatever either holds. Everything else this walks
         * either derives its equality from what it is made of or is a container answering to a
         * contract that does — and where one of those turns out not to, what says so is a half of
         * its equality this can put on its own, which is asked where that half is walked.
         */
        private static OwnEquality ownEqualityOf(Object a, Class<?> c) {
            if (c.isArray()) {
                return OwnEquality.ITS_ADDRESS;
            }
            if (contractOf(a) != Contract.A_THING) {
                // Something answering to a contract this walk knows is equal to another by what it
                // holds, which the contract says and this does not have to work out. Where an
                // implementation of one answers otherwise, what says so is the half of its equality
                // this puts on its own where that half is walked.
                return OwnEquality.ITS_PARTS;
            }
            try {
                if (c.getMethod("equals", Object.class).getDeclaringClass() == Object.class) {
                    // Nothing of its own to compare with, so what it answers is its address.
                    return OwnEquality.ITS_ADDRESS;
                }
            } catch (NoSuchMethodException none) {
                return OwnEquality.ITS_ADDRESS;
            }
            if (c.isRecord()) {
                // A twin of it, made of the very things it holds. One that denies that is one whose
                // equality is not what it holds — asked of the thing rather than read off its class,
                // because a record may write its own.
                Boolean deniesItsTwin = deniesATwinOfItself(a, c);
                if (deniesItsTwin != null) {
                    return deniesItsTwin ? OwnEquality.ITS_ADDRESS : OwnEquality.ITS_PARTS;
                }
            }
            return OwnEquality.NEITHER_COULD_BE_SHOWN;
        }

        /** Whether {@code a} denies a twin built from the very things it holds, or null where no
         *  twin could be built. */
        private static Boolean deniesATwinOfItself(Object a, Class<?> c) {
            try {
                java.lang.reflect.RecordComponent[] held = c.getRecordComponents();
                Class<?>[] types = new Class<?>[held.length];
                Object[] values = new Object[held.length];
                for (int i = 0; i < held.length; i++) {
                    types[i] = held[i].getType();
                    java.lang.reflect.Method reader = held[i].getAccessor();
                    reader.setAccessible(true);
                    values[i] = reader.invoke(a);
                }
                java.lang.reflect.Constructor<?> canonical = c.getDeclaredConstructor(types);
                canonical.setAccessible(true);
                return !a.equals(canonical.newInstance(values));
            } catch (ReflectiveOperationException | RuntimeException | Error opaque) {
                return null;
            }
        }

        /**
         * Which contract a thing is read under, where it keeps one at all.
         *
         * <p>Something that says it keeps none of it is read as a thing of its own, which is
         * {@link AnswerShape#keepsThatContract}'s to say and is what the walk of one store reads
         * too. A map whose equality is which objects were put in it, paired entry by entry, would
         * have its members compared and its own answer never asked.
         */
        private static Contract contractOf(Object each) {
            if (!AnswerShape.keepsThatContract(each.getClass())) {
                return Contract.A_THING;
            }
            if (each instanceof List<?>) {
                return Contract.A_LIST;
            }
            if (each instanceof Set<?>) {
                return Contract.A_SET;
            }
            if (each instanceof Map<?, ?>) {
                return Contract.A_MAP;
            }
            if (each instanceof java.util.Optional<?>) {
                return Contract.AN_ABSENCE;
            }
            return each instanceof Collection<?>
                    ? Contract.SOMETHING_ELSE_THAT_HOLDS_THINGS : Contract.A_THING;
        }

        /**
         * The two walked part by part, over the correspondence their own contract gives them.
         *
         * <p>The contract before the class. A list and a linked list holding one thing are one value
         * by the contract both answer to, so which concrete class each of them is is not what says
         * whether they are the same thing — read that way, a pair of them holding something that does
         * not compare would come back as one input having compiled to two different answers.
         *
         * @return whether the shape of the two is one this knows how to take apart
         */
        private boolean takeApart(Object a, Object b, Class<?> c, Locus path, Parts parts) {
            Contract mineIs = contractOf(a);
            Contract theirsIs = contractOf(b);
            if (mineIs != theirsIs) {
                // Two contracts and not an unknown one. A list and a set are both understood and
                // neither is the other, so the two are different things — said as that rather than
                // as somewhere this could not go, which would send a reader after the walk instead
                // of after the compile.
                say(path, c, Kind.DIFFERENT_THINGS);
                parts.theSameThing = false;
                return true;
            }
            if (mineIs == Contract.SOMETHING_ELSE_THAT_HOLDS_THINGS) {
                // Neither position nor membership is its equality, so there is no rule here to pair
                // it by. Said before the sizes are compared: that two of different sizes hold
                // different things is a contract too, and this is where the contract is unknown.
                stopped(Gap.Why.A_CONTAINER_WITH_NO_RULE_FOR_PAIRING, path);
                return false;
            }
            if (a instanceof List<?> mine && b instanceof List<?> yours) {
                if (mine.size() != yours.size()) {
                    say(path, c, Kind.DIFFERENT_THINGS);
                    parts.theSameThing = false;
                    return true;
                }
                for (int i = 0; i < mine.size(); i++) {
                    parts.and(at(mine.get(i), yours.get(i), path.then(new Locus.Step.Element())));
                }
                return true;
            }
            if (a instanceof Set<?> mine && b instanceof Set<?> yours) {
                if (mine.size() != yours.size()) {
                    say(path, c, Kind.DIFFERENT_THINGS);
                    parts.theSameThing = false;
                    return true;
                }
                // A set pairs by what its members say, so a member it pairs is equal to the other
                // side and there is nothing under it left to walk. What the pairing is for is that
                // it either holds one to one or does not.
                if (!pairedOneToOne(mine, yours, path.then(new Locus.Step.Element()))) {
                    parts.covered = false;
                }
                return true;
            }
            if (a instanceof Map<?, ?> mine && b instanceof Map<?, ?> yours) {
                entries(mine, yours, c, path, parts);
                return true;
            }
            if (a instanceof java.util.Optional<?> mine && b instanceof java.util.Optional<?> yours) {
                if (mine.isPresent() != yours.isPresent()) {
                    say(path, c, Kind.DIFFERENT_THINGS);
                    parts.theSameThing = false;
                    return true;
                }
                if (mine.isPresent()) {
                    parts.and(at(mine.get(), yours.get(), path.then(new Locus.Step.Present())));
                }
                return true;
            }
            // Past the shared contracts, two things of two classes are two things.
            if (a.getClass() != b.getClass()) {
                say(path, c, Kind.DIFFERENT_THINGS);
                parts.theSameThing = false;
                return true;
            }
            if (c.isArray()) {
                int length = java.lang.reflect.Array.getLength(a);
                if (length != java.lang.reflect.Array.getLength(b)) {
                    say(path, c, Kind.DIFFERENT_THINGS);
                    parts.theSameThing = false;
                    return true;
                }
                for (int i = 0; i < length; i++) {
                    parts.and(at(java.lang.reflect.Array.get(a, i),
                            java.lang.reflect.Array.get(b, i),
                            path.then(new Locus.Step.Element())));
                }
                return true;
            }
            fieldsOf(a, b, c, path, parts);
            return true;
        }

        private void fieldsOf(Object a, Object b, Class<?> c, Locus path, Parts parts) {
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
                        stopped(Gap.Why.A_FIELD_THAT_WOULD_NOT_OPEN, path.thenMember(k, f.getName()));
                        parts.covered = false;
                        continue;
                    }
                    parts.and(at(mine, theirs, path.thenMember(k, f.getName())));
                }
            }
        }

        /**
         * {@code right}'s members put in correspondence with {@code left}'s by what each of them
         * says.
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
         * The two maps taken apart entry by entry, over a correspondence built here.
         *
         * <p>Built here and never asked of the map. A map that compares its keys by address answers
         * no to every question about another store's however equal the keys are, so a walk that took
         * the map's own answer for the question would file a container nothing can keep as a compile
         * that did not reproduce.
         *
         * <p>The values, and the keys only as far as pairing them. A key that pairs is a key the
         * other side holds one equal to, and two equal things are where this walk stops looking.
         */
        private void entries(Map<?, ?> left, Map<?, ?> right, Class<?> c, Locus path, Parts parts) {
            if (left.size() != right.size()) {
                say(path, c, Kind.DIFFERENT_THINGS);
                parts.theSameThing = false;
                return;
            }
            if (!pairedOneToOne(left.keySet(), right.keySet(),
                    path.then(new Locus.Step.MapKey()))) {
                parts.covered = false;
                return;
            }
            // Asked here and not left to the rule that judges a thing on its parts. A map's
            // equality has a half that can be put on its own — whether the two hold the same keys —
            // and the answer to that does not depend on what the values did. Left to the whole, a
            // map comparing its keys by address goes unnamed for as long as anything under it also
            // fails to compare, so wrapping something already written down in one of them would add
            // no line.
            if (!left.keySet().equals(right.keySet())) {
                say(path.then(new Locus.Step.MapKey()), c, Kind.THE_SAME_THING_TWICE);
                parts.alreadySaid = true;
            }
            Map<Object, Object> theirs = new HashMap<>();
            for (Map.Entry<?, ?> each : right.entrySet()) {
                theirs.put(each.getKey(), each.getValue());
            }
            for (Map.Entry<?, ?> each : left.entrySet()) {
                parts.and(at(each.getValue(), theirs.get(each.getKey()),
                        path.then(new Locus.Step.MapValue())));
            }
        }
    }

    /** What one pair came to, and what was found under it, as paths relative to it. */
    private record Settled(Walk.Came came, List<Divergence> found) {}

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
