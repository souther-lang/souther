package souther.compiler.query;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Random;

/**
 * Object graphs nobody chose, grown from a recipe and built twice.
 *
 * <p>What the walks here promise holds of every graph, and what has been asked of them is the graphs
 * whoever wrote the fixture thought of. A fixture and the mechanism under it share an author, so the
 * two agree with each other and neither is measured against the promise — which is how a container
 * comparing by address came to be found only where nothing under it also failed, how two containers
 * of one contract came to be called two answers, and how three rounds of review each found the shape
 * the round before had not imagined.
 *
 * <p>So the shapes are grown. A recipe says what a shape is without saying which objects are in it;
 * built twice, it gives two graphs that are the same thing wherever every leaf of it says something,
 * and two that are the same thing and deny it wherever a leaf only says itself. That is all a
 * property has to know about them, and it is not something an author chose.
 *
 * <p>The seed is fixed. A run that failed on numbers nobody can get back says a mechanism is wrong
 * somewhere and leaves nowhere to look.
 */
final class AGraphNobodyChose {

    /** Something that says which object it is and nothing else. */
    static final class Address {}

    /** A thing made of parts, whose equality is its parts'. */
    record Node(List<Object> parts) {}

    /** What a shape is, said without saying which objects are in it. */
    sealed interface Recipe {

        /** A leaf that says what it is, so two of them are equal. */
        record Says(String what) implements Recipe {}

        /** A leaf that says only which object it is, so two of them never are. */
        record Itself() implements Recipe {}

        /** Parts under a record, whose equality is its parts'. */
        record Made(List<Recipe> of) implements Recipe {}

        /** Parts in a list, whose equality is position. */
        record InAList(List<Recipe> of) implements Recipe {}

        /** Parts in a set, whose equality is membership. */
        record InASet(List<Recipe> of) implements Recipe {}

        /** Parts under keys that say what they are. */
        record UnderKeys(List<Recipe> of) implements Recipe {}

        /** One part behind an absence. */
        record BehindAnAbsence(Recipe of) implements Recipe {}

        /** Parts in an array, whose equality is its address whatever it holds. */
        record InAnArray(List<Recipe> of) implements Recipe {}

        /** Parts under one key object, in a map that compares by address. */
        record UnderAddresses(List<Recipe> of) implements Recipe {}

        /** Parts in a collection whose equality is neither its order nor what it holds. */
        record WithNoRule(List<Recipe> of) implements Recipe {}

        /**
         * Parts under something that wrote its own equality, and wrote it over its address.
         *
         * <p>The axis that was missing. A leaf that only says which object it is and a record whose
         * equality is its parts' were both here; a thing that has parts and whose own equality is
         * its address was not, so no number of shapes reached the one case where telling the two
         * apart matters.
         */
        record WithOwnIdentity(List<Recipe> of) implements Recipe {}
    }

    /** Something with parts, whose equality is its address. */
    static final class OwnIdentity {

        private final List<Object> parts;

        OwnIdentity(List<Object> parts) {
            this.parts = parts;
        }

        List<Object> parts() {
            return parts;
        }

        @Override
        public boolean equals(Object other) {
            return this == other;
        }

        @Override
        public int hashCode() {
            return System.identityHashCode(this);
        }
    }

    private AGraphNobodyChose() {
    }

    /** A recipe of at most {@code depth} steps, grown from {@code random}. */
    static Recipe recipe(Random random, int depth) {
        if (depth <= 0) {
            return random.nextInt(4) == 0 ? new Recipe.Itself()
                    : new Recipe.Says("v" + random.nextInt(3));
        }
        return switch (random.nextInt(11)) {
            case 0 -> new Recipe.Says("v" + random.nextInt(3));
            case 1 -> new Recipe.Itself();
            case 2 -> new Recipe.Made(parts(random, depth));
            case 3 -> new Recipe.InAList(parts(random, depth));
            case 4 -> new Recipe.InASet(parts(random, depth));
            case 5 -> new Recipe.UnderKeys(parts(random, depth));
            case 6 -> new Recipe.BehindAnAbsence(recipe(random, depth - 1));
            case 7 -> new Recipe.UnderAddresses(parts(random, depth));
            case 8 -> new Recipe.WithNoRule(parts(random, depth));
            case 9 -> new Recipe.WithOwnIdentity(parts(random, depth));
            default -> new Recipe.InAnArray(parts(random, depth));
        };
    }

    private static List<Recipe> parts(Random random, int depth) {
        List<Recipe> out = new ArrayList<>();
        for (int i = 0; i <= random.nextInt(3); i++) {
            out.add(recipe(random, depth - 1));
        }
        return out;
    }

    /**
     * One graph of that shape, built the way {@code random} picks.
     *
     * <p><b>The two sides are built apart.</b> A recipe says what a shape is, and what class carries
     * it is not part of that: a list is a list whichever list it is. Built once and handed to both
     * sides, every pair would be of one concrete class — which is a shape this mechanism has to be
     * right about and the shape it was wrong about, since a list and a linked list holding one thing
     * are one value and were being called two answers.
     *
     * <p>The key a map that compares by address is given is the same object on both sides, so the
     * two line up by address as well as by what they say. Given fresh keys, the pairing fails and
     * the pair says so — which is a different thing this is also about, and it happens where the
     * keys are what {@link Recipe.UnderKeys} makes.
     */
    // The point of the list and map arms is that one contract is met by several classes, so the
    // ones nobody would choose for their speed are exactly the ones wanted here.
    @SuppressWarnings("JdkObsolete")
    static Object built(Recipe recipe, Random random) {
        return switch (recipe) {
            case Recipe.Says(String what) -> what;
            case Recipe.Itself _ -> new Address();
            case Recipe.Made(List<Recipe> of) -> new Node(each(of, random));
            case Recipe.InAList(List<Recipe> of) -> switch (random.nextInt(3)) {
                case 0 -> new ArrayList<>(each(of, random));
                case 1 -> new java.util.LinkedList<>(each(of, random));
                default -> List.copyOf(each(of, random));
            };
            case Recipe.InASet(List<Recipe> of) -> random.nextBoolean()
                    ? new LinkedHashSet<>(each(of, random))
                    : new java.util.HashSet<>(each(of, random));
            case Recipe.UnderKeys(List<Recipe> of) -> keyed(random.nextInt(3) == 0
                    ? new java.util.TreeMap<>()
                    : random.nextBoolean() ? new LinkedHashMap<>() : new java.util.HashMap<>(),
                    of, random);
            // Keys that mean the same and are two objects, which is every key of one of these
            // across two stores — and which is what makes the half of its equality that is about
            // keys something to judge on its own.
            case Recipe.UnderAddresses(List<Recipe> of) ->
                    freshlyKeyed(new java.util.IdentityHashMap<>(), of, random);
            case Recipe.BehindAnAbsence(Recipe of) -> Optional.of(built(of, random));
            case Recipe.InAnArray(List<Recipe> of) -> each(of, random).toArray();
            case Recipe.WithNoRule(List<Recipe> of) ->
                    new java.util.ArrayDeque<>(each(of, random));
            case Recipe.WithOwnIdentity(List<Recipe> of) -> new OwnIdentity(each(of, random));
        };
    }

    /** Parts under keys that are the same objects whichever side builds them, so that a map
     *  comparing by address lines its keys up and is judged on what it does with them. */
    private static Map<Object, Object> keyed(Map<Object, Object> into, List<Recipe> of,
                                             Random random) {
        List<Object> parts = each(of, random);
        for (int i = 0; i < parts.size(); i++) {
            into.put(KEYS[i], parts.get(i));
        }
        return into;
    }

    /** Interned, so both sides hold the same key object. */
    private static final String[] KEYS = {"k0", "k1", "k2", "k3"};

    /** The same keys, made afresh on each side. */
    private static Map<Object, Object> freshlyKeyed(Map<Object, Object> into, List<Recipe> of,
                                                    Random random) {
        List<Object> parts = each(of, random);
        for (int i = 0; i < parts.size(); i++) {
            into.put(new String(KEYS[i]), parts.get(i));
        }
        return into;
    }

    private static List<Object> each(List<Recipe> of, Random random) {
        List<Object> out = new ArrayList<>();
        of.forEach(one -> out.add(built(one, random)));
        return out;
    }

    /**
     * How many things in two graphs of one shape deny being what they are.
     *
     * <p>Found by experiment and not by a rule. Whether a thing's denial is its own is the question
     * the mechanism answers, so an expectation worked out by the same reasoning would agree with it
     * wherever the reasoning is wrong — which is what a property is here to not do. So each shape is
     * built again with every part of it replaced by something that says what it is, and asked
     * whether it still denies its twin. A record of honest parts agrees; an array of them does not,
     * because an array is its address whatever it holds.
     *
     * <p>What is counted is every place the walk reaches. A set is where it pairs and stops, so what
     * is inside one is not among them.
     */
    static int denialsIn(Recipe recipe) {
        return denials(recipe);
    }

    private static int denials(Recipe recipe) {
        int out = deniesWithHonestParts(recipe) ? 1 : 0;
        switch (recipe) {
            case Recipe.Says _, Recipe.Itself _, Recipe.WithNoRule _ -> { }
            // A set is where the walk pairs and stops, so nothing inside one is reached.
            case Recipe.InASet _ -> { }
            case Recipe.BehindAnAbsence(Recipe of) -> out += denials(of);
            case Recipe.Made(List<Recipe> of) -> out += under(of);
            case Recipe.InAList(List<Recipe> of) -> out += under(of);
            case Recipe.UnderKeys(List<Recipe> of) -> out += under(of);
            case Recipe.UnderAddresses(List<Recipe> of) -> out += under(of);
            case Recipe.InAnArray(List<Recipe> of) -> out += under(of);
            case Recipe.WithOwnIdentity(List<Recipe> of) -> out += under(of);
        }
        return out;
    }

    private static int under(List<Recipe> of) {
        int out = 0;
        for (Recipe one : of) {
            out += denials(one);
        }
        return out;
    }

    /**
     * Whether two of this shape deny each other when everything under them says what it is.
     *
     * <p>The experiment. Built twice with every part replaced by a thing that means what it says,
     * anything left denying is denying on its own account — and anything that agrees was only ever
     * denying because a part did.
     */
    private static boolean deniesWithHonestParts(Recipe recipe) {
        Recipe honest = withHonestParts(recipe);
        Random same = new Random(SEED_FOR_THE_EXPERIMENT);
        Object one = built(honest, same);
        Object other = built(honest, new Random(SEED_FOR_THE_EXPERIMENT));
        return !one.equals(other);
    }

    /** Fixed, so the experiment answers the same thing every time it is put. */
    private static final long SEED_FOR_THE_EXPERIMENT = 1103;

    private static final Recipe HONEST = new Recipe.Says("h");

    private static Recipe withHonestParts(Recipe recipe) {
        return switch (recipe) {
            case Recipe.Says _, Recipe.Itself _ -> recipe;
            case Recipe.BehindAnAbsence _ -> new Recipe.BehindAnAbsence(HONEST);
            case Recipe.Made(List<Recipe> of) -> new Recipe.Made(honestly(of));
            case Recipe.InAList(List<Recipe> of) -> new Recipe.InAList(honestly(of));
            case Recipe.InASet(List<Recipe> of) -> new Recipe.InASet(honestly(of));
            case Recipe.UnderKeys(List<Recipe> of) -> new Recipe.UnderKeys(honestly(of));
            case Recipe.UnderAddresses(List<Recipe> of) ->
                    new Recipe.UnderAddresses(honestly(of));
            case Recipe.InAnArray(List<Recipe> of) -> new Recipe.InAnArray(honestly(of));
            case Recipe.WithNoRule(List<Recipe> of) -> new Recipe.WithNoRule(honestly(of));
            case Recipe.WithOwnIdentity(List<Recipe> of) ->
                    new Recipe.WithOwnIdentity(honestly(of));
        };
    }

    private static List<Recipe> honestly(List<Recipe> of) {
        List<Recipe> out = new ArrayList<>();
        of.forEach(_ -> out.add(HONEST));
        return out;
    }

    private static boolean any(List<Recipe> of) {
        return anyOnlyItself(of);
    }

    private static boolean anyWithNoRule(List<Recipe> of) {
        return of.stream().anyMatch(AGraphNobodyChose::holdsSomethingWithNoRule);
    }

    /**
     * Where a walk of two graphs of this shape is expected to fall short, and why.
     *
     * <p>Said from the shape rather than read off what happened. A walk that gave up is a walk that
     * says less than it was asked to, so a property that skipped whatever came back that way would
     * be one anything could escape by giving up — and the graphs it lets through are the ones nobody
     * wrote down, which is what this whole thing is for.
     *
     * <p>Two shapes fall short and no others. A collection whose equality is neither its order nor
     * what it holds has no rule for pairing, and a set of things that only say which object they are
     * has members that will not line up one to one.
     */
    static java.util.Set<Gap.Why> fallsShortOn(Recipe recipe) {
        java.util.Set<Gap.Why> out = new java.util.LinkedHashSet<>();
        collectFallingShort(recipe, out);
        return out;
    }

    /**
     * @return whether the walk gave up somewhere at or under this shape, so that whatever the shape
     *     above it would have asked is never asked
     */
    private static boolean collectFallingShort(Recipe recipe, java.util.Set<Gap.Why> out) {
        switch (recipe) {
            case Recipe.WithNoRule _ -> {
                out.add(Gap.Why.A_CONTAINER_WITH_NO_RULE_FOR_PAIRING);
                return true;
            }
            case Recipe.Says _, Recipe.Itself _ -> {
                return false;
            }
            case Recipe.BehindAnAbsence(Recipe of) -> {
                return collectFallingShort(of, out);
            }
            // A set is where the walk pairs and stops, so nothing inside one is reached and what
            // can fall short is the pairing.
            case Recipe.InASet(List<Recipe> of) -> {
                if (anyOnlyItself(of)) {
                    out.add(Gap.Why.MEMBERS_THAT_DO_NOT_PAIR);
                    return true;
                }
                return false;
            }
            // Something that wrote its own equality: where a part of it denies, no walk can say
            // whose denial its denial is — but only where the walk got as far as asking, which it
            // does not where a part of it gave up first.
            case Recipe.WithOwnIdentity(List<Recipe> of) -> {
                boolean below = under(of, out);
                if (!below && anyOnlyItself(of)) {
                    out.add(Gap.Why.WHOSE_DENIAL_THIS_IS_CANNOT_BE_TOLD);
                    return true;
                }
                return below;
            }
            case Recipe.Made(List<Recipe> of) -> {
                return under(of, out);
            }
            case Recipe.InAList(List<Recipe> of) -> {
                return under(of, out);
            }
            case Recipe.UnderKeys(List<Recipe> of) -> {
                return under(of, out);
            }
            case Recipe.UnderAddresses(List<Recipe> of) -> {
                return under(of, out);
            }
            case Recipe.InAnArray(List<Recipe> of) -> {
                return under(of, out);
            }
        }
    }

    private static boolean under(List<Recipe> of, java.util.Set<Gap.Why> out) {
        boolean any = false;
        for (Recipe one : of) {
            any |= collectFallingShort(one, out);
        }
        return any;
    }

    /** Whether two things of this shape are never equal, which is what stops a set pairing. */
    private static boolean saysOnlyWhichObjectItIs(Recipe recipe) {
        return switch (recipe) {
            case Recipe.Itself _ -> true;
            case Recipe.Says _ -> false;
            // An array is its address, so two of them are never equal whatever they hold.
            case Recipe.InAnArray _ -> true;
            // And a map that compares by address is never equal to another of it either.
            case Recipe.UnderAddresses _ -> true;
            case Recipe.WithOwnIdentity _ -> true;
            case Recipe.BehindAnAbsence(Recipe of) -> saysOnlyWhichObjectItIs(of);
            case Recipe.Made(List<Recipe> of) -> any(of);
            case Recipe.InAList(List<Recipe> of) -> any(of);
            case Recipe.InASet(List<Recipe> of) -> any(of);
            case Recipe.UnderKeys(List<Recipe> of) -> any(of);
            case Recipe.WithNoRule _ -> true;
        };
    }

    private static boolean anyOnlyItself(List<Recipe> of) {
        return of.stream().anyMatch(AGraphNobodyChose::saysOnlyWhichObjectItIs);
    }

    /** Whether a shape holds one the mechanism says it has no rule for pairing. */
    static boolean holdsSomethingWithNoRule(Recipe recipe) {
        return switch (recipe) {
            case Recipe.WithNoRule _ -> true;
            case Recipe.Says _, Recipe.Itself _ -> false;
            case Recipe.BehindAnAbsence(Recipe of) -> holdsSomethingWithNoRule(of);
            case Recipe.Made(List<Recipe> made) -> anyWithNoRule(made);
            case Recipe.InAList(List<Recipe> inAList) -> anyWithNoRule(inAList);
            case Recipe.InASet(List<Recipe> inASet) -> anyWithNoRule(inASet);
            case Recipe.UnderKeys(List<Recipe> underKeys) -> anyWithNoRule(underKeys);
            case Recipe.UnderAddresses(List<Recipe> underAddresses) -> anyWithNoRule(underAddresses);
            case Recipe.InAnArray(List<Recipe> inAnArray) -> anyWithNoRule(inAnArray);
            case Recipe.WithOwnIdentity(List<Recipe> own) -> anyWithNoRule(own);
        };
    }
}
