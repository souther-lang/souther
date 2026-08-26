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
    }

    private AGraphNobodyChose() {
    }

    /** A recipe of at most {@code depth} steps, grown from {@code random}. */
    static Recipe recipe(Random random, int depth) {
        if (depth <= 0) {
            return random.nextInt(4) == 0 ? new Recipe.Itself()
                    : new Recipe.Says("v" + random.nextInt(3));
        }
        return switch (random.nextInt(10)) {
            case 0 -> new Recipe.Says("v" + random.nextInt(3));
            case 1 -> new Recipe.Itself();
            case 2 -> new Recipe.Made(parts(random, depth));
            case 3 -> new Recipe.InAList(parts(random, depth));
            case 4 -> new Recipe.InASet(parts(random, depth));
            case 5 -> new Recipe.UnderKeys(parts(random, depth));
            case 6 -> new Recipe.BehindAnAbsence(recipe(random, depth - 1));
            case 7 -> new Recipe.UnderAddresses(parts(random, depth));
            case 8 -> new Recipe.WithNoRule(parts(random, depth));
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
     * <p>Worked out from the recipe and from {@code equals}, and from nothing else. What a walk of
     * the two should find is not a matter of opinion: two graphs of one shape are one thing, so
     * anything in them that denies its twin is a defect — and it is that thing's own defect exactly
     * where every part of it agreed with its twin, because a thing whose part denies is a thing
     * denying for a reason.
     *
     * <p>This does not walk the graphs the way the mechanism does. It takes the shape it was told
     * and asks each pair the one question the language answers, which is what makes it something to
     * measure the mechanism against rather than the mechanism written twice.
     */
    static int denialsIn(Recipe recipe, Object a, Object b) {
        return denials(recipe, a, b, new int[1]);
    }

    private static int denials(Recipe recipe, Object a, Object b, int[] counted) {
        boolean partsAgree = true;
        switch (recipe) {
            case Recipe.Says _, Recipe.Itself _ -> { }
            case Recipe.Made(List<Recipe> of) ->
                    partsAgree = parts(of, ((Node) a).parts(), ((Node) b).parts(), counted);
            case Recipe.InAList(List<Recipe> of) ->
                    partsAgree = parts(of, List.copyOf((List<?>) a), List.copyOf((List<?>) b),
                            counted);
            // A set is where the mechanism pairs and stops: a member it pairs is equal to the
            // other side, so nothing under one is ever reported and nothing under one is expected.
            case Recipe.InASet _ -> { }
            case Recipe.UnderKeys(List<Recipe> under) -> {
                // Read after, and never as a compound assignment: what is counted under the map is
                // counted while this runs, and adding to a number read before it would drop it.
                int own = ofAMap(under, (Map<?, ?>) a, (Map<?, ?>) b, counted);
                counted[0] = counted[0] + own;
                return counted[0];
            }
            case Recipe.UnderAddresses(List<Recipe> under) -> {
                int own = ofAMap(under, (Map<?, ?>) a, (Map<?, ?>) b, counted);
                counted[0] = counted[0] + own;
                return counted[0];
            }
            case Recipe.BehindAnAbsence(Recipe of) -> partsAgree = parts(List.of(of),
                    List.of(((Optional<?>) a).orElseThrow()),
                    List.of(((Optional<?>) b).orElseThrow()), counted);
            case Recipe.InAnArray(List<Recipe> of) -> partsAgree = parts(of,
                    List.of((Object[]) a), List.of((Object[]) b), counted);
            case Recipe.WithNoRule _ -> throw new IllegalArgumentException(
                    "a shape the mechanism says it cannot pair is not one to expect a count from");
        }
        if (!a.equals(b) && partsAgree) {
            counted[0]++;
        }
        return counted[0];
    }

    /**
     * Whether a map denies being what it is, counting it once however many ways it does.
     *
     * <p>A map's equality has two halves and either of them can be the defect: it may hold keys that
     * mean the same and say it does not, and it may deny its twin while every value agreed. Both are
     * one map denying, so it is one line.
     */
    private static int ofAMap(List<Recipe> of, Map<?, ?> a, Map<?, ?> b, int[] counted) {
        boolean valuesAgree = parts(of, values(a), values(b), counted);
        boolean keysDeny = !a.keySet().equals(b.keySet());
        return keysDeny || (!a.equals(b) && valuesAgree) ? 1 : 0;
    }

    private static List<Object> values(Map<?, ?> of) {
        List<Object> out = new ArrayList<>();
        for (Object key : KEYS) {
            for (Map.Entry<?, ?> each : of.entrySet()) {
                if (key.equals(each.getKey())) {
                    out.add(each.getValue());
                }
            }
        }
        return out;
    }

    private static boolean parts(List<Recipe> of, List<?> mine, List<?> theirs, int[] counted) {
        boolean agree = true;
        for (int i = 0; i < of.size(); i++) {
            denials(of.get(i), mine.get(i), theirs.get(i), counted);
            agree &= mine.get(i).equals(theirs.get(i));
        }
        return agree;
    }

    private static boolean any(List<Recipe> of) {
        return of.stream().anyMatch(AGraphNobodyChose::holdsSomethingWithNoRule);
    }

    /** Whether a shape holds one the mechanism says it has no rule for pairing. */
    static boolean holdsSomethingWithNoRule(Recipe recipe) {
        return switch (recipe) {
            case Recipe.WithNoRule _ -> true;
            case Recipe.Says _, Recipe.Itself _ -> false;
            case Recipe.BehindAnAbsence(Recipe of) -> holdsSomethingWithNoRule(of);
            case Recipe.Made(List<Recipe> made) -> any(made);
            case Recipe.InAList(List<Recipe> inAList) -> any(inAList);
            case Recipe.InASet(List<Recipe> inASet) -> any(inASet);
            case Recipe.UnderKeys(List<Recipe> underKeys) -> any(underKeys);
            case Recipe.UnderAddresses(List<Recipe> underAddresses) -> any(underAddresses);
            case Recipe.InAnArray(List<Recipe> inAnArray) -> any(inAnArray);
        };
    }
}
