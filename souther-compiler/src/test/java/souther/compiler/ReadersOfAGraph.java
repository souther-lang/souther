package souther.compiler;

import souther.test.Visits;

import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.IntFunction;
import java.util.function.Supplier;
import java.util.stream.Stream;

/**
 * What a reader of a graph of values costs on a chain of them, so that a reader that goes down the
 * graph as a tree is told by what it costs and not by being looked for.
 *
 * <p>A value used twice is one object held in two places, so the values made of it are a graph, and
 * the ways down a chain of values each holding the one before it twice are two to its length. A
 * reader of the values goes into each of them a few times; one that goes down every way goes into a
 * chain of {@link #LONG} two to that many times, which is what it is told by ({@link Visits}). What
 * it goes into is counted and time is not, so this does not turn on how fast a machine is, and a
 * reader that allocates nothing is told as one that does. A chain of {@link #SHORT} is asked first
 * and without counting, for whether the reader answers or refuses.
 *
 * <p>Asked of every static method of the compiler whose first parameter is the value, and of the
 * methods the value (or what wraps it) has. A method that refuses — throws — is said of apart ({@link Findings}): what it
 * costs to say so, a message naming the value, is not what a reader of the values costs. The
 * methods are found and not listed, so a reader written later is asked as the rest are.
 */
public final class ReadersOfAGraph {

    /** The shorter chain. */
    public static final int SHORT = 14;

    /** The longer chain. */
    public static final int LONG = 22;

    /** Two to {@code LONG - SHORT} is 256; a reader of the values is nowhere near this. */
    private static final long GROWTH_THAT_IS_THE_WAYS = 16;

    /** Under this a reader on the shorter chain goes into too few values for the ratio to say anything. */
    private static final long VISITS_TOO_FEW_TO_TELL = 64;

    /** Readers that go into the longer chain this often are the ones whose growth is asked: the
     *  ways down it are two to {@link #LONG}, sixty-four times this. */
    private static final long VISITS_THAT_ARE_THE_WAYS = 1L << 16;

    /** How many readers are counted together, before the ones past the figure are told apart. */
    private static final int ASKED_TOGETHER = 64;

    /** What a piece of a reading takes: the reading it is a piece of. */
    private static final Set<String> IN_A_READING = Set.of("StatementReading", "EachOnce",
            "InContext");

    private ReadersOfAGraph() {
    }

    /**
     * A chain of values to ask of, and what is asked of it.
     *
     * @param label  what the chain is, said beside a reader it is slow on
     * @param type   the type whose static readers take the chain as the first argument, and whose
     *               methods have it as the receiver
     * @param ofLength the chain of that many values
     * @param made   what to give a parameter of a type that is not made here: a map, a list, a
     *               boolean and a number are
     */
    public record Chain(String label, Class<?> type, IntFunction<Object> ofLength,
                        Map<Class<?>, Supplier<Object>> made) {

        public Chain(String label, Class<?> type, IntFunction<Object> ofLength) {
            this(label, type, ofLength, Map.of());
        }
    }

    /**
     * What was asked, and what came of it, each by the name of the class, the method and the chain.
     *
     * @param answered a reader that answered on both chains, which is what it costs is told of
     * @param refused  a reader that threw on one of them, which a chain of this kind may be one
     *                 for: nothing is said of what it costs
     * @param notAsked a reader with a parameter that is not made, so that it was not asked
     * @param slow     a reader that goes down every way
     */
    public record Findings(Set<String> answered, Set<String> refused, Set<String> notAsked,
                           Set<String> slow) {}

    private static Object other(Class<?> type, Chain chain) {
        Supplier<Object> made = chain.made().get(type);
        if (made != null) {
            return made.get();
        }
        if (type == Map.class) {
            return new LinkedHashMap<>();
        }
        if (type == List.class || type == Collection.class) {
            return new ArrayList<>();
        }
        if (type == Set.class) {
            return new LinkedHashSet<>();
        }
        if (type == boolean.class) {
            return false;
        }
        if (type == int.class) {
            return 0;
        }
        if (type == long.class) {
            return 0L;
        }
        return null;
    }

    /** The classes of the compiler, and those nested in them. */
    public static List<Class<?>> classesOfTheCompiler() throws IOException {
        Path main = Path.of("src/main/java/souther/compiler");
        List<Class<?>> out = new ArrayList<>();
        try (Stream<Path> sources = Files.walk(main)) {
            for (Path source : (Iterable<Path>) sources
                    .filter(each -> each.toString().endsWith(".java"))::iterator) {
                String name = "souther.compiler." + main.relativize(source).toString()
                        .replace('/', '.').replaceAll("\\.java$", "");
                try {
                    addWithNested(Class.forName(name, false,
                            ReadersOfAGraph.class.getClassLoader()), out);
                } catch (ClassNotFoundException | LinkageError notAClass) {
                    // package-info and the like.
                }
            }
        }
        return out;
    }

    private static void addWithNested(Class<?> owner, List<Class<?>> into) {
        into.add(owner);
        for (Class<?> nested : owner.getDeclaredClasses()) {
            addWithNested(nested, into);
        }
    }

    /** The arguments of a method but the graph, made anew: the graph is the receiver of a method
     *  of it and the first argument of a static one, and is put in by the one that asks. */
    private static Object[] argumentsOf(Method method, boolean aMethodOfIt, Chain chain) {
        Object[] out = new Object[method.getParameterCount()];
        for (int at = aMethodOfIt ? 0 : 1; at < out.length; at++) {
            out[at] = other(method.getParameterTypes()[at], chain);
        }
        return out;
    }

    /** The first parameter of a method that is not made, by its type, or null where all are. */
    private static String missingFrom(Method method, boolean aMethodOfIt, Chain chain) {
        Object[] made = argumentsOf(method, aMethodOfIt, chain);
        for (int at = aMethodOfIt ? 0 : 1; at < made.length; at++) {
            if (made[at] == null) {
                return method.getParameterTypes()[at].getSimpleName();
            }
        }
        return null;
    }

    /**
     * What the reader answers on a chain of {@code length}, or nothing where it refuses.
     *
     * <p>The chain and the arguments are made for this asking: a reader that gathers into the
     * collection it is handed, or that the compiler keeps something of by what a statement is equal
     * to, is asked of nothing a previous asking left. What it answers is wrapped, so that an answer
     * of nothing is told from a refusal.
     */
    private static Optional<Optional<Object>> answerOn(Method method, boolean aMethodOfIt,
                                                       Supplier<Object[]> others, Chain of,
                                                       int length) {
        Object chain = of.ofLength().apply(length);
        Object[] args = others.get();
        if (!aMethodOfIt) {
            args[0] = chain;
        }
        try {
            return Optional.of(Optional.ofNullable(method.invoke(aMethodOfIt ? chain : null, args)));
        } catch (InvocationTargetException refusing) {
            return Optional.empty();
        } catch (IllegalAccessException notAllowed) {
            throw new IllegalStateException(method.toString(), notAllowed);
        }
    }

    /**
     * What of {@code asks} goes into the values more than {@link #VISITS_THAT_ARE_THE_WAYS} times.
     *
     * <p>The asks are counted together and told apart only where the count says one of them is past
     * the figure, by halves, so that what is counted is the few readings it takes to name the slow
     * ones and not one for each reader.
     */
    private static Set<String> past(Visits visits, List<Map.Entry<String, Ask>> asks) {
        if (asks.isEmpty()) {
            return Set.of();
        }
        Visits.Counted<List<Object>> asked = visits.count(() -> {
            List<Object> answers = new ArrayList<>();
            for (Map.Entry<String, Ask> ask : asks) {
                answers.add(ask.getValue().onLong().get());
            }
            return answers;
        });
        if (asked.visits() <= VISITS_THAT_ARE_THE_WAYS) {
            return Set.of();
        }
        if (asks.size() == 1) {
            return goesDownEveryWay(visits, asks.getFirst().getValue())
                    ? Set.of(asks.getFirst().getKey()) : Set.of();
        }
        Set<String> slow = new TreeSet<>();
        int half = asks.size() / 2;
        slow.addAll(past(visits, asks.subList(0, half)));
        slow.addAll(past(visits, asks.subList(half, asks.size())));
        return slow;
    }

    /**
     * Whether a reader that goes into the values often is going down every way: it goes into the
     * longer chain more than the ways down it is longer by as often as into the shorter. A reader
     * that goes into each value many times goes into twice the values twice as often.
     */
    private static boolean goesDownEveryWay(Visits visits, Ask ask) {
        long onShort = visits.count(ask.onShort()).visits();
        long onLong = visits.count(ask.onLong()).visits();
        return onLong > GROWTH_THAT_IS_THE_WAYS * Math.max(onShort, VISITS_TOO_FEW_TO_TELL);
    }

    private static Set<String> past(Visits visits, Map<String, Ask> asks) {
        Set<String> slow = new TreeSet<>();
        List<Map.Entry<String, Ask>> all = new ArrayList<>(asks.entrySet());
        for (int from = 0; from < all.size(); from += ASKED_TOGETHER) {
            slow.addAll(past(visits, all.subList(from, Math.min(all.size(), from + ASKED_TOGETHER))));
        }
        return slow;
    }

    /** One reading asked on the shorter chain and on the longer. */
    private record Ask(Supplier<Object> onShort, Supplier<Object> onLong) {}

    /**
     * Every reader of {@code chains} that goes down every way, by the name of the class and the
     * method and the chain it was slow on; and how many readers were asked.
     *
     * @param byTheirNature readers whose work is the ways down, which is what they are for, by the
     *                      name of the class and the method, with why
     */
    public static Findings askEach(List<Chain> chains, Map<String, String> byTheirNature)
            throws IOException {
        try (Visits visits = Visits.into(chains.stream().<Class<?>>map(Chain::type).toList())) {
            return askEach(visits, chains, byTheirNature);
        }
    }

    private static Findings askEach(Visits visits, List<Chain> chains,
                                    Map<String, String> byTheirNature) throws IOException {
        Map<String, Ask> asks = new LinkedHashMap<>();
        for (Chain chain : chains) {
            asks.put("making " + chain.label(), new Ask(() -> chain.ofLength().apply(SHORT),
                    () -> chain.ofLength().apply(LONG)));
        }
        Set<String> answered = new TreeSet<>();
        Set<String> refused = new TreeSet<>();
        Set<String> notAsked = new TreeSet<>();
        for (Class<?> owner : classesOfTheCompiler()) {
            Method[] methods;
            try {
                methods = owner.getDeclaredMethods();
            } catch (LinkageError unloadable) {
                continue;
            }
            for (Method method : methods) {
                String name = owner.getName().replace("souther.compiler.", "")
                        .replaceAll("^[a-z]+\\.", "") + "." + method.getName();
                if (method.isSynthetic() || byTheirNature.containsKey(name)) {
                    continue;
                }
                boolean aStatic = Modifier.isStatic(method.getModifiers());
                for (Chain chain : chains) {
                    boolean aMethodOfIt = !aStatic && owner == chain.type();
                    boolean takesIt = aStatic && method.getParameterCount() > 0
                            && method.getParameterTypes()[0] == chain.type();
                    if (!aMethodOfIt && !takesIt) {
                        continue;
                    }
                    Supplier<Object[]> others = () -> argumentsOf(method, aMethodOfIt, chain);
                    String missing = missingFrom(method, aMethodOfIt, chain);
                    String told = name + " on " + chain.label();
                    if (missing != null) {
                        // The pieces of a reading, which take the reading they are a piece of,
                        // are asked through the reading that is made of them.
                        if (!IN_A_READING.contains(missing)) {
                            notAsked.add(told + ", for want of a " + missing);
                        }
                        continue;
                    }
                    method.setAccessible(true);
                    if (answerOn(method, aMethodOfIt, others, chain, SHORT).isPresent()) {
                        answered.add(told);
                        asks.put(told, new Ask(
                                () -> answerOn(method, aMethodOfIt, others, chain, SHORT),
                                () -> answerOn(method, aMethodOfIt, others, chain, LONG)));
                    } else {
                        refused.add(told);
                    }
                }
            }
        }
        return new Findings(answered, refused, notAsked, past(visits, asks));
    }
}
