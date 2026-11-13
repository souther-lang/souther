package souther.compiler;

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
import java.util.OptionalLong;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.function.IntFunction;
import java.util.function.Supplier;
import java.util.stream.Stream;

/**
 * What a reader of a graph of values costs on a chain of them, so that a reader that goes down the
 * graph as a tree is told by what it costs and not by being looked for.
 *
 * <p>A value used twice is one object held in two places, so the values made of it are a graph, and
 * the ways down a chain of values each holding the one before it twice are two to its length. A
 * reader of the values takes about as long on a chain of {@link #LONG} as on one of {@link #SHORT};
 * one that goes down every way takes two to the difference as long, which is what it is told by.
 * What it costs is not asked, so that this does not turn on how fast a machine is.
 *
 * <p>Asked of every static method of the compiler whose first parameter is the value, and of the
 * methods the value (or what wraps it) has. A method that refuses — throws — is not asked: what it
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

    /** Under this a reader on the longer chain is too quick for the ratio to say anything. */
    private static final long NANOS_TOO_SHORT_TO_TELL = 20_000_000L;

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

    /** What was asked and what was found slow. */
    public record Findings(int asked, Set<String> slow) {}

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

    /** Whether the reader answered; one that refuses throws. */
    private static boolean ask(Method method, boolean aMethodOfIt, Object[] others, Object chain)
            throws ReflectiveOperationException {
        Object[] args = others.clone();
        if (!aMethodOfIt) {
            args[0] = chain;
        }
        try {
            method.invoke(aMethodOfIt ? chain : null, args);
            return true;
        } catch (InvocationTargetException refused) {
            return false;
        }
    }

    /** The fastest of three askings, which is what the reader costs when nothing else is running;
     *  none where it refuses. */
    private static OptionalLong fastest(Method method, boolean aMethodOfIt, Object[] others,
                                        Object chain) throws ReflectiveOperationException {
        long best = Long.MAX_VALUE;
        for (int times = 0; times < 3; times++) {
            long start = System.nanoTime();
            if (!ask(method, aMethodOfIt, others, chain)) {
                return OptionalLong.empty();
            }
            best = Math.min(best, System.nanoTime() - start);
        }
        return OptionalLong.of(best);
    }

    /** Whether {@code onLong} is the ways down to what {@code onShort} is the values of. */
    private static boolean goesDownEveryWay(long onShort, long onLong) {
        return onLong > NANOS_TOO_SHORT_TO_TELL
                && onLong > GROWTH_THAT_IS_THE_WAYS * Math.max(onShort, 100_000L);
    }

    private static long fastestMaking(Chain chain, int length) {
        long best = Long.MAX_VALUE;
        for (int times = 0; times < 3; times++) {
            long start = System.nanoTime();
            chain.ofLength().apply(length);
            best = Math.min(best, System.nanoTime() - start);
        }
        return best;
    }

    /**
     * Every reader of {@code chains} that goes down every way, by the name of the class and the
     * method and the chain it was slow on; and how many readers were asked.
     *
     * @param byTheirNature readers whose work is the ways down, which is what they are for, by the
     *                      name of the class and the method, with why
     */
    public static Findings askEach(List<Chain> chains, Map<String, String> byTheirNature)
            throws IOException, ReflectiveOperationException, InterruptedException {
        Map<Chain, Object> shorter = new LinkedHashMap<>();
        Map<Chain, Object> longer = new LinkedHashMap<>();
        Set<String> slow = new TreeSet<>();
        for (Chain chain : chains) {
            shorter.put(chain, chain.ofLength().apply(SHORT));
            longer.put(chain, chain.ofLength().apply(LONG));
            if (goesDownEveryWay(fastestMaking(chain, SHORT), fastestMaking(chain, LONG))) {
                slow.add("making " + chain.label());
            }
        }
        ExecutorService pool = Executors.newCachedThreadPool(each -> {
            Thread thread = new Thread(each);
            thread.setDaemon(true);
            return thread;
        });
        int asked = 0;
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
                    Object[] others = new Object[method.getParameterCount()];
                    boolean made = true;
                    for (int at = aMethodOfIt ? 0 : 1; at < others.length; at++) {
                        others[at] = other(method.getParameterTypes()[at], chain);
                        made &= others[at] != null;
                    }
                    if (!made) {
                        continue;
                    }
                    method.setAccessible(true);
                    asked++;
                    String told = name + " on " + chain.label();
                    try {
                        pool.submit(() -> {
                            OptionalLong onShort = fastest(method, aMethodOfIt, others,
                                    shorter.get(chain));
                            OptionalLong onLong = fastest(method, aMethodOfIt, others,
                                    longer.get(chain));
                            if (onShort.isPresent() && onLong.isPresent()
                                    && goesDownEveryWay(onShort.getAsLong(), onLong.getAsLong())) {
                                synchronized (slow) {
                                    slow.add(told);
                                }
                            }
                            return null;
                        }).get(120, TimeUnit.SECONDS);
                    } catch (TimeoutException wayTooLong) {
                        slow.add(told);
                    } catch (ExecutionException failed) {
                        throw new IllegalStateException(told, failed.getCause());
                    }
                }
            }
        }
        pool.shutdownNow();
        return new Findings(asked, slow);
    }
}
