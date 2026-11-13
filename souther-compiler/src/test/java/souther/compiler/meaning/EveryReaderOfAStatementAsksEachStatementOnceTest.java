package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.test.ClosedWorldContract;

import java.io.IOException;
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
import java.util.Set;
import java.util.TreeSet;
import java.util.UUID;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every reader of a statement asks each statement once, however many statements hold it.
 *
 * <p>A condition read through a name used twice is held by two statements, so statements are a
 * graph, and the ways down a chain of names each using the one before it twice are two to its
 * length. A reader that recurses into the parts for itself pays for every way, and the readers that
 * did took longer than the whole of a compile at twenty-two names. Going down the parts is
 * {@link StatementReading}'s, and this is what keeps a reader that does not from being written.
 *
 * <p>Asked of every static method of the compiler whose first parameter is a statement, and of the
 * methods a statement has, on a chain of {@link #SHORT} names and on one of {@link #LONG}. A reader
 * of the statements takes about as long on both. One that goes down every way takes two to the
 * difference as long on the longer, which is what it is told by: what the reader costs is not
 * asked, so that the test does not turn on how fast a machine is.
 *
 * <p>The methods are found and not listed, so a reader written later is asked as the rest are, and
 * that some were found is held ({@link #AT_LEAST_ASKED}) so that this cannot come to ask none.
 */
@ClosedWorldContract
class EveryReaderOfAStatementAsksEachStatementOnceTest {

    private static final int SHORT = 14;

    private static final int LONG = 22;

    /** Two to {@code LONG - SHORT} is 256; a reader of the statements is nowhere near this. */
    private static final long GROWTH_THAT_IS_THE_WAYS = 16;

    /** Under this a reader on the longer chain is too quick for the ratio to say anything. */
    private static final long NANOS_TOO_SHORT_TO_TELL = 20_000_000L;

    /**
     * Readers whose work is the ways down, which is what they are for: a text of a statement is as
     * long as the ways down to its parts, and what a truth table is worked through for is every way
     * its distinct parts can come out.
     */
    private static final Map<String, String> BY_THEIR_NATURE = Map.of(
            "BorderQuantity$HowMany.said", "the text of the statement",
            "BorderQuantity$HowMany.grouped", "the text of the statement",
            "Proposition.spelledOut", "the text of the statement",
            "WhereEachLineDecides.held", "the message of the error it throws names the statement",
            "WhereEachLineDecides$Reading.of", "every way the distinct parts can come out",
            "TruthOutcomes.of", "every way the distinct parts can come out",
            "Proposition.toString", "the text of the statement");

    /** How many readers are asked at least, so that finding none is not a pass. */
    private static final int AT_LEAST_ASKED = 40;

    private static Proposition chainOf(int length) {
        String mine = UUID.randomUUID().toString();
        Proposition held = CompoundSamples.truth(mine + "0");
        for (int at = 1; at <= length; at++) {
            held = Proposition.all(List.of(held,
                    Proposition.any(List.of(held, CompoundSamples.truth(mine + at)))));
        }
        return held;
    }

    /** A value for a parameter that is not the statement, or null where none is made. */
    private static Object other(Class<?> type) {
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

    private static List<Class<?>> classesOfTheCompiler() throws IOException {
        Path main = Path.of("src/main/java/souther/compiler");
        List<Class<?>> out = new ArrayList<>();
        try (Stream<Path> sources = Files.walk(main)) {
            for (Path source : (Iterable<Path>) sources
                    .filter(each -> each.toString().endsWith(".java"))::iterator) {
                String name = "souther.compiler." + main.relativize(source).toString()
                        .replace('/', '.').replaceAll("\\.java$", "");
                try {
                    addWithNested(Class.forName(name, false,
                            EveryReaderOfAStatementAsksEachStatementOnceTest.class
                                    .getClassLoader()), out);
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

    /** What the reader does when it is asked of {@code chain}, the statement being the receiver
     *  of a method of one and the first argument of a static one. */
    private static void ask(Method method, boolean ofTheStatement, Object[] others,
                            Proposition chain) throws ReflectiveOperationException {
        Object[] args = others.clone();
        if (!ofTheStatement) {
            args[0] = chain;
        }
        try {
            method.invoke(ofTheStatement ? chain : null, args);
        } catch (java.lang.reflect.InvocationTargetException refused) {
            // What a reader says of a chain of truths is not what is asked here.
        }
    }

    /** The fastest of three askings, which is what the reader costs when nothing else is running. */
    private static long fastest(Method method, boolean ofTheStatement, Object[] others,
                                Proposition chain) throws ReflectiveOperationException {
        long best = Long.MAX_VALUE;
        for (int times = 0; times < 3; times++) {
            long start = System.nanoTime();
            ask(method, ofTheStatement, others, chain);
            best = Math.min(best, System.nanoTime() - start);
        }
        return best;
    }

    @Test
    void noReaderOfAStatementGoesDownEveryWayToItsParts() throws Exception {
        Proposition shorter = chainOf(SHORT);
        Proposition longer = chainOf(LONG);
        ExecutorService pool = Executors.newCachedThreadPool(each -> {
            Thread thread = new Thread(each);
            thread.setDaemon(true);
            return thread;
        });
        Set<String> goingDownEveryWay = new TreeSet<>();
        int asked = 0;
        for (Class<?> owner : classesOfTheCompiler()) {
            Method[] methods;
            try {
                methods = owner.getDeclaredMethods();
            } catch (LinkageError unloadable) {
                continue;
            }
            for (Method method : methods) {
                boolean aStatic = Modifier.isStatic(method.getModifiers());
                boolean ofTheStatement = owner == Proposition.class && !aStatic;
                boolean takesOne = aStatic && method.getParameterCount() > 0
                        && method.getParameterTypes()[0] == Proposition.class;
                String name = owner.getName().replace("souther.compiler.", "")
                        .replaceAll("^[a-z]+\\.", "") + "." + method.getName();
                if (method.isSynthetic() || !(ofTheStatement || takesOne)
                        || BY_THEIR_NATURE.containsKey(name)) {
                    continue;
                }
                Object[] others = new Object[method.getParameterCount()];
                boolean made = true;
                for (int at = ofTheStatement ? 0 : 1; at < others.length; at++) {
                    others[at] = other(method.getParameterTypes()[at]);
                    made &= others[at] != null;
                }
                if (!made) {
                    continue;
                }
                method.setAccessible(true);
                asked++;
                try {
                    pool.submit(() -> {
                        long onShort = fastest(method, ofTheStatement, others, shorter);
                        long onLong = fastest(method, ofTheStatement, others, longer);
                        if (onLong > NANOS_TOO_SHORT_TO_TELL
                                && onLong > GROWTH_THAT_IS_THE_WAYS * Math.max(onShort, 100_000L)) {
                            synchronized (goingDownEveryWay) {
                                goingDownEveryWay.add(name);
                            }
                        }
                        return null;
                    }).get(60, TimeUnit.SECONDS);
                } catch (TimeoutException wayTooLong) {
                    goingDownEveryWay.add(name);
                }
            }
        }
        pool.shutdownNow();

        assertEquals(Set.of(), goingDownEveryWay,
                "readers that take " + GROWTH_THAT_IS_THE_WAYS + " times as long on a chain of "
                        + LONG + " names as on one of " + SHORT);
        assertTrue(asked >= AT_LEAST_ASKED, asked + " readers asked");
    }
}
