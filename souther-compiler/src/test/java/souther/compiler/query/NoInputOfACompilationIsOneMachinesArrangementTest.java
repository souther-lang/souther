package souther.compiler.query;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a compilation is told, and never how one machine carries it out.
 *
 * <p>An {@link Input} is the one thing a caller of this compiler sets: the sources, the path they
 * resolve against, the terms a run is held to. Every caller has those, whatever runs its programs. A
 * thread, a stack, a wall clock are how one implementation keeps a term, they mean nothing to an
 * execution that is not that one, and an input carrying one puts it on the surface a build, an
 * editor and a Java binding all hold.
 *
 * <p>It is not a rule about tidiness. The arrangement was an input once, and while it was, the value
 * it carried answered for the wait as well — so the boundary stated a minute while the run was being
 * given up on after a hundred milliseconds, and a rendered line quoted a number no compilation had
 * been told. What that costs is why this is checked and not written down.
 *
 * <p>Read from what each input answers with, not from what its key is called, and read as far as the
 * answer goes: a record's components and a sum's cases, so an input carrying the machine one type
 * further down is the same finding as one carrying it outright.
 *
 * <p>What a type cannot say, this does not say either. {@code WorkerStack} was an
 * {@code Input<Long>} — a number of bytes of a thread's stack, which is the machine's through and
 * through and which no walk over {@code Long} will ever reach. That half is
 * {@code TheArrangementThatKeepsATermDoesNotAskTheCompilationForItTest}, which asks it from the
 * other end: whatever the key is called and whatever it answers with, the arrangement is not allowed
 * to come here to read it.
 */
class NoInputOfACompilationIsOneMachinesArrangementTest {

    /** The packages and types that are one machine's way of running a row rather than a term any
     *  execution can be held to. */
    private static final List<String> THE_MACHINES = List.of(
            "souther.compiler.execute.jvm.",
            "souther.compiler.examples.Deadline");

    /** Where the inputs of a compilation are declared. Checked against the source below, so this
     *  file cannot go on holding a set that has moved on without it. */
    private static final List<Class<?>> DECLARING = List.of(Front.class, Adequacy.class);

    private static final Path MAIN = Path.of("src/main/java");

    /**
     * Nothing an input answers with reaches the machine.
     */
    @Test
    void whatAnInputAnswersWithIsNotOneMachinesArrangement() {
        List<String> naming = new ArrayList<>();
        for (Class<?> key : inputs()) {
            for (Class<?> reached : whatItAnswersWith(key)) {
                for (String machine : THE_MACHINES) {
                    if (reached.getName().startsWith(machine)) {
                        naming.add(key.getSimpleName() + " reaches " + reached.getName());
                    }
                }
            }
        }

        assertEquals(List.of(), naming,
                "an input is what this compilation was told; how one machine keeps a term is"
                        + " offered where that implementation is named, which is"
                        + " Compilation.withJvmExampleDeadlines");
    }

    /** And the inputs this reads are all of them. */
    @Test
    void andEveryInputThereIsWasWalked() throws IOException {
        Set<String> declaringInSource = new LinkedHashSet<>();
        try (Stream<Path> written = Files.walk(MAIN)) {
            for (Path each : written.filter(p -> p.toString().endsWith(".java")).toList()) {
                if (Files.readString(each).contains("implements Input<")) {
                    String file = each.getFileName().toString();
                    declaringInSource.add(file.substring(0, file.length() - ".java".length()));
                }
            }
        }

        assertEquals(DECLARING.stream().map(Class::getSimpleName).collect(
                        java.util.stream.Collectors.toCollection(LinkedHashSet::new)),
                declaringInSource,
                "every file declaring an input is one this walks; a new one has to be added here"
                        + " with a reason, not left out of the walk");
        assertTrue(inputs().size() >= 10, "and the walk found them: " + inputs());
    }

    /** Every input key declared in {@link #DECLARING}. */
    private static List<Class<?>> inputs() {
        List<Class<?>> found = new ArrayList<>();
        for (Class<?> where : DECLARING) {
            for (Class<?> nested : where.getDeclaredClasses()) {
                if (Input.class.isAssignableFrom(nested)) {
                    found.add(nested);
                }
            }
        }
        return found;
    }

    /** Everything the answer to {@code key} carries, as far as its own types go. */
    private static Set<Class<?>> whatItAnswersWith(Class<?> key) {
        Set<Class<?>> reached = new LinkedHashSet<>();
        Deque<Type> left = new ArrayDeque<>();
        for (Type each : key.getGenericInterfaces()) {
            if (each instanceof ParameterizedType asked
                    && asked.getRawType() == Input.class) {
                left.add(asked.getActualTypeArguments()[0]);
            }
        }
        while (!left.isEmpty()) {
            switch (left.poll()) {
                case ParameterizedType asked -> {
                    left.add(asked.getRawType());
                    left.addAll(List.of(asked.getActualTypeArguments()));
                }
                case Class<?> found -> {
                    if (!reached.add(found) || found.getName().startsWith("java.")) {
                        continue;
                    }
                    if (found.isRecord()) {
                        for (var component : found.getRecordComponents()) {
                            left.add(component.getGenericType());
                        }
                    }
                    if (found.isSealed()) {
                        left.addAll(List.of(found.getPermittedSubclasses()));
                    }
                    for (var field : found.getDeclaredFields()) {
                        left.add(field.getGenericType());
                    }
                }
                default -> { }
            }
        }
        return reached;
    }
}
