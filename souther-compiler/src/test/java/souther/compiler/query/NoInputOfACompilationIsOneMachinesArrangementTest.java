package souther.compiler.query;

import souther.compiler.WhatWasCompiled;

import org.junit.jupiter.api.Test;

import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

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
 * further down is the same finding as one carrying it outright. The inputs themselves come from what
 * was compiled rather than from a file saying {@code implements Input<}, so where one is declared and
 * how the declaration is spelled are not part of the rule.
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

    /**
     * And the walk finds the inputs there are.
     *
     * <p>Pinned as what has to be among them rather than as all of them: an input added later is
     * held by the rule above, and a list here would be a second place to say how many there are. A
     * walk that had gone blind would find nothing and pass, which is what this refuses.
     */
    @Test
    void andTheWalkFindsTheInputsThereAre() {
        List<String> found = inputs().stream().map(Class::getName).toList();

        assertTrue(found.containsAll(List.of(
                        "souther.compiler.query.Front$Text",
                        "souther.compiler.query.Front$Policy",
                        "souther.compiler.query.Adequacy$Requested")),
                () -> "the inputs there are should be among what was walked: " + found);
    }

    /** Every input this module compiled. */
    private static List<Class<?>> inputs() {
        List<Class<?>> found = new ArrayList<>();
        for (String each : WhatWasCompiled.answering(Input.class)) {
            Class<?> key = loaded(each);
            if (Input.class.isAssignableFrom(key)) {
                found.add(key);
            }
        }
        return found;
    }

    private static Class<?> loaded(String name) {
        try {
            return Class.forName(name);
        } catch (ClassNotFoundException e) {
            throw new IllegalStateException(name + " was compiled and cannot be loaded", e);
        }
    }

    /**
     * What {@code at} says an input answers with, looked for through whatever is between it and
     * {@link Input}.
     *
     * <p>A key may reach the interface through one of its own, and a walk reading only what the key
     * itself declares would find nothing there and report nothing about it — a rule that passes by
     * looking away. So this walks up, and where it arrives at an {@code Input} whose argument is a
     * variable rather than a type, it says so: that shape is one this cannot read, and a walk that
     * cannot read a key has not checked it.
     */
    private static Type whatItAnswers(Class<?> at, Class<?> key) {
        for (Type each : at.getGenericInterfaces()) {
            if (each instanceof ParameterizedType asked && asked.getRawType() == Input.class) {
                Type carried = asked.getActualTypeArguments()[0];
                assertTrue(carried instanceof Class<?> || carried instanceof ParameterizedType,
                        () -> key.getName() + " answers with " + carried + ", which this walk cannot"
                                + " read; a key whose answer is a variable needs the walk to resolve"
                                + " it before this rule holds for it");
                return carried;
            }
            if (each instanceof ParameterizedType asked
                    && asked.getRawType() instanceof Class<?> between
                    && Input.class.isAssignableFrom(between)) {
                return whatItAnswers(between, key);
            }
            if (each instanceof Class<?> between && Input.class.isAssignableFrom(between)) {
                return whatItAnswers(between, key);
            }
        }
        throw new IllegalStateException(key.getName() + " is an input and this walk did not find"
                + " what it answers with");
    }

    /** Everything the answer to {@code key} carries, as far as its own types go. */
    private static Set<Class<?>> whatItAnswersWith(Class<?> key) {
        Set<Class<?>> reached = new LinkedHashSet<>();
        Deque<Type> left = new ArrayDeque<>();
        left.add(whatItAnswers(key, key));
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
