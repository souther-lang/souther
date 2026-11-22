package souther.compiler.query;

import souther.compiler.ast.Hir;
import souther.compiler.check.CheckSurface;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.RecordComponent;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * Which behavior a compilation is working on, for someone waiting on it to be told.
 *
 * <p>Two answers, since answering a question about one behavior asks questions about others. What
 * the work is <em>for</em> is the behavior of the outermost question in flight that is about one,
 * and what is being <em>read</em> is the behavior of the innermost. Where they are one behavior the
 * time is going to that behavior's own account; where they differ, it is going to another
 * behavior the first has to be told about, which is what an author looking for what is costly
 * needs told apart. Where no question in flight is about a behavior, both are the module of the
 * outermost one about a module, and there is nothing where none is.
 *
 * <p>A question is about one behavior where it carries one: a key is a record of what identifies
 * its question ({@link Key}), and the component named {@code behavior} that is a name is that
 * behavior's. So every question about a behavior is counted, with nothing to write on each.
 *
 * <p>Listens on the thread that holds the store, and is read from any ({@link #now}).
 */
public final class WhatIsBeingMeasured implements Answering {

    /** A module, and its behavior where the work is about one. */
    public record Subject(String module, Optional<String> behavior) {}

    /**
     * What is worked on.
     *
     * @param asked   what the work is for
     * @param reading what is read for it as this is asked, which is {@code asked} where it is
     *                its own account that is read
     */
    public record Work(Subject asked, Subject reading) {}

    private static final ClassValue<Optional<RecordComponent>> BEHAVIOR_OF = new ClassValue<>() {
        @Override
        protected Optional<RecordComponent> computeValue(Class<?> type) {
            if (!type.isRecord()) {
                return Optional.empty();
            }
            for (RecordComponent part : type.getRecordComponents()) {
                if (part.getName().equals("behavior") && part.getType() == String.class) {
                    part.getAccessor().setAccessible(true);
                    return Optional.of(part);
                }
            }
            return Optional.empty();
        }
    };

    /** What is worked on inside each question in flight, innermost first; empty where it is
     *  nothing. */
    private final Deque<Optional<Work>> inFlight = new ArrayDeque<>();
    private volatile Optional<Work> now = Optional.empty();

    /**
     * The behaviors {@code compilation} measures ({@link Adequacy.Choice}), by module and in the
     * order they are declared; a module it measures none of is left out.
     */
    public static Map<String, List<String>> toBeMeasuredIn(Compilation compilation) {
        Map<String, List<String>> out = new LinkedHashMap<>();
        for (String module : compilation.modules()) {
            CheckSurface surface =
                    compilation.db().ask(new Shapes.CheckSurface(module)).value();
            if (surface == null) {
                continue;
            }
            List<String> measured = surface.behaviors().stream().map(Hir.BehaviorDef::name)
                    .filter(behavior -> Adequacy.chosen(compilation.db(), module, behavior))
                    .toList();
            if (!measured.isEmpty()) {
                out.put(module, measured);
            }
        }
        return out;
    }

    /** What the compilation is working on as this is asked. */
    public Optional<Work> now() {
        return now;
    }

    @Override
    public void started(Key<?> key) {
        Optional<Work> around = inFlight.isEmpty() ? Optional.empty() : inFlight.peek();
        Optional<Subject> about = about(key);
        Optional<Work> within = about.isEmpty() ? around
                : Optional.of(inside(around, about.get()));
        inFlight.push(within);
        now = within;
    }

    @Override
    public void finished(Key<?> key) {
        inFlight.pop();
        now = inFlight.isEmpty() ? Optional.empty() : inFlight.peek();
    }

    /**
     * What is worked on in a question about {@code subject} asked while {@code around} was: for
     * the behavior the work around it is for, where that is one, and reading the behavior of this
     * question, where it carries one.
     */
    private static Work inside(Optional<Work> around, Subject subject) {
        if (around.isEmpty()) {
            return new Work(subject, subject);
        }
        Work outer = around.get();
        if (outer.asked().behavior().isEmpty()) {
            return new Work(subject, subject);
        }
        return subject.behavior().isEmpty() ? outer : new Work(outer.asked(), subject);
    }

    /** What {@code key} is about, where it is about a module. */
    private static Optional<Subject> about(Key<?> key) {
        String module = key.module();
        if (module == null) {
            return Optional.empty();
        }
        return Optional.of(new Subject(module, BEHAVIOR_OF.get(key.getClass())
                .map(part -> behaviorOf(key, part))));
    }

    private static String behaviorOf(Key<?> key, RecordComponent part) {
        try {
            return (String) part.getAccessor().invoke(key);
        } catch (IllegalAccessException | InvocationTargetException e) {
            throw new IllegalStateException(key + " does not say which behavior it carries", e);
        }
    }
}
