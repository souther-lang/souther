package souther.compiler.query;

import java.lang.reflect.RecordComponent;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.TreeSet;

/**
 * Which of a module's indexes each question about one definition reads, and what each of those
 * edges is.
 *
 * <p>Read off the graph a compile built rather than off the source that would build it. What a
 * question depends on is what it asked for while it was answered, and a {@code compute} reached
 * through two helpers and a branch says that nowhere a reader of the file can see. {@link
 * Db#everyAnswer} and {@link Db#dependenciesOf} are the graph itself.
 *
 * <p><b>An edge is what its consumer means.</b> A collection gathered per module is an index; a
 * question about one definition depends on the entries it reaches and not on the index. Read whole,
 * the index hands the finer question the coarser one's identity, and an edit anywhere in the module
 * arrives as an edit to every definition in it.
 *
 * <p><b>Two ways out and no third.</b> {@link WhatItIs} is what makes an edge sound, and which of
 * the two an edge is cannot be read off the graph — it takes the graph, what equality says about
 * the answers, and an edit. An edge that is neither is not written down and has no word here, so
 * the check that reads this fails on it.
 *
 * <p><b>Both ways out can be had for nothing, so neither is taken on its own.</b> An answer holding
 * nothing is entries of every index there is, and an index that does not move under the edit leaves
 * every reader of it alone whatever the reader means. So a reading here says what the edit moved as
 * well as what it found: a verdict over an index that stayed put says nothing about the edge, and
 * is not one.
 */
final class IndexEdges {

    /**
     * One edge as a shape: the question about one definition, and the index it read.
     *
     * <p>The classes and not the keys. What is written down is a judgement about a question, and a
     * module with two behaviors in it holds the same edge twice; keyed by the key, the register
     * would be a register of a fixture.
     */
    record Edge(Class<?> reader, Class<?> index) implements Comparable<Edge> {

        @Override
        public String toString() {
            return named(reader) + " -> " + named(index);
        }

        @Override
        public int compareTo(Edge other) {
            return toString().compareTo(other.toString());
        }

        private static String named(Class<?> type) {
            Class<?> around = type.getEnclosingClass();
            return (around == null ? "" : around.getSimpleName() + ".") + type.getSimpleName();
        }
    }

    /** What makes an edge sound, asked only of an edit that moved the index. */
    enum WhatItIs {

        /**
         * The reader answers with entries of the index, so an entry beside them moves the index and
         * this comes out equal. The index is still built once, and what reads this stops here.
         *
         * <p>Entries and not the values at them. A reader holding what happens to equal some value
         * of the index is not holding part of the index: an arity of one is an arity of one
         * wherever it was read, and a fold that came out to a handful of those would read as a
         * projection of everything. So a map is asked whether its entries are the index's entries,
         * keys and all.
         *
         * <p>That it projects and not how much of the index it takes. A reader answering with every
         * entry is entries of it and reads as this, and it cuts nothing; what says a projection is
         * narrow is a question about that reader's own meaning, and it is asked where that reader
         * is.
         */
        A_PROJECTION,

        /**
         * The reader folds the index in and the index moved, and what the reader came to is what it
         * was — so what travels along this edge is stopped by an equality rather than by a cut.
         */
        AN_ANSWER_EQUAL_UNDER_A_SIBLING_EDIT
    }

    /** A store's graph as it stood: what each question answered, and what it read to answer it. */
    record Snapshot(Map<Key<?>, Answer<?>> answers, Map<Key<?>, Set<Key<?>>> reads) {

        static Snapshot of(Db db) {
            Map<Key<?>, Answer<?>> answers = db.everyAnswer();
            Map<Key<?>, Set<Key<?>>> reads = new LinkedHashMap<>();
            answers.keySet().forEach(key -> reads.put(key, db.dependenciesOf(key)));
            return new Snapshot(answers, reads);
        }
    }

    /**
     * What the graph holds, and what one edit made of it.
     *
     * @param whereTheIndexMoved the edges this edit actually exercised, and what each was found to
     *                           be. An edge whose index came out equal is not here: this edit put
     *                           no question to it
     * @param neither the exercised edges that are neither, one line each, in an order a reader can
     *                follow
     * @param exercised every edge this edit moved the index of, whatever came of it — so an edge
     *                  nothing here asks is told from one that was asked and answered badly
     * @param witnessed the shapes some instance of which was seen to project something: an answer
     *                  holding nothing is entries of every index there is, so a shape read as a
     *                  projection over nothing but those was never asked the question
     * @param everyEdge every edge shape in the graph, moved or not, which is what says an edge no
     *                  edit reaches is an edge nothing here has judged
     * @param instances how many edges were read, which says a census of nothing is a census of
     *                  nothing rather than a clean one
     */
    record Census(Map<Edge, Set<WhatItIs>> whereTheIndexMoved, List<String> neither,
                  Set<Edge> exercised, Set<Edge> witnessed, Set<Edge> everyEdge, int instances) {}

    /**
     * What the graph held before the edit, read against what it held after.
     *
     * <p>A projection is a projection whatever is edited, so it is asked first; what is left is
     * asked of the reader, which either came to what it came to before or was dragged by an index
     * that means more than it does.
     */
    static Census taken(Snapshot before, Snapshot after) {
        Map<Edge, Set<WhatItIs>> moved = new LinkedHashMap<>();
        Set<Edge> exercised = new TreeSet<>();
        List<String> neither = new ArrayList<>();
        Set<Edge> witnessed = new TreeSet<>();
        Set<Edge> everyEdge = new TreeSet<>();
        int instances = 0;
        for (Map.Entry<Key<?>, Answer<?>> each : before.answers().entrySet()) {
            Key<?> reader = each.getKey();
            if (!aboutOneDefinition(reader)) {
                continue;
            }
            for (Key<?> read : before.reads().get(reader)) {
                Answer<?> index = before.answers().get(read);
                if (!anIndex(read, index)) {
                    continue;
                }
                instances++;
                Edge edge = new Edge(reader.getClass(), read.getClass());
                everyEdge.add(edge);
                Projection projection = projects(each.getValue(), index);
                if (projection == Projection.OF_SOMETHING) {
                    witnessed.add(edge);
                }
                if (Objects.equals(index, after.answers().get(read))) {
                    // This edit put no question to this edge. Saying what the reader is over an
                    // index that stayed where it was is saying what any reader of it is.
                    continue;
                }
                exercised.add(edge);
                WhatItIs is = projection != Projection.OF_NOTHING_OF_THIS_INDEX
                        ? WhatItIs.A_PROJECTION
                        : Objects.equals(each.getValue(), after.answers().get(reader))
                                ? WhatItIs.AN_ANSWER_EQUAL_UNDER_A_SIBLING_EDIT : null;
                if (is == null) {
                    neither.add(edge + ", at " + reader + ", reading " + read);
                    continue;
                }
                moved.computeIfAbsent(edge, _ -> new TreeSet<>()).add(is);
            }
        }
        Collections.sort(neither);
        return new Census(moved, neither, exercised, witnessed, everyEdge, instances);
    }

    /** How much of the index a reader's answer was seen to be entries of. */
    private enum Projection {
        /** Entries of it, and there is something there to have been projected. */
        OF_SOMETHING,
        /** Entries of it the way an empty hand is entries of every index there is. */
        OF_NOTHING_AT_ALL,
        /** Something else: the reader folds the index into an answer of its own. */
        OF_NOTHING_OF_THIS_INDEX
    }

    /**
     * Whether what the reader answers with is entries of the index's answer.
     *
     * <p>Asked of what is there rather than of the types, because that is what an author of a
     * {@code compute} can get wrong: a key that once looked an entry up and now folds the index into
     * something of its own has the same signature it had.
     *
     * <p>Two shapes and no others. A reader answering with a table of its own is its entries against
     * the index's, keys included; a reader answering with one thing is that thing against the
     * index's entries, and which entry it took is not something this can see — what it says is that
     * recomputing the reader is a lookup, which is what the edge costs. A reader answering with a
     * table against an index that is not one is not projecting anything.
     */
    private static Projection projects(Answer<?> reader, Answer<?> index) {
        if (reader == null || !reader.present()) {
            return Projection.OF_NOTHING_AT_ALL;
        }
        if (index == null || !index.present()) {
            return Projection.OF_NOTHING_OF_THIS_INDEX;
        }
        Object held = reader.value();
        Object all = index.value();
        if (held instanceof Map<?, ?> mine) {
            if (mine.isEmpty()) {
                return Projection.OF_NOTHING_AT_ALL;
            }
            return all instanceof Map<?, ?> table
                    && table.entrySet().containsAll(mine.entrySet())
                    ? Projection.OF_SOMETHING : Projection.OF_NOTHING_OF_THIS_INDEX;
        }
        if (held instanceof Collection<?> mine) {
            if (mine.isEmpty()) {
                return Projection.OF_NOTHING_AT_ALL;
            }
            return all instanceof Collection<?> table && table.containsAll(mine)
                    ? Projection.OF_SOMETHING : Projection.OF_NOTHING_OF_THIS_INDEX;
        }
        return entriesOf(all).contains(held)
                ? Projection.OF_SOMETHING : Projection.OF_NOTHING_OF_THIS_INDEX;
    }

    /** What a table holds, or null where what was handed over is not one. */
    private static Collection<?> entriesOf(Object held) {
        return switch (held) {
            case Map<?, ?> map -> map.values();
            case Collection<?> all -> all;
            case null, default -> null;
        };
    }

    /**
     * Whether {@code key} is a collection its module gathered: it names its module and nothing
     * narrower, and it answers with a table.
     *
     * <p>Not counted. A key about a module may hold more than the module — {@link Bodies.Expanding}
     * takes a policy — and reading how many things it holds would leave every index that takes one
     * out of the census.
     */
    private static boolean anIndex(Key<?> key, Answer<?> answer) {
        if (answer == null || !answer.present() || aboutOneDefinition(key)) {
            return false;
        }
        return key.getClass().getRecordComponents() != null && entriesOf(answer.value()) != null;
    }

    /** Whether {@code key} means something about one definition rather than about its module. */
    private static boolean aboutOneDefinition(Key<?> key) {
        RecordComponent[] parts = key.getClass().getRecordComponents();
        if (parts == null) {
            return false;
        }
        for (RecordComponent part : parts) {
            if (narrows(key, part)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Whether what a key holds at one of its components names something inside the module it is
     * about.
     *
     * <p>Read off the component rather than off how many there are. A key naming one declaration
     * holds one thing ({@link Shapes.FieldBindingsOf}) and a key about a module holds more than one
     * where the rest say how to read it ({@link Bodies.Expanding} takes a policy), so a count
     * misreads both ways.
     *
     * <p><b>Narrower unless somebody said otherwise, and the default is the safe half.</b> A
     * component read as naming something puts its key among the readers, so its reads of an index
     * are counted and have to be judged; read as saying which module, they leave the census without
     * a word. So an unjudged component makes this ask more, never less, and the register below is
     * only the components somebody had to excuse.
     *
     * <p>A name written as text is the one case decided by what is there rather than by a judgement:
     * the key says which module it is about, and a component holding that name is that module while
     * one holding another name is something in it.
     */
    private static boolean narrows(Key<?> key, RecordComponent part) {
        if (part.getType() == String.class) {
            return !(held(key, part) instanceof String named) || !named.equals(key.module());
        }
        return !saysWhichModuleOrHowToReadIt().contains(new Part(key.getClass(), part.getName()));
    }

    /** One component of one question. */
    record Part(Class<?> key, String component) implements Comparable<Part> {

        @Override
        public String toString() {
            Class<?> around = key.getEnclosingClass();
            return (around == null ? "" : around.getSimpleName() + ".") + key.getSimpleName()
                    + "#" + component;
        }

        @Override
        public int compareTo(Part other) {
            return toString().compareTo(other.toString());
        }
    }

    /**
     * The components that say which module a question is about, or how what it asks for is to be
     * read, rather than naming something the module holds.
     *
     * <p>Per component and not per type, because the role is the component's. That a question holds
     * a source says which file its module was written in at one key and which of a module's
     * attached files was read at another; that it holds a number says which control of a module at
     * one and could say how deep to look at the next. The type is what is held, and this is what it
     * is held for.
     */
    static Set<Part> saysWhichModuleOrHowToReadIt() {
        Set<Part> out = new LinkedHashSet<>();
        out.add(new Part(Bodies.Expanding.class, "policy"));
        out.add(new Part(Bodies.RecursiveCallSigs.class, "policy"));
        out.add(new Part(Output.Evaluated.class, "arms"));
        out.add(new Part(Output.EvaluationLinked.class, "arms"));
        out.add(new Part(Output.Examples.class, "arms"));
        out.add(new Part(Output.Examples.class, "sourceId"));
        out.add(new Part(Adequacy.Obligations.class, "scope"));
        return out;
    }

    /** Whether every component this register excuses is one a question still holds. */
    static Set<Part> staleIn(List<Class<?>> questions) {
        Set<Part> held = new LinkedHashSet<>();
        for (Class<?> question : questions) {
            RecordComponent[] parts = question.getRecordComponents();
            if (parts == null) {
                continue;
            }
            for (RecordComponent part : parts) {
                held.add(new Part(question, part.getName()));
            }
        }
        Set<Part> stale = new TreeSet<>(saysWhichModuleOrHowToReadIt());
        stale.removeAll(held);
        return stale;
    }

    private static Object held(Object record, RecordComponent part) {
        try {
            part.getAccessor().setAccessible(true);
            return part.getAccessor().invoke(record);
        } catch (ReflectiveOperationException cannotRead) {
            throw new IllegalStateException("a key would not say what it holds at "
                    + part.getName(), cannotRead);
        }
    }

    private IndexEdges() {
    }
}
