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
     * @param unread every component of every question this walk met that nobody has read, which is
     *               what the census rests on and cannot be defaulted either way
     * @param instances how many edges were read, which says a census of nothing is a census of
     *                  nothing rather than a clean one
     */
    record Census(Map<Edge, Set<WhatItIs>> whereTheIndexMoved, List<String> neither,
                  Set<Edge> exercised, Set<Edge> witnessed, Set<Edge> everyEdge, Set<Part> unread,
                  int instances) {}

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
        Set<Part> unread = new TreeSet<>();
        for (Map.Entry<Key<?>, Answer<?>> each : before.answers().entrySet()) {
            Key<?> reader = each.getKey();
            unread(reader, unread);
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
        return new Census(moved, neither, exercised, witnessed, everyEdge, unread, instances);
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
        if (held instanceof Collection<?>) {
            // Not a projection, whatever it holds. What containment says about two collections
            // depends on which collection they are: it drops multiplicity over a list and order
            // over a sequence, so a reader answering [x, x] is entries of an index holding [x].
            // Nothing in this graph answers a collection off an index, and a word for it written
            // before there is one would be a word for whichever of those somebody meant.
            return Projection.OF_NOTHING_OF_THIS_INDEX;
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
     * What a key holds at a component, which decides what the key is about.
     *
     * <p><b>There is no safe default, so there is no default.</b> The two questions this settles
     * want opposite things of a component nobody has read. A reader holding an unread component is
     * safer read as naming something, because that puts its reads of an index into the census; an
     * index holding one is safer read as saying which module, because reading it as naming
     * something takes the index itself out of the census and every edge into it with it. One
     * word cannot be both, and a word that leaned either way would be quietly wrong about the
     * other.
     *
     * <p>So {@link #UNREAD} is a third thing and it is nobody's default: a census that meets one
     * says so, and the check fails until somebody writes down which of the two it is.
     */
    enum WhatAComponentHolds {

        /** The module the question is about. */
        THE_MODULE,

        /** A name of something the module holds — a declaration, a definition, a clause, a place in
         *  a file — so a question holding it means less than its module does. */
        SOMETHING_THE_MODULE_HOLDS,

        /** How what is asked for is to be read: which of a module's files, under which policy. A
         *  question holding nothing else is a question about the module. */
        HOW_TO_READ_IT,

        /** Nobody has said. Not a reading of the component and not a way of treating one. */
        UNREAD
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
            if (roleOf(key, part) == WhatAComponentHolds.SOMETHING_THE_MODULE_HOLDS) {
                return true;
            }
        }
        return false;
    }

    /**
     * What {@code key} holds at {@code part}.
     *
     * <p>Read off the component rather than off how many there are. A key naming one declaration
     * holds one thing ({@link Shapes.FieldBindingsOf}) and a key about a module holds more than one
     * where the rest say how to read it ({@link Bodies.Expanding} takes a policy), so a count
     * misreads both ways.
     *
     * <p>A name written as text is the one case decided by what is there rather than by a
     * judgement: the key says which module it is about, and a component holding that name is that
     * module while one holding another name is something in it. Everything else is
     * {@link #whatEachComponentHolds}'s to say, and {@link WhatAComponentHolds#UNREAD} where it has
     * not.
     */
    private static WhatAComponentHolds roleOf(Key<?> key, RecordComponent part) {
        if (part.getType() == String.class) {
            return held(key, part) instanceof String named && named.equals(key.module())
                    ? WhatAComponentHolds.THE_MODULE
                    : WhatAComponentHolds.SOMETHING_THE_MODULE_HOLDS;
        }
        return whatEachComponentHolds().getOrDefault(new Part(key.getClass(), part.getName()),
                WhatAComponentHolds.UNREAD);
    }

    /** Every component of a key this census met that nobody has read. */
    private static void unread(Key<?> key, Set<Part> out) {
        RecordComponent[] parts = key.getClass().getRecordComponents();
        if (parts == null) {
            return;
        }
        for (RecordComponent part : parts) {
            if (roleOf(key, part) == WhatAComponentHolds.UNREAD) {
                out.add(new Part(key.getClass(), part.getName()));
            }
        }
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
     * What each component a census meets is held for, where the type alone does not say.
     *
     * <p>Per component and not per type, because the role is the component's. That a question holds
     * a source says which file its module was written in at one key and which of a module's
     * attached files was read at another; that it holds a number says which control of a module at
     * one and could say how deep to look at the next. The type is what is held, and this is what it
     * is held for.
     */
    static Map<Part, WhatAComponentHolds> whatEachComponentHolds() {
        Map<Part, WhatAComponentHolds> out = new LinkedHashMap<>();
        holds(out, Bodies.Expanding.class, "policy", WhatAComponentHolds.HOW_TO_READ_IT);
        holds(out, Bodies.RecursiveCallSigs.class, "policy", WhatAComponentHolds.HOW_TO_READ_IT);
        holds(out, Bodies.WrittenIntoBody.class, "policy", WhatAComponentHolds.HOW_TO_READ_IT);
        holds(out, Bodies.ReachedByBody.class, "policy", WhatAComponentHolds.HOW_TO_READ_IT);
        holds(out, Bodies.BehaviorAritiesForBody.class, "policy",
                WhatAComponentHolds.HOW_TO_READ_IT);
        holds(out, Output.Evaluated.class, "arms", WhatAComponentHolds.HOW_TO_READ_IT);
        holds(out, Output.EvaluationLinked.class, "arms", WhatAComponentHolds.HOW_TO_READ_IT);
        holds(out, Output.Examples.class, "arms", WhatAComponentHolds.HOW_TO_READ_IT);
        holds(out, Output.Examples.class, "sourceId", WhatAComponentHolds.HOW_TO_READ_IT);
        holds(out, Adequacy.Obligations.class, "scope", WhatAComponentHolds.HOW_TO_READ_IT);
        holds(out, Front.AttachedTo.class, "id", WhatAComponentHolds.HOW_TO_READ_IT);
        holds(out, Front.Declares.class, "id", WhatAComponentHolds.HOW_TO_READ_IT);
        holds(out, Front.LayoutOf.class, "id", WhatAComponentHolds.HOW_TO_READ_IT);
        holds(out, Front.ModuleOf.class, "id", WhatAComponentHolds.HOW_TO_READ_IT);
        holds(out, Front.Parsed.class, "id", WhatAComponentHolds.HOW_TO_READ_IT);
        holds(out, Front.RowNames.class, "id", WhatAComponentHolds.HOW_TO_READ_IT);
        holds(out, Front.Text.class, "id", WhatAComponentHolds.HOW_TO_READ_IT);
        holds(out, Names.StandInBlocks.class, "id", WhatAComponentHolds.HOW_TO_READ_IT);
        names(out, Bodies.LoweredBody.class, "fn");
        names(out, Bodies.Assumptions.class, "behavior");
        names(out, Machines.OfDeclaration.class, "named");
        names(out, Names.CompilationDeclares.class, "named");
        names(out, Names.Declaration.class, "named");
        names(out, Names.DeclarationIsNewtype.class, "named");
        names(out, Names.DeclarationKindOf.class, "named");
        names(out, Names.Definition.class, "named");
        names(out, Names.ResolvedDeclaration.class, "named");
        names(out, Shapes.CardinalityPremiseOf.class, "named");
        names(out, Shapes.ClausesExpandedFor.class, "named");
        names(out, Shapes.DerivedDef.class, "named");
        names(out, Shapes.EffectiveFieldTypesOf.class, "named");
        names(out, Shapes.FieldBindingsOf.class, "named");
        names(out, Shapes.MeaningOf.class, "named");
        names(out, Shapes.NewtypeInnerOf.class, "named");
        names(out, Shapes.NormalizedDef.class, "named");
        return out;
    }

    private static void names(Map<Part, WhatAComponentHolds> out, Class<?> key, String component) {
        holds(out, key, component, WhatAComponentHolds.SOMETHING_THE_MODULE_HOLDS);
    }

    private static void holds(Map<Part, WhatAComponentHolds> out, Class<?> key, String component,
                              WhatAComponentHolds what) {
        out.put(new Part(key, component), what);
    }

    /**
     * Every line of the register that nothing reads: one naming a component no question holds any
     * more, and one naming a component whose role is read off what it holds.
     *
     * <p>Both are lines that say nothing, and a line that says nothing beside lines that decide the
     * census is a line somebody will read as deciding something. A name written as text is settled
     * against the module the key names, so writing a word beside one here would be writing a word
     * that is never asked for.
     */
    static Set<Part> staleIn(List<Class<?>> questions) {
        Set<Part> read = new LinkedHashSet<>();
        for (Class<?> question : questions) {
            RecordComponent[] parts = question.getRecordComponents();
            if (parts == null) {
                continue;
            }
            for (RecordComponent part : parts) {
                if (part.getType() != String.class) {
                    read.add(new Part(question, part.getName()));
                }
            }
        }
        Set<Part> stale = new TreeSet<>(whatEachComponentHolds().keySet());
        stale.removeAll(read);
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
