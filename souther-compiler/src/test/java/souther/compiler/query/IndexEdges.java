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
 * <p><b>What is asked is not what shape an edge has.</b> It is whether an edit wider than what the
 * reader means moves what the reader answers: the index moved, and the reader came to what it came
 * to before. That is one question and it is the whole of it, and it cannot be read off the graph —
 * it takes the graph, what equality says about the answers, and an edit.
 *
 * <p>{@link WhyItHeld} is read afterwards and says why the answer held. Asked first, it lets through
 * exactly what this is for: a reader answering with every entry of an index is entries of it,
 * reads as a projection, and moves with the index whenever it moves.
 *
 * <p><b>And an index that stayed put asks nothing.</b> It leaves every reader of it alone whatever
 * the reader means, so a verdict taken under such an edit is a verdict about the edit. A reading
 * here says which edit moved the index as well as what came of it.
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

    /**
     * Why an edge that was sound was sound.
     *
     * <p>Not what makes it sound. What makes it sound is one thing and it is the same for both: the
     * index moved and the reader came to what it came to before. These are read after that, and
     * they say which of the two ways it happened — a classification of a fact rather than the fact.
     *
     * <p>Held apart from it because the two came apart once already. Read as the test, a reader
     * answering with every entry of the index is entries of it, reads as a projection, and cuts
     * nothing: the index moves, the answer moves with it, and every reader downstream is asked
     * again while this says the edge is fine.
     */
    enum WhyItHeld {

        /** The reader answers with entries of the index, so what it comes to is what those entries
         *  are. */
        A_PROJECTION,

        /** The reader folds the index in and came to what it came to before, so what travels along
         *  this edge is stopped by an equality rather than by a cut. */
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
     * @param everyEdge every edge shape in the graph, moved or not, which is what says an edge no
     *                  edit reaches is an edge nothing here has judged
     * @param unread every component of every question this walk met that nobody has read, which is
     *               what the census rests on and cannot be defaulted either way
     * @param instances how many edges were read, which says a census of nothing is a census of
     *                  nothing rather than a clean one
     */
    record Census(Map<Edge, Set<WhyItHeld>> whereTheIndexMoved, List<String> neither,
                  Set<Edge> exercised, Set<Edge> everyEdge, Set<Part> unread,
                  int instances) {}

    /**
     * What the graph held before the edit, read against what it held after.
     *
     * <p>One question per edge and it is asked of the reader: an index that moved, and an answer
     * that did or did not move with it. What shape the reader's answer has is read after that and
     * only to say why it held.
     */
    static Census taken(Snapshot before, Snapshot after) {
        Map<Edge, Set<WhyItHeld>> moved = new LinkedHashMap<>();
        Set<Edge> exercised = new TreeSet<>();
        List<String> neither = new ArrayList<>();
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
                if (Objects.equals(index, after.answers().get(read))) {
                    // This edit put no question to this edge. Saying what the reader is over an
                    // index that stayed where it was is saying what any reader of it is.
                    continue;
                }
                exercised.add(edge);
                // The one thing that is asked. The index moved, so what the reader means is
                // whether it moved with it — and what stops an edit is what an answer's equality
                // says, whatever shape the answer has.
                if (!Objects.equals(each.getValue(), after.answers().get(reader))) {
                    neither.add(edge + ", at " + reader + ", reading " + read);
                    continue;
                }
                moved.computeIfAbsent(edge, _ -> new TreeSet<>())
                        .add(projectsSomething(each.getValue(), index)
                                ? WhyItHeld.A_PROJECTION
                                : WhyItHeld.AN_ANSWER_EQUAL_UNDER_A_SIBLING_EDIT);
            }
        }
        Collections.sort(neither);
        return new Census(moved, neither, exercised, everyEdge, unread, instances);
    }

    /**
     * Whether what the reader answers with is entries of the index's answer, and some.
     *
     * <p>Asked of what is there rather than of the types, because that is what an author of a
     * {@code compute} can get wrong: a key that once looked an entry up and now folds the index into
     * something of its own has the same signature it had.
     *
     * <p>Two shapes and no others. A reader answering with a table of its own is its entries against
     * the index's, keys included; a reader answering with one thing is that thing against the
     * index's entries, and which entry it took is not something this can see. An answer holding
     * nothing is not one of them: it is entries of every index there is, so reading it as a
     * projection would be reading nothing at all.
     *
     * <p>A reader answering with a collection off a collection is not asked. What containment says
     * about two of those depends on which collection they are — it drops multiplicity over a list
     * and order over a sequence — and nothing in this graph is that shape, so a word for it written
     * now would be a word for whichever of them somebody meant.
     */
    private static boolean projectsSomething(Answer<?> reader, Answer<?> index) {
        if (reader == null || !reader.present() || index == null || !index.present()) {
            return false;
        }
        Object held = reader.value();
        Object all = index.value();
        if (held instanceof Map<?, ?> mine) {
            return !mine.isEmpty() && all instanceof Map<?, ?> table
                    && table.entrySet().containsAll(mine.entrySet());
        }
        return !(held instanceof Collection<?>) && entriesOf(all).contains(held);
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
     * <p><b>What somebody said comes first.</b> A role is the component's, so a reading taken off
     * what happens to be there cannot overrule one. The two come apart where a module and a
     * definition of it are spelled alike — {@code module orders} with a {@code behavior orders} in
     * it — and there the text says module while the component says behavior. Taken the other way
     * round, that question stops being about one definition, its reads of an index leave the census,
     * and nothing says so.
     *
     * <p>What is left to the text is the component nobody wrote down, and one thing only: holding
     * the name the key says it is about is being that module. Any other text is not thereby a name
     * — it could as well say how to read what is asked for — so it is {@link
     * WhatAComponentHolds#UNREAD}, which is the word that keeps a module index taking a mode written
     * as text from dropping out of the census.
     */
    private static WhatAComponentHolds roleOf(Key<?> key, RecordComponent part) {
        WhatAComponentHolds said = whatEachComponentHolds().get(
                new Part(key.getClass(), part.getName()));
        if (said != null) {
            return said;
        }
        return part.getType() == String.class && held(key, part) instanceof String named
                && named.equals(key.module())
                ? WhatAComponentHolds.THE_MODULE : WhatAComponentHolds.UNREAD;
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

    /** What {@code key} holds at the component named {@code component}, for a check of the reading
     *  itself. */
    static WhatAComponentHolds roleAt(Key<?> key, String component) {
        for (RecordComponent part : key.getClass().getRecordComponents()) {
            if (part.getName().equals(component)) {
                return roleOf(key, part);
            }
        }
        throw new IllegalArgumentException(key.getClass() + " holds nothing at " + component);
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
        holds(out, Bodies.StandingRecursionsOfBody.class, "policy",
                WhatAComponentHolds.HOW_TO_READ_IT);
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
        names(out, Adequacy.InputsOf.class, "behavior");
        names(out, Bodies.BehaviorAritiesForBody.class, "fn");
        names(out, Bodies.BehaviorsReached.class, "behavior");
        names(out, Bodies.BodyForInvariantDischarge.class, "fn");
        names(out, Bodies.CalleeSigsForBody.class, "behavior");
        names(out, Bodies.CheckedBehavior.class, "behavior");
        names(out, Bodies.ContractsForBody.class, "behavior");
        names(out, Bodies.DeclaredSignature.class, "behavior");
        names(out, Bodies.RecursiveCallSigsForBody.class, "behavior");
        names(out, Bodies.RecursiveHelperConstructsForBody.class, "behavior");
        names(out, Bodies.SettledFn.class, "fn");
        names(out, Bodies.Spec.class, "behavior");
        names(out, Bodies.StandingRecursionsOfBody.class, "fn");
        names(out, Bodies.Stated.class, "behavior");
        names(out, Bodies.WrittenIntoBody.class, "fn");
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
     * Every line of the register naming a component no question holds any more.
     *
     * <p>A line that says nothing, beside lines that decide the census, is a line somebody will read
     * as deciding something.
     */
    static Set<Part> staleIn(List<Class<?>> questions) {
        Set<Part> read = new LinkedHashSet<>();
        for (Class<?> question : questions) {
            RecordComponent[] parts = question.getRecordComponents();
            if (parts == null) {
                continue;
            }
            for (RecordComponent part : parts) {
                read.add(new Part(question, part.getName()));
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
