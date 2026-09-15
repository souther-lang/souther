package souther.compiler.query;

import souther.compiler.ast.DefinitionName;
import souther.compiler.check.Clause;
import souther.compiler.check.InliningPolicy;
import souther.compiler.check.RuleRef;
import souther.compiler.diag.SourcePos;
import souther.compiler.observe.ArmObservation;
import souther.compiler.sites.WrittenCondition;
import souther.compiler.source.SourceId;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

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

    /** What makes an edge sound. */
    enum WhatItIs {

        /**
         * The reader answers with entries of the index, so an entry beside them moves the index and
         * this comes out equal. The index is still built once, and what reads this stops here.
         *
         * <p>That it projects and not how much of the index it takes. A reader answering with every
         * entry is entries of it and reads as this, and it cuts nothing; what says a projection is
         * narrow is a question about that reader's own meaning, and it is asked where that reader
         * is.
         */
        A_PROJECTION,

        /**
         * The reader folds the index in, and the index is what it was after a definition the reader
         * says nothing about was edited — so nothing travels along this edge at all.
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
     * What the graph holds, and what each edge in it is.
     *
     * @param whatEachEdgeIs every edge shape met, and what its instances were found to be
     * @param neither the edges that are neither, one line each, in an order a reader can follow
     * @param witnessed the shapes some instance of which was seen to project something: an answer
     *                  holding nothing is entries of every index there is, so a shape read as a
     *                  projection over nothing but those was never asked the question
     * @param instances how many edges were read, which says a census of nothing is a census of
     *                  nothing rather than a clean one
     */
    record Census(Map<Edge, Set<WhatItIs>> whatEachEdgeIs, List<String> neither,
                  Set<Edge> witnessed, int instances) {}

    /**
     * What the graph held before the edit, read against what it held after.
     *
     * <p>The edit is the one that tells the two apart. A projection is a projection whatever is
     * edited, and it is asked first; what is left is asked of the index, which either came out equal
     * under the edit or moved and dragged a reader that means less than it does.
     */
    static Census taken(Snapshot before, Snapshot after) {
        Map<Edge, Set<WhatItIs>> whatEachEdgeIs = new LinkedHashMap<>();
        List<String> neither = new ArrayList<>();
        Set<Edge> witnessed = new TreeSet<>();
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
                WhatItIs is = switch (projects(each.getValue(), index)) {
                    case OF_SOMETHING -> {
                        witnessed.add(edge);
                        yield WhatItIs.A_PROJECTION;
                    }
                    case OF_NOTHING_AT_ALL -> WhatItIs.A_PROJECTION;
                    case OF_NOTHING_OF_THIS_INDEX ->
                            Objects.equals(index, after.answers().get(read))
                                    ? WhatItIs.AN_ANSWER_EQUAL_UNDER_A_SIBLING_EDIT : null;
                };
                if (is == null) {
                    neither.add(edge + ", at " + reader + ", reading " + read);
                    continue;
                }
                whatEachEdgeIs.computeIfAbsent(edge, _ -> new TreeSet<>()).add(is);
            }
        }
        Collections.sort(neither);
        return new Census(whatEachEdgeIs, neither, witnessed, instances);
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
     * <p>An answer holding nothing is a projection and says nothing. It is entries of every index
     * there is, so a fold that came to nothing over this fixture reads the same as a projection —
     * which is why a shape read as a projection is held to being witnessed projecting something
     * somewhere, and the two are told apart here rather than at the assertion.
     */
    private static Projection projects(Answer<?> reader, Answer<?> index) {
        if (reader == null || !reader.present()) {
            return Projection.OF_NOTHING_AT_ALL;
        }
        if (index == null || !index.present()) {
            return Projection.OF_NOTHING_OF_THIS_INDEX;
        }
        Object held = reader.value();
        Collection<?> entries = entriesOf(index.value());
        Collection<?> mine = entriesOf(held);
        if (mine != null && mine.isEmpty()) {
            return Projection.OF_NOTHING_AT_ALL;
        }
        if (entries.contains(held) || (mine != null && entries.containsAll(mine))) {
            return Projection.OF_SOMETHING;
        }
        return Projection.OF_NOTHING_OF_THIS_INDEX;
    }

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
            if (narrows(part, held(key, part), key.module())) {
                return true;
            }
        }
        return false;
    }

    /**
     * Whether what a key holds at one of its components names something the module it is about
     * holds, rather than the module or how to read it.
     *
     * <p>Read off the component rather than off how many there are. A key naming one declaration
     * holds one thing ({@link Shapes.FieldBindingsOf}) and a key about a module holds more than one
     * where the rest say how to read it ({@link Bodies.Expanding} takes a policy), so a count
     * misreads both ways.
     *
     * <p>A name written as text is the one case decided by what is there: a module says its own
     * name and a definition of it says a different one, and no type tells the two apart. Every other
     * type is {@link #whatAComponentHolds}'s to say, over what this compiler declares rather than
     * over what a fixture reached.
     */
    private static boolean narrows(RecordComponent part, Object held, String module) {
        if (part.getType() == String.class) {
            return !(held instanceof String named) || !named.equals(module);
        }
        return WHAT_A_COMPONENT_HOLDS.get(part.getType())
                == WhatAComponentHolds.SOMETHING_THE_MODULE_HOLDS;
    }

    /**
     * What each edge of the graph is, said once so that a check can read it.
     *
     * <p>Written down rather than worked out, for the reason the classification cannot be read off
     * the graph at all. An edge read as sound because it came out sound over one fixture is an edge
     * nobody has judged, and the day it stops being a projection the census would follow it into
     * whatever it became. Held here, the shape says what it is and the census is held to that.
     */
    static Map<Edge, Set<WhatItIs>> written() {
        Map<Edge, Set<WhatItIs>> out = new LinkedHashMap<>();
        projection(out, Bodies.BehaviorAritiesForBody.class, Bodies.NamedBehaviorArity.class);
        projection(out, Bodies.CalleeSigsForBody.class, Bodies.CalleeSigs.class);
        projection(out, Bodies.DeclaredSignature.class, Bodies.DeclaredSignatures.class);
        projection(out, Bodies.SettledFn.class, Bodies.RowFixtureDefs.class);
        projection(out, Bodies.Stated.class, Bodies.StatedContracts.class);
        projection(out, Names.Declaration.class, Names.Declarations.class);
        projection(out, Names.ResolvedDeclaration.class, Names.ResolvedDeclarations.class);
        projection(out, Shapes.DerivedDef.class, Shapes.DerivedDeclarations.class);
        projection(out, Shapes.NormalizedDef.class, Shapes.NormalizedDeclarations.class);
        equalUnderASiblingEdit(out, Bodies.Assumptions.class, Bodies.StatedContracts.class);
        equalUnderASiblingEdit(out, Bodies.CheckedBehavior.class, Bodies.RecursiveCallSigs.class);
        equalUnderASiblingEdit(out, Bodies.CheckedBehavior.class, Bodies.ReqSigs.class);
        equalUnderASiblingEdit(out, Bodies.CheckedBehavior.class,
                Bodies.RecursiveHelperConstructs.class);
        equalUnderASiblingEdit(out, Names.Definition.class, Names.Unbuilt.class);
        equalUnderASiblingEdit(out, Shapes.ClausesExpandedFor.class,
                Shapes.ExpandedDeclarationClauses.class);
        return out;
    }

    private static void projection(Map<Edge, Set<WhatItIs>> out, Class<?> reader, Class<?> index) {
        out.put(new Edge(reader, index), Set.of(WhatItIs.A_PROJECTION));
    }

    private static void equalUnderASiblingEdit(Map<Edge, Set<WhatItIs>> out, Class<?> reader,
                                               Class<?> index) {
        out.put(new Edge(reader, index),
                Set.of(WhatItIs.AN_ANSWER_EQUAL_UNDER_A_SIBLING_EDIT));
    }

    /** What a key holds at a component, which is one of two things and never a third. */
    enum WhatAComponentHolds {

        /** A name of something the module holds — a declaration, a definition, a clause, a place in
         *  a file — so a question holding it means less than its module does. */
        SOMETHING_THE_MODULE_HOLDS,

        /** Which module, which of its files, or how what is asked for is to be read. A question
         *  holding nothing else is a question about the module. */
        THE_MODULE_OR_HOW_TO_READ_IT
    }

    /**
     * What each type a question holds at a component is, so that a new one arrives as a failure
     * rather than as a question quietly left out of the census.
     *
     * <p>Both words written down and no default, because either way round is wrong on its own. Read
     * as naming something, a policy would make every question about a module read as a question
     * about one of its definitions; read as saying which module, a name of a kind nothing here knows
     * would take every index that question folds in out of the census — and that is the reading
     * which hides the defect this is about.
     */
    static Map<Class<?>, WhatAComponentHolds> whatAComponentHolds() {
        return WHAT_A_COMPONENT_HOLDS;
    }

    /** Read once per component of every key in a census, so it is built once. */
    private static final Map<Class<?>, WhatAComponentHolds> WHAT_A_COMPONENT_HOLDS = whatEachIs();

    private static Map<Class<?>, WhatAComponentHolds> whatEachIs() {
        Map<Class<?>, WhatAComponentHolds> out = new LinkedHashMap<>();
        names(out, int.class);
        names(out, DefinitionName.class);
        names(out, Clause.Id.class);
        names(out, RuleRef.Written.class);
        names(out, SourcePos.class);
        names(out, WrittenCondition.class);
        names(out, SourceConstructOrigin.class);
        names(out, TypeKey.class);
        names(out, TypeSymbol.class);
        names(out, TypeSymbol.AtModule.class);
        names(out, ValueName.class);
        names(out, ValueName.Behavior.class);
        saysWhichModule(out, InliningPolicy.class);
        saysWhichModule(out, ArmObservation.class);
        saysWhichModule(out, GenerationScope.class);
        saysWhichModule(out, SourceId.class);
        return out;
    }

    private static void names(Map<Class<?>, WhatAComponentHolds> out, Class<?> type) {
        out.put(type, WhatAComponentHolds.SOMETHING_THE_MODULE_HOLDS);
    }

    private static void saysWhichModule(Map<Class<?>, WhatAComponentHolds> out, Class<?> type) {
        out.put(type, WhatAComponentHolds.THE_MODULE_OR_HOW_TO_READ_IT);
    }

    /** Every type the questions this compiler declares hold at a component, other than a name
     *  written as text. */
    static Set<Class<?>> componentTypes(List<Class<?>> questions) {
        Set<Class<?>> out = new LinkedHashSet<>();
        for (Class<?> question : questions) {
            RecordComponent[] parts = question.getRecordComponents();
            if (parts == null) {
                continue;
            }
            for (RecordComponent part : parts) {
                if (part.getType() != String.class) {
                    out.add(part.getType());
                }
            }
        }
        return out;
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
