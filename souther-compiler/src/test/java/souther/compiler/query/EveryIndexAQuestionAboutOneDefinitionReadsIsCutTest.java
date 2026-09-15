package souther.compiler.query;

import souther.compiler.meta.ModulePath;
import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An edge is what its consumer means: a question about one definition depends on the entries it
 * reaches, and never on the index its module gathered them into.
 *
 * <p>The third of the rules {@link Db} states. {@code EverythingAnAnswerHoldsMeansSomethingTest}
 * says what an answer may hold and {@code EveryAnswerThisCompilerDeclaresIsSettledTest} which of the
 * two kinds a question is read under; this one is what nothing else sees, because a breach of it
 * leaves every answer the compiler gives unchanged. What it costs is work, so without a check the
 * only way to it is somebody noticing that an edit has become slow — which finds one reader at a
 * time while the shape goes on being written.
 *
 * <p><b>The census is the graph's and not the source's.</b> Which index a {@code compute} reaches
 * through a helper and a branch is not something a reading of the file settles, and a register
 * written by hand would be a register of what somebody looked at. {@link IndexEdges} asks the store
 * what a compile actually built.
 *
 * <p><b>The classification is not the graph's.</b> Which of the two sound forms an edge is takes the
 * graph, what equality says about the answers, and an edit — so the edit is here, and it is a
 * behavior declared beside the ones the module already had. A behavior is the one thing a module
 * gathers every kind of index over, and declaring one says nothing about any definition already
 * written — so an answer about one of those that moves under it moved for the module's sake.
 */
class EveryIndexAQuestionAboutOneDefinitionReadsIsCutTest {

    /**
     * A module with enough in it to reach the questions this is about.
     *
     * <p>Declarations with rules of their own, a helper, behaviors that state something about their
     * answers and one that names another behavior, and a row to run. What is wanted of each is an
     * index: a module gathers one per kind of thing in it, and a kind of thing the fixture does not
     * write is a column of the census that is never read.
     */
    private static final String MODULE = """
            module shop.orders exposing ( Code, Amount, Line, priceOf, twiceOf, codeOf, labelOf )

            data Code = String
                invariant String.matches("[A-Z]{2}[0-9]{3}", value)
            data Amount = Int
                invariant value >= 0 && value <= 1000
            data Line = { code: Code, amount: Amount }

            let double (n: Int) = n * 2

            behavior priceOf : (line: Line) -> Amount
                ensures value.value >= line.amount.value
            let priceOf (line) = line.amount

            behavior twiceOf : (line: Line) -> Int
            let twiceOf (line) = double(line.amount.value)

            behavior codeOf : (line: Line) -> Code
                ensures value.value == line.code.value
            let codeOf (line) = line.code

            behavior labelOf : (line: Line) -> String
            let labelOf (line) = codeOf(line).value

            example priceOf
                | "one" : (Line { code = Code { value = "AB123" }, amount = Amount { value = 1 } })
                    -> Amount { value = 1 }
            """;

    /**
     * The same module with one more behavior declared after all of them.
     *
     * <p>Nothing here names it and it names nothing here, so what every definition the module
     * already had means is what it meant. What moves is the module: every index it gathers has one
     * more entry.
     */
    private static final String AND_ONE_MORE_BEHAVIOR = MODULE + """

            behavior weigh : (x: Int) -> Int
            let weigh (x) = x
            """;

    private static final String ID = "orders.sou";

    /** What the store held before the edit and after it, worked out once for the class that asks. */
    private static final IndexEdges.Census CENSUS = census();

    private static IndexEdges.Census census() {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put(ID, MODULE);
        Compilation c = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        c.measure(Adequacy.Asked.fullReport());
        c.answerEverything();
        assertTrue(c.db().allReports().isEmpty(),
                () -> "the module compiles to begin with: " + said(c));
        IndexEdges.Snapshot before = IndexEdges.Snapshot.of(c.db());

        c.update(Map.of(ID, AND_ONE_MORE_BEHAVIOR), Set.of());
        c.measure(Adequacy.Asked.fullReport());
        c.answerEverything();
        assertTrue(c.db().allReports().isEmpty(),
                () -> "and after the behavior beside it: " + said(c));

        return IndexEdges.taken(before, IndexEdges.Snapshot.of(c.db()));
    }

    /** What the compiler said about the fixture, as a reader of a failure can read it. */
    private static List<String> said(Compilation c) {
        return c.db().allReports().stream()
                .map(each -> each.report().diagnostic().severity() + " "
                        + each.report().diagnostic().code() + " "
                        + each.report().diagnostic().said())
                .toList();
    }

    /** The same set of types, as a failure reads them. */
    private static Set<String> named(Set<Class<?>> types) {
        Set<String> out = new TreeSet<>();
        types.forEach(each -> out.add(each.getName()));
        return out;
    }

    /** What is written down, by what makes each edge sound. */
    private static Map<String, Set<String>> written() {
        Map<String, Set<String>> out = new TreeMap<>();
        IndexEdges.written().forEach((edge, is) -> out.put(edge.toString(),
                new TreeSet<>(is.stream().map(Enum::name).toList())));
        return out;
    }

    private static Map<String, Set<String>> met() {
        Map<String, Set<String>> out = new TreeMap<>();
        CENSUS.whatEachEdgeIs().forEach((edge, is) -> out.put(edge.toString(),
                new TreeSet<>(is.stream().map(Enum::name).toList())));
        return out;
    }

    /**
     * The census reaches the edges this is about.
     *
     * <p>The control the assertions below need. A store where no question about a definition ever
     * read an index answers every one of them, and a fixture that stopped reaching the compiler's
     * later passes would take the shapes with it one at a time.
     */
    @Test
    void theCensusReachesTheEdgesThisIsAbout() {
        IndexEdges.Census census = CENSUS;

        assertTrue(census.instances() > 20,
                () -> "a census of " + census.instances() + " edges is not this compiler's graph");
        assertTrue(census.whatEachEdgeIs().size() > 8,
                () -> "a census of " + census.whatEachEdgeIs().size() + " shapes is not this"
                        + " compiler's graph");
    }

    /** And every edge in it is one of the two, at every definition it stands at. */
    @Test
    void noEdgeIsNeitherAProjectionNorEqualUnderASiblingEdit() {
        assertEquals(List.of(), CENSUS.neither(),
                "a question about one definition took its module's index whole, so a behavior"
                        + " declared beside it is an edit to this definition");
    }

    /** And each is what is written down beside it. */
    @Test
    void everyEdgeIsWhatIsWrittenDownBesideIt() {
        assertEquals(written(), met(),
                "an edge of the store's graph that nobody has said what it is");
    }

    /**
     * And every edge written down as a projection was seen projecting something.
     *
     * <p>Its own sentence because an answer holding nothing is entries of every index there is. A
     * reader that folds an index in and came to nothing over this fixture reads as a projection, so
     * what says a projection is a projection is an instance where there was something to project.
     */
    @Test
    void everyProjectionWrittenDownWasSeenProjectingSomething() {
        Set<String> written = new TreeSet<>();
        IndexEdges.written().forEach((edge, is) -> {
            if (is.contains(IndexEdges.WhatItIs.A_PROJECTION)) {
                written.add(edge.toString());
            }
        });
        Set<String> witnessed = new TreeSet<>();
        CENSUS.witnessed().forEach(edge -> witnessed.add(edge.toString()));

        assertEquals(written, witnessed,
                "a projection nothing was ever seen to project, which is what an answer holding"
                        + " nothing reads as");
    }

    /**
     * And somebody has said what every type a question holds at a component is.
     *
     * <p>Quantified over what this compiler declares rather than over what the fixture reached,
     * because this is the reading the census rests on and both ways of getting it wrong are silent:
     * a policy read as a name makes every question about a module read as a question about one of
     * its definitions, and a name of a kind nothing here knows takes every index its question folds
     * in out of the census.
     */
    @Test
    void somebodyHasSaidWhatEveryTypeAQuestionHoldsIs() throws Exception {
        List<Class<?>> questions = DeclaredQuestions.found(DeclaredQuestions.scan());

        assertTrue(questions.size() > 100,
                () -> "a vocabulary of " + questions.size() + " is not this compiler's");
        assertEquals(named(IndexEdges.whatAComponentHolds().keySet()),
                named(IndexEdges.componentTypes(questions)),
                "a question holds something at a component that nobody has said whether it names"
                        + " something the module holds");
    }
}
