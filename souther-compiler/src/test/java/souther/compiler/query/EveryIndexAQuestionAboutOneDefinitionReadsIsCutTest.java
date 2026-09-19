package souther.compiler.query;

import souther.compiler.meta.ModulePath;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
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
 * <p><b>Over the graph one compile built, which is narrower than the vocabulary.</b> A question this
 * fixture never asks has no edges here, and the register would not miss it. That is the price of a
 * classification an edit has to settle: what the compiler declares can be walked without running
 * anything, and what an edge is cannot. What holds the gap down is the register — a shape written
 * here is a shape the fixture has to go on reaching, so a fixture that stopped reaching one fails
 * rather than quietly checking less.
 *
 * <p><b>An edit that leaves the index where it was asks the edge nothing.</b> Every index is
 * gathered over a different kind of thing, and one edit moves some of them: a behavior declared
 * beside adds an entry to what the module declares and none to what its behaviors require. So the
 * edits are {@link Edit}, each additive and each about nothing already written, and every edge is
 * held to having been met under one that moved the index it reads. An edge no edit here moves is an
 * edge nobody has put a question to, and it fails as one.
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
            module shop.orders exposing
                ( Code, Amount, Line, priceOf, twiceOf, codeOf, labelOf, totalOf )

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

            partial let spinDown (n: Int): Amount =
                if n <= 0 then Amount { value = 0 } else spinDown(n - 1)

            behavior totalOf : (line: Line) -> Amount
            let totalOf (line) = spinDown(line.amount.value)

            example priceOf
                | "one" : (Line { code = Code { value = "AB123" }, amount = Amount { value = 1 } })
                    -> Amount { value = 1 }
            """;

    /**
     * The ways this module is added to, each saying nothing about anything already written in it.
     *
     * <p>Additive, and that is what makes them siblings. Changing a definition that is already here
     * would be an edit to a definition the census holds edges of, and every reader of that
     * definition would be recomputed for its own sake — which is a reader doing what it is for, and
     * nothing this is about. What arrives is a definition nothing here names and which names
     * nothing here.
     */
    private enum Edit {

        /** Which behaviors the module declares, what each takes, and what a body may call. */
        A_BEHAVIOR_DECLARED_BESIDE("""

                behavior weigh : (x: Int) -> Int
                let weigh (x) = x
                """),

        /**
         * What the behaviors of the module require. A behavior with nothing to inject is in none of
         * this, so a behavior declared beside leaves it where it was however much else it moves.
         */
        A_BEHAVIOR_BESIDE_TAKING_A_REQUIREMENT("""

                behavior fetch : (x: Int) -> Amount
                    constructs Amount

                behavior order : (x: Int) -> Amount depends on fetch
                let order (x, fetch) = fetch(x)
                """),

        /** What each behavior of the module states about its answer. */
        A_BEHAVIOR_BESIDE_STATING_A_RULE("""

                behavior atLeast : (x: Int) -> Int
                    ensures value >= x
                let atLeast (x) = x
                """),

        /** What the module declares, resolves, normalizes and derives. */
        A_DATA_DECLARED_BESIDE("""

                data Spare = Int
                    invariant value >= 1
                """),

        /** The definitions a module writes to run its rows. */
        A_ROW_WRITTEN_BESIDE("""

                behavior half : (x: Int) -> Int
                let half (x) = Rational.toInt(DOWN, x / 2)

                example half
                    | "two" : (2) -> 1
                """),

        /** What the module has to emit because an expansion could not remove it, and what those
         *  recursions are typed as. */
        A_RECURSIVE_HELPER_BESIDE("""

                partial let countDown (n: Int): Int = if n <= 0 then 0 else countDown(n - 1)

                behavior down : (x: Int) -> Int
                let down (x) = countDown(x)
                """),

        /**
         * Which of the module's declarations have no meaning to give.
         *
         * <p>The one edit the compiler has something to say about, and it has to be: what this index
         * holds is the declarations that did not come out, so nothing that compiles moves it. What is
         * said is said about the declaration added here and about nothing that was already written.
         */
        A_DECLARATION_BESIDE_THAT_CANNOT_BE_BUILT("""

                data Broken = { missing: NoSuchType }
                """, "E1023");

        private final String added;
        private final List<String> says;

        Edit(String added, String... says) {
            this.added = added;
            this.says = List.of(says);
        }

        String source() {
            return MODULE + added;
        }

        /**
         * What the compiler is expected to say once this is added.
         *
         * <p>Which problems and not whether there are any. An edit that broke something already
         * written would say something too, and every verdict taken under it would be a verdict about
         * a module the edit had changed the meaning of.
         */
        List<String> says() {
            return says;
        }
    }

    private static final String ID = "orders.sou";

    /** What each edit made of the graph, worked out once for the class that asks. */
    private static final Map<Edit, IndexEdges.Census> CENSUS = census();

    private static Map<Edit, IndexEdges.Census> census() {
        Map<Edit, IndexEdges.Census> out = new LinkedHashMap<>();
        for (Edit edit : Edit.values()) {
            Map<String, String> byId = new LinkedHashMap<>();
            byId.put(ID, MODULE);
            Compilation c = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
            c.measure(Adequacy.Asked.fullReport());
            c.answerEverything();
            assertTrue(c.db().allReports().isEmpty(),
                    () -> "the module compiles to begin with: " + said(c));
            IndexEdges.Snapshot before = IndexEdges.Snapshot.of(c.db());

            c.update(Map.of(ID, edit.source()), Set.of());
            c.measure(Adequacy.Asked.fullReport());
            c.answerEverything();
            assertEquals(edit.says(), codesFrom(c),
                    () -> "after " + edit + " the compiler said " + said(c));

            out.put(edit, IndexEdges.taken(before, IndexEdges.Snapshot.of(c.db())));
        }
        return out;
    }

    /** Which problems the compiler has, in the order it found them. */
    private static List<String> codesFrom(Compilation c) {
        return c.db().allReports().stream()
                .map(each -> each.report().diagnostic().code()).toList();
    }

    /** What the compiler said about the fixture, as a reader of a failure can read it. */
    private static List<String> said(Compilation c) {
        return c.db().allReports().stream()
                .map(each -> each.report().diagnostic().severity() + " "
                        + each.report().diagnostic().code() + " "
                        + each.report().diagnostic().said())
                .toList();
    }

    /**
     * What an edge was found to be, and under the edit that found it.
     *
     * <p>The edit is kept beside the verdict rather than folded away. An edit that stopped moving an
     * index leaves every edge under it exactly as they were, so a register of verdicts alone cannot
     * tell an edge that is still held from one nothing is asking any more.
     */
    private record Witness(IndexEdges.WhyItHeld is, Edit under) implements Comparable<Witness> {

        @Override
        public String toString() {
            return is + " under " + under;
        }

        @Override
        public int compareTo(Witness other) {
            return toString().compareTo(other.toString());
        }
    }

    /** What each edge of the graph was met as. */
    private static Map<IndexEdges.Edge, Set<Witness>> met() {
        Map<IndexEdges.Edge, Set<Witness>> out = new TreeMap<>();
        CENSUS.forEach((edit, census) -> census.whereTheIndexMoved().forEach((edge, was) ->
                was.forEach(is -> out.computeIfAbsent(edge, _ -> new TreeSet<>())
                        .add(new Witness(is, edit)))));
        return out;
    }

    /** What two accounts differ over, in an order a reader can follow. */
    private static List<String> differencesBetween(Map<IndexEdges.Edge, Set<Witness>> written,
                                                   Map<IndexEdges.Edge, Set<Witness>> met) {
        Set<IndexEdges.Edge> every = new TreeSet<>(written.keySet());
        every.addAll(met.keySet());
        List<String> out = new ArrayList<>();
        every.forEach(edge -> {
            if (!Objects.equals(written.get(edge), met.get(edge))) {
                out.add(edge + ": written down " + written.get(edge) + ", met as " + met.get(edge));
            }
        });
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
        IndexEdges.Census first = CENSUS.get(Edit.A_BEHAVIOR_DECLARED_BESIDE);
        Set<IndexEdges.Edge> shapes = new TreeSet<>();
        first.everyEdge().forEach(at -> shapes.add(at.shape()));

        assertTrue(first.everyEdge().size() > 20,
                () -> "a census of " + first.everyEdge().size() + " edges is not this compiler's"
                        + " graph");
        assertTrue(shapes.size() > 8,
                () -> "a census of " + shapes.size() + " shapes is not this compiler's graph");
    }

    /** And every edge an edit moved the index of is one of the two, at every definition it stands
     *  at. */
    @Test
    void noEdgeIsNeitherAProjectionNorEqualUnderASiblingEdit() {
        List<String> neither = new ArrayList<>();
        CENSUS.forEach((edit, census) ->
                census.neither().forEach(each -> neither.add(each + ", under " + edit)));

        assertEquals(List.of(), neither,
                "a question about one definition took its module's index whole, so an edit to a"
                        + " definition it says nothing about is an edit to this one");
    }

    /**
     * And every edge in the graph was met under an edit that moved the index it reads.
     *
     * <p>Its own sentence because the other half of each verdict can be had for nothing. An index
     * that stays where it was leaves every reader of it alone whether the reader means one entry or
     * the module, so a verdict read off an edit that moved nothing is a verdict about the edit. An
     * edge here that no edit moves is one nobody has put a question to, and what it wants is an edit
     * that moves its index rather than a word in the register.
     *
     * <p><b>Edge by edge and not shape by shape.</b> Two edges of one shape are two edges, and an
     * edit may move the index of one and leave the other's — a question asked under one policy and
     * an index gathered under another are exactly that. Folded to the shape before the difference is
     * taken, the one that was asked stands as the other's witness, which is the reading this whole
     * check exists to refuse. The register is by shape because a judgement is about a question; what
     * an edit did is about these.
     */
    @Test
    void everyEdgeWasMetUnderAnEditThatMovedItsIndex() {
        Set<IndexEdges.At> everyEdge = new TreeSet<>();
        Set<IndexEdges.At> exercised = new TreeSet<>();
        CENSUS.values().forEach(census -> {
            everyEdge.addAll(census.everyEdge());
            exercised.addAll(census.exercised());
        });
        Set<IndexEdges.At> untouched = new TreeSet<>(everyEdge);
        untouched.removeAll(exercised);

        assertEquals(Set.of(), untouched,
                "an edge no edit here moves the index of, so what it is was never asked");
    }

    /**
     * What each edge of this compiler's graph was seen to be, and under which edit, said once so
     * that this can read it.
     *
     * <p>Written down rather than worked out, because an edge read as sound because it came out
     * sound is an edge nobody has judged: the day one stops holding the way it held, the census
     * would follow it into whatever it became.
     *
     * <p>A register of observations and not of natures. An entry says an edit moved this index and
     * the reader held, and why it held that time; an edge seen both ways is written both ways.
     */
    private static Map<IndexEdges.Edge, Set<Witness>> written() {
        Map<IndexEdges.Edge, Set<Witness>> out = new TreeMap<>();
        metEitherWay(out,Bodies.BehaviorAritiesForBody.class, Bodies.NamedBehaviorArity.class,
                Edit.A_BEHAVIOR_BESIDE_STATING_A_RULE, Edit.A_BEHAVIOR_DECLARED_BESIDE,
                Edit.A_RECURSIVE_HELPER_BESIDE, Edit.A_ROW_WRITTEN_BESIDE);
        metEitherWay(out,Bodies.CalleeSigsForBody.class, Bodies.CalleeSigs.class,
                Edit.A_BEHAVIOR_BESIDE_STATING_A_RULE, Edit.A_BEHAVIOR_DECLARED_BESIDE,
                Edit.A_RECURSIVE_HELPER_BESIDE, Edit.A_ROW_WRITTEN_BESIDE);
        projection(out, Bodies.DeclaredSignature.class, Bodies.DeclaredSignatures.class,
                Edit.A_BEHAVIOR_BESIDE_STATING_A_RULE,
                Edit.A_BEHAVIOR_BESIDE_TAKING_A_REQUIREMENT, Edit.A_BEHAVIOR_DECLARED_BESIDE,
                Edit.A_RECURSIVE_HELPER_BESIDE, Edit.A_ROW_WRITTEN_BESIDE);
        metEitherWay(out,Bodies.RecursiveCallSigsForBody.class, Bodies.RecursiveCallSigs.class,
                Edit.A_RECURSIVE_HELPER_BESIDE);
        metEitherWay(out,Bodies.RecursiveHelperConstructsForBody.class,
                Bodies.RecursiveHelperConstructs.class, Edit.A_RECURSIVE_HELPER_BESIDE);
        projection(out, Bodies.SettledFn.class, Bodies.RowFixtureDefs.class,
                Edit.A_ROW_WRITTEN_BESIDE);
        metEitherWay(out,Bodies.Stated.class, Bodies.StatedContracts.class,
                Edit.A_BEHAVIOR_BESIDE_STATING_A_RULE);
        projection(out, Names.Declaration.class, Names.Declarations.class,
                Edit.A_DATA_DECLARED_BESIDE, Edit.A_DECLARATION_BESIDE_THAT_CANNOT_BE_BUILT);
        projection(out, Names.ResolvedDeclaration.class, Names.ResolvedDeclarations.class,
                Edit.A_DATA_DECLARED_BESIDE, Edit.A_DECLARATION_BESIDE_THAT_CANNOT_BE_BUILT);
        projection(out, Shapes.DerivedDef.class, Shapes.DerivedDeclarations.class,
                Edit.A_DATA_DECLARED_BESIDE);
        projection(out, Shapes.NormalizedDef.class, Shapes.NormalizedDeclarations.class,
                Edit.A_DATA_DECLARED_BESIDE, Edit.A_DECLARATION_BESIDE_THAT_CANNOT_BE_BUILT);
        equalUnderASiblingEdit(out, Bodies.Assumptions.class, Bodies.StatedContracts.class,
                Edit.A_BEHAVIOR_BESIDE_STATING_A_RULE);
        equalUnderASiblingEdit(out, Bodies.CheckedBehavior.class, Bodies.ReqSigs.class,
                Edit.A_BEHAVIOR_BESIDE_TAKING_A_REQUIREMENT);
        equalUnderASiblingEdit(out, Names.Definition.class, Names.Unbuilt.class,
                Edit.A_DECLARATION_BESIDE_THAT_CANNOT_BE_BUILT);
        equalUnderASiblingEdit(out, Shapes.ClausesExpandedFor.class,
                Shapes.ExpandedDeclarationClauses.class, Edit.A_DATA_DECLARED_BESIDE,
                Edit.A_DECLARATION_BESIDE_THAT_CANNOT_BE_BUILT);
        // Which declarations are answered together is a fact about the graph rather than about any
        // declaration in it, so it is worked out once for the module and each declaration is handed
        // the component it is in. A declaration written beside them is a component of its own and
        // leaves every other component where it was, which is what keeps the counts built on this
        // from being taken again.
        equalUnderASiblingEdit(out, Shapes.CardinalityComponentOf.class,
                Shapes.CardinalityComponentsOf.class, Edit.A_DATA_DECLARED_BESIDE,
                Edit.A_DECLARATION_BESIDE_THAT_CANNOT_BE_BUILT);
        return out;
    }

    private static void projection(Map<IndexEdges.Edge, Set<Witness>> out, Class<?> reader,
                                   Class<?> index, Edit... under) {
        out.put(new IndexEdges.Edge(reader, index), witnesses(IndexEdges.WhyItHeld.A_PROJECTION,
                under));
    }

    /**
     * An edge met both ways: its answer is an entry of the index at a definition that has one, and
     * nothing at a definition that has none.
     *
     * <p>Two observations of one edge and not two natures of it. What this register holds is what
     * was seen under each edit — the edge held, and here is why it held that time — so an edge
     * standing at a behavior that names none and at a behavior that names one is seen both ways and
     * says so. The stronger word alone would be a claim about instances nobody looked at.
     */
    private static void metEitherWay(Map<IndexEdges.Edge, Set<Witness>> out, Class<?> reader,
                                     Class<?> index, Edit... under) {
        Set<Witness> both = new TreeSet<>(witnesses(IndexEdges.WhyItHeld.A_PROJECTION, under));
        both.addAll(witnesses(IndexEdges.WhyItHeld.AN_ANSWER_EQUAL_UNDER_A_SIBLING_EDIT, under));
        out.put(new IndexEdges.Edge(reader, index), both);
    }

    private static void equalUnderASiblingEdit(Map<IndexEdges.Edge, Set<Witness>> out,
                                               Class<?> reader, Class<?> index, Edit... under) {
        out.put(new IndexEdges.Edge(reader, index),
                witnesses(IndexEdges.WhyItHeld.AN_ANSWER_EQUAL_UNDER_A_SIBLING_EDIT, under));
    }

    private static Set<Witness> witnesses(IndexEdges.WhyItHeld is, Edit... under) {
        Set<Witness> out = new TreeSet<>();
        for (Edit each : under) {
            out.add(new Witness(is, each));
        }
        return out;
    }

    /** And each is what is written down beside it. */
    @Test
    void everyEdgeIsWhatIsWrittenDownBesideIt() {
        assertEquals(List.of(), differencesBetween(written(), met()),
                "an edge of the store's graph that nobody has said what it is");
    }

    /**
     * And somebody has read every component of every question the census met.
     *
     * <p>No default either way, because the two halves of the census want opposite ones. A reader
     * holding an unread component is safer read as naming something, which puts its reads of an
     * index into the census; an index holding one is safer read as saying which module, because
     * reading it as naming something takes the index itself out of the census and every edge into it
     * along with it. A word that leaned either way would be quietly wrong about the other half, so
     * an unread component is a failure and not a reading.
     */
    @Test
    void somebodyHasReadEveryComponentTheCensusMet() {
        Set<IndexEdges.Part> unread = new TreeSet<>();
        CENSUS.values().forEach(census -> unread.addAll(census.unread()));

        assertEquals(Set.of(), unread,
                "a question holds something at a component that nobody has said whether it names"
                        + " something the module holds");
    }

    /**
     * And what somebody said a component holds is what it holds, whatever is in it.
     *
     * <p>A module and a definition of it may be spelled alike — {@code module orders} with a
     * {@code behavior orders} in it — and then the text at a component says module while the
     * component says behavior. Read off the text, that question stops being about one definition,
     * every index it reads leaves the census, and nothing says so: the reading is not
     * {@code UNREAD}, so the question that catches an unread component never sees it.
     *
     * <p>Its own sentence rather than a line of the census, because the census cannot show it. The
     * shape of every edge that instance holds is held by its siblings too, so what is lost is one
     * instance out of many and no count this keeps would move.
     */
    @Test
    void whatSomebodySaidAComponentHoldsBeatsWhatIsInIt() {
        Key<?> named = new Bodies.CheckedBehavior("orders", "orders");

        assertEquals(IndexEdges.WhatAComponentHolds.SOMETHING_THE_MODULE_HOLDS,
                IndexEdges.roleAt(named, "behavior"),
                "a behavior spelled like the module it is in was read as the module");
        assertEquals(IndexEdges.WhatAComponentHolds.THE_MODULE,
                IndexEdges.roleAt(named, "module"),
                "and the component that is the module is still the module");
    }

    /**
     * And every component that register reads is one a question still holds.
     *
     * <p>The other side of the same table. A line left behind by a key that has moved on says
     * nothing and is read by nothing, and the register is what the census rests on.
     */
    @Test
    void everyComponentReadIsOneAQuestionStillHolds() throws Exception {
        List<Class<?>> questions = DeclaredQuestions.found(DeclaredQuestions.scan());

        assertTrue(questions.size() > 100,
                () -> "a vocabulary of " + questions.size() + " is not this compiler's");
        assertEquals(Set.of(), IndexEdges.staleIn(questions),
                "a component written down here, which no question holds");
    }
}
