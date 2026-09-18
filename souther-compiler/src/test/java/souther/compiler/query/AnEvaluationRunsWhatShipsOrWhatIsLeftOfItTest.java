package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.SoutherJvmAbi;
import souther.compiler.meta.ModulePath;
import souther.compiler.observe.ArmObservation;
import souther.compiler.observe.Disposition;
import souther.compiler.observe.FailurePhase;
import souther.compiler.observe.RowOutcome;
import souther.compiler.generated.EvaluationArtifact;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a row is run against: the program this compile ships, or what is left of it.
 *
 * <p>Two artifacts and one reading of the module behind them. {@link Output.Classes} is what a jar
 * carries and is a whole module or nothing; {@link Output.Evaluated} is never written out, and a
 * module holding one body nothing elaborated holds the rest of its bodies all the same.
 *
 * <p>Where the module came out whole the two are the same program, and that is held here as
 * identity rather than as agreement. Two elaborations equal by value would carry equal plans filed
 * under different objects, and a run numbered against one and read against the other agrees until
 * it does not.
 */
class AnEvaluationRunsWhatShipsOrWhatIsLeftOfItTest {

    /**
     * A chain of callers over a body the invariant refuses, and one behavior off to the side.
     *
     * <p>{@code %s} is what {@code mint} constructs, so the whole module and the module with a
     * refused body differ in that and in nothing else.
     */
    private static final String MODEL = """
            module demo

            data Seat = Int
                invariant value >= 1 && value <= 300

            behavior apart : (n: Int) -> Int
            let apart (n) = n

            behavior onwards = apart >-> thrice

            behavior thrice : (n: Int) -> Seat
            let thrice (n) = twice(n)

            behavior twice : (n: Int) -> Seat
            let twice (n) = mint(n)

            behavior mint : (n: Int) -> Seat
                constructs Seat
            let mint (n) = Seat(%s)

            example twice
                | "one" : (1) -> Seat(1)
            """;

    /**
     * A whole module is observed against the very program it ships.
     *
     * <p>The one answer, and not a second one built to match. This is what the partial elaboration
     * beside it is a refinement of: asked of a module with nothing missing, it hands back what the
     * whole check came to.
     */
    @Test
    void whereTheModuleCameOutWholeAnEvaluationObservesTheProgramThatShips() {
        Compilation clean = compile("1");

        Answer<Bodies.Elaborated> ships = clean.db().ask(new Bodies.Checked("demo"));
        Answer<Bodies.Elaborated> observed = clean.db().ask(new Bodies.Observable("demo"));

        assertTrue(ships.present(), "this model is written to be a module that ships");
        assertSame(ships.value(), observed.value(),
                "a whole module is observed against the elaboration it ships, and not against a"
                        + " second one equal to it");
    }

    /**
     * A refused body leaves nothing to ship and leaves the bodies that may be run.
     *
     * <p>Which bodies those are is {@link Bodies.RunnableBehaviors}'s answer, and that this
     * elaboration holds exactly them is what makes it the emission: what it does not hold is what
     * the backend has no body here to emit.
     */
    @Test
    void aRefusedBodyLeavesNoModuleToShipAndTheBodiesThatMayBeRun() {
        Compilation refused = compile("0");

        assertFalse(refused.db().ask(new Bodies.Checked("demo")).present(),
                "a module one of whose bodies did not come out has no whole to ship");
        assertFalse(refused.db().ask(new Output.Classes("demo")).present(),
                "and nothing to publish either");
        Answer<Bodies.Elaborated> observed = refused.db().ask(new Bodies.Observable("demo"));
        assertTrue(observed.present(), "and the bodies that came out are still here");
        assertEquals(Set.of("apart"), observed.value().behaviorBodies().keySet());
    }

    /**
     * And what is emitted for it declares every behavior the module declares.
     *
     * <p>What a partial image leaves out is an implementation and never a declaration. A behavior
     * whose body may not be run is still one this module declares, and an image that dropped the
     * declaration with the body would be a program whose shape moves with what happened to check.
     */
    @Test
    void thePartialImageDeclaresEveryBehaviorAndImplementsOnlyWhatMayBeRun() {
        Compilation refused = compile("0");

        Answer<EvaluationArtifact> run =
                refused.db().ask(new Output.Evaluated("demo", ArmObservation.RECORD));
        assertTrue(run.present(), "a module with a body left out is still one a row can be run in");
        Set<String> classes = run.value().classes().keySet();

        for (String behavior : List.of("apart", "onwards", "thrice", "twice", "mint")) {
            assertTrue(classes.contains(declarationOf(behavior)),
                    () -> "`" + behavior + "` is declared by this module and its declaration is"
                            + " not in " + classes);
        }
        assertTrue(classes.contains(implementationOf("apart")),
                () -> "`apart` may be run and nothing implements it: " + classes);
        // `onwards` among them, and it is the one a map of bodies could not have answered for: it
        // has no body, and it applies `thrice` by constructing what this image does not hold.
        for (String behavior : List.of("onwards", "thrice", "twice", "mint")) {
            assertFalse(classes.contains(implementationOf(behavior)),
                    () -> "`" + behavior + "` may not be run and something implements it: "
                            + classes);
        }
    }

    /**
     * And a row about one of them is undecided, saying that this compile made no implementation.
     *
     * <p>The whole of the way through, from what the emission left out to what a person is told
     * about the row. Held at the row rather than at any step of it: every step between is a value
     * this test could have built, and what has to hold is that a model reaches the end of them.
     *
     * <p>Not pending, which is the answer for a behavior nothing implements. A row that says it
     * waits sends an author looking for a stand-in nobody owes it.
     */
    @Test
    void aRowOfAnImplementationThatWasNotMadeIsUndecidedAndSaysWhy() {
        Compilation refused = compile("0");

        Output.RowsRead.Of read = refused.db().ask(new Output.RowsRead("demo")).value();
        List<RowOutcome> ran = new java.util.ArrayList<>(read.byBehavior().get("twice").ran());

        assertEquals(1, ran.size(), () -> "the row written for `twice` is what this reads: " + ran);
        RowOutcome row = ran.getFirst();
        assertEquals(Disposition.INCOMPLETE, row.disposition(),
                () -> "nothing was found out about this row: " + row);
        assertEquals(FailurePhase.IMPLEMENTATION_NOT_MADE, row.failurePhase(),
                () -> "and what stopped it is this compile having made no implementation: " + row);
    }

    /** Asked of the ABI rather than spelled here, so this reads the names that were emitted. */
    private static String declarationOf(String behavior) {
        return SoutherJvmAbi.nameOf(
                new GeneratedClass.BehaviorInterface("demo", behavior)).binaryName();
    }

    private static String implementationOf(String behavior) {
        return SoutherJvmAbi.nameOf(
                new GeneratedClass.BehaviorImpl("demo", behavior)).binaryName();
    }

    private static Compilation compile(String constructs) {
        Compilation compilation =
                Compilation.ofSources(List.of(MODEL.formatted(constructs)), ModulePath.EMPTY);
        compilation.answerEverything();
        return compilation;
    }
}
