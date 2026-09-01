package souther.program.api;

import souther.compiler.Compiler;
import souther.compiler.core.Composition;
import souther.compiler.core.Core;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.meta.ModulePath;
import souther.compiler.program.BehaviorTarget;
import souther.compiler.program.CheckedBehavior;
import souther.compiler.program.CheckedHelper;
import souther.compiler.program.CheckedImplementation;
import souther.compiler.program.CheckedModule;
import souther.compiler.program.CheckedProgram;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A call reaches a behavior, and the program says what that behavior takes, what it answers, and
 * where its implementation comes from — whichever module declares it.
 *
 * <p>Two modules compiled together do not say this. Both are among what the snapshot is taken of,
 * so a reader that could only get to a behavior through its module would still find every callee it
 * looked for. A module declared only on the path is what says a call carries an identity and the
 * program answers for it: that module is not emitted here, and the behavior is called all the same.
 */
class ACallReachesTheBehaviorItsProgramDeclaresTest {

    /**
     * Published by another project: a behavior it implements, one it leaves to Java, and one
     * nothing below names.
     */
    private static final String PUBLISHED = """
            module lib.rates exposing ( Rate, spin, rateFor, tally, unused )
            data Rate = Int

            behavior spin : (of: Int) -> Rate
            let spin (of) = Rate(of)

            behavior rateFor : (of: Int) -> Rate

            behavior tally : (r: Rate) -> Int
            let tally (r) = r.value

            behavior unused : (r: Rate) -> Int
            let unused (r) = r.value
            """;

    /**
     * And it is called from each of the two places a call to a behavior stands: a behavior's body,
     * and the stages a composed behavior applies. A carried helper is here as well, for the check
     * that it is not a third.
     */
    private static final String USES = """
            module app.uses
            import lib.rates ( Rate, spin, rateFor, tally )

            behavior rateOf : (base: Int) -> Rate
                depends on rateFor
            let rateOf (base, rateFor) = rateFor(base)

            behavior spun : (base: Int) -> Rate
            let spun (base) = spin(base)

            behavior counted = spun >-> tally

            behavior looped : (base: Int) -> Rate
            let looped (base) = spinning(base)

            partial let spinning (n: Int): Rate = spinning(n)

            fake rateFor
                | (1) -> Rate(10)
                | _ -> Rate(99)

            example rateOf
                | "the table lists it" : (1) -> Rate(10)
            """;

    private static final ValueName.Behavior SPIN = new ValueName.Behavior("lib.rates", "spin");
    private static final ValueName.Behavior RATE_FOR = new ValueName.Behavior("lib.rates",
            "rateFor");
    private static final ValueName.Behavior TALLY = new ValueName.Behavior("lib.rates", "tally");
    private static final ValueName.Behavior UNUSED = new ValueName.Behavior("lib.rates", "unused");
    private static final Type RATE = Type.ref(TypeSymbols.declared(new TypeKey("lib.rates",
            "Rate")));

    /**
     * What a body carries at a call is answered for, every call of it.
     *
     * <p>The walk is over what the program hands over rather than over the calls this test wrote:
     * a check made by naming the callees expected would be right about the ones it thought to name,
     * and a snapshot that dropped a callee written somewhere else would keep passing it.
     */
    @Test
    void everyBehaviorACallReachesIsAnsweredForByTheProgram() {
        CheckedProgram program = compiled();

        Set<ValueName.Behavior> reached = everyBehaviorCalledIn(program);

        assertFalse(reached.isEmpty(), "the walk found no call to a behavior at all");
        for (ValueName.Behavior called : reached) {
            assertInstanceOf(BehaviorTarget.class, program.behavior(called),
                    () -> "a body calls `" + called + "` and the program answers nothing for it");
        }
        assertEquals(Set.of(SPIN, RATE_FOR, TALLY, new ValueName.Behavior("app.uses", "spun")),
                reached, "and the calls the walk found are the ones these modules write: a body's,"
                        + " and a composition's stages");
    }

    /**
     * And a carried helper reaches no behavior, which is why the walk above does not go through
     * one.
     *
     * <p>The language refuses a call to a behavior from a helper's {@code let} (E1818), so the
     * places a call to a behavior stands are a behavior's own body and a composition's stages. Said
     * here as a check rather than left as a walk of the helpers that can only ever find nothing:
     * such a walk answers the same whether the rule holds or the module has no helper, and the day
     * the rule moved it would be a walk nobody had noticed had started mattering.
     */
    @Test
    void aCarriedHelperReachesNoBehavior() {
        CheckedModule uses = compiled().module("app.uses");

        assertFalse(uses.helpers().isEmpty(), "the module carries a helper to ask about");
        for (CheckedHelper helper : uses.helpers()) {
            Set<ValueName.Behavior> reached = new LinkedHashSet<>();
            collectCalled(helper.body(), reached);
            assertEquals(Set.of(), reached, () -> "`" + helper + "` calls a behavior");
        }
    }

    /**
     * A call to a behavior a module on the path implements reaches an implementation this program
     * does not hold.
     *
     * <p>Which is what an output emitting the call needs to know it may emit a call at all: the
     * implementation exists, and emitting one of its own under the same name would be a second
     * definition of one behavior.
     */
    @Test
    void whatACallToABehaviorOnThePathReachesIsWhatItWasDeclaredToBe() {
        BehaviorTarget spin = compiled().behavior(SPIN);

        assertEquals(List.of(Type.INT), spin.signature().takes());
        assertEquals(RATE, spin.signature().answers());
        assertInstanceOf(CheckedImplementation.ImplementedElsewhere.class, spin.implementation(),
                "the build that published `lib.rates` emitted its body");
    }

    /** And one that module leaves to Java is injected here, as it is where it was declared: what
     *  it does is not in either program, and a crossing into what is emitted here reaches it. */
    @Test
    void aBehaviorThePathLeavesToJavaIsInjected() {
        BehaviorTarget rateFor = compiled().behavior(RATE_FOR);

        assertEquals(List.of(Type.INT), rateFor.signature().takes());
        assertInstanceOf(CheckedImplementation.Injected.class, rateFor.implementation());
    }

    /**
     * And a behavior of that module nothing here names is answered for too.
     *
     * <p>What the program answers for is what the modules it read declare, and not what a walk of
     * its bodies happened to reach. Cut down to the calls that were made, the snapshot would be a
     * walk an output has to trust and repeat, and the day an output emitted a call this one did not
     * make there would be nothing to ask.
     */
    @Test
    void aBehaviorNothingHereNamesIsAnsweredForAllTheSame() {
        BehaviorTarget unused = compiled().behavior(UNUSED);

        assertEquals(List.of(RATE), unused.signature().takes());
        assertEquals(Type.INT, unused.signature().answers());
        assertInstanceOf(CheckedImplementation.ImplementedElsewhere.class, unused.implementation());
    }

    /**
     * A behavior of a checked module is one boundary, whichever way it is reached.
     *
     * <p>The same value and not an equal one. Two readings of what a behavior takes would agree the
     * day they were made and drift the day either was made from something else, and a program
     * holding one fact cannot drift.
     */
    @Test
    void aBehaviorOfACheckedModuleIsOneBoundaryReachedTwoWays() {
        CheckedProgram program = compiled();
        ValueName.Behavior spun = new ValueName.Behavior("app.uses", "spun");

        CheckedBehavior emitted = program.module("app.uses").behavior(spun);

        assertSame(emitted.signature(), program.behavior(spun).signature());
        assertSame(emitted.implementation(), program.behavior(spun).implementation());
    }

    /** And the module that declares the called behavior is still not something this program
     *  emits. */
    @Test
    void theModuleThatDeclaresItIsNotAmongTheModulesEmitted() {
        assertEquals(List.of("app.uses"), compiled().modules().stream()
                .map(CheckedModule::name).toList());
    }

    /**
     * An identity no module this compile read declares is a mistake at the reader.
     *
     * <p>{@link ValueName.Behavior} is public, so an address can be assembled out of two strings.
     * Answered with an absence it would read as a program in which the behavior is not implemented.
     */
    @Test
    void anIdentityNoModuleDeclaresIsRefused() {
        CheckedProgram program = compiled();

        assertThrows(IllegalArgumentException.class,
                () -> program.behavior(new ValueName.Behavior("lib.rates", "nobodyWroteThis")));
        assertThrows(IllegalArgumentException.class,
                () -> program.behavior(new ValueName.Behavior("no.module", "spin")));
    }

    /** And a module is not asked about a behavior of another one. What only this compile knows
     *  about a behavior — what its examples said — is what a module answers, and a behavior it does
     *  not declare is one it has none of rather than one that does not exist. */
    @Test
    void aModuleIsNotAskedAboutABehaviorItDoesNotDeclare() {
        CheckedModule uses = compiled().module("app.uses");

        assertThrows(IllegalArgumentException.class, () -> uses.behavior(SPIN));
    }

    private static CheckedProgram compiled() {
        Map<String, ClassFileImage> published = Compiler.compile(PUBLISHED);
        return CheckedProgram.of(List.of(USES), ModulePath.of(published));
    }

    /**
     * Every behavior a call in this program reaches: from the bodies of its behaviors, and from the
     * stages a composed behavior applies.
     *
     * <p>Both are a place a callee is named, and a walk that visited one of them would answer that
     * everything it found was answered for. A carried helper is not a third: the language refuses a
     * call to a behavior from a helper's {@code let} (E1818), which
     * {@link #aCarriedHelperReachesNoBehavior} is what says here rather than a walk that goes
     * looking and can find nothing.
     *
     * <p>The switch has no {@code default}, so a state an implementation is in that this has
     * nothing to say about stops this compiling rather than being walked past.
     */
    private static Set<ValueName.Behavior> everyBehaviorCalledIn(CheckedProgram program) {
        Set<ValueName.Behavior> reached = new LinkedHashSet<>();
        for (CheckedModule module : program.modules()) {
            for (CheckedBehavior behavior : module.behaviors()) {
                switch (behavior.implementation()) {
                    case CheckedImplementation.Body body -> collectCalled(body.body(), reached);
                    case CheckedImplementation.Composed(Composition composition) -> {
                        for (Composition.Stage stage : composition.stages()) {
                            reached.add(stage.behavior());
                        }
                    }
                    case CheckedImplementation.Injected ignored -> { }
                    case CheckedImplementation.Unwritten ignored -> { }
                    case CheckedImplementation.ImplementedElsewhere ignored -> { }
                }
            }
        }
        return reached;
    }

    private static void collectCalled(Core node, Set<ValueName.Behavior> into) {
        if (node instanceof Core.Call call
                && call.fn() instanceof Core.Reached.OfDeclaration declared
                && declared.reaches() instanceof Core.Reaches.ABehavior(ValueName.Behavior behavior)) {
            into.add(behavior);
        }
        Core.forEachChild(node, child -> collectCalled(child, into));
    }
}
