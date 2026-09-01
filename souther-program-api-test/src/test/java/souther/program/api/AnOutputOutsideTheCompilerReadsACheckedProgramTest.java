package souther.program.api;

import souther.compiler.Compiler;
import souther.compiler.core.Composition;
import souther.compiler.diag.CompileException;
import souther.compiler.core.Core;
import souther.compiler.core.Kernel;
import souther.compiler.core.KernelSignature;
import souther.compiler.program.CheckedBehavior;
import souther.compiler.program.CheckedData;
import souther.compiler.program.CheckedHelper;
import souther.compiler.program.CheckedImplementation;
import souther.compiler.program.CheckedModule;
import souther.compiler.program.CheckedProgram;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.fail;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What an output that is not this compiler can do with a checked Souther program.
 *
 * <p>This artifact depends on {@code souther-compiler} and on nothing else of the project, which is
 * the position a WebAssembly compiler or any other output would be in. Everything below is written
 * with what such an artifact can name: no query, no code generation, no syntax tree. What it needs
 * is decisions the language compiler made, and this is a reading of them.
 */
class AnOutputOutsideTheCompilerReadsACheckedProgramTest {

    private static final String MODULE = """
            module demo

            data Name = String
            data Employee = { boss: Employee?, name: Name }
            data Depth = Int
            data Deep = { depth: Int }

            // Java supplies this one (spec §injected-behavior)
            behavior loadEmployee : (name: Name) -> Employee

            // Walking the reporting line is a recursion no fold expresses, so this helper stays a
            // definition of its own rather than being expanded where it is used.
            let depth (e: Employee): Int =
                match e.boss with
                    | Some b -> depth(b) + 1
                    | None -> 1

            behavior measureDepth : (e: Employee) -> Depth constructs Depth

            let measureDepth (e) = Depth(depth(e))

            behavior toDeep : (d: Depth) -> Deep constructs Deep

            let toDeep (d) = Deep { depth = d.value }

            behavior measure = measureDepth >-> toDeep
            """;


    /**
     * A composition where a case leaves the main line: {@code classify} answers a {@code Domestic}
     * or an {@code Overseas}, and {@code priceIt} takes only the first.
     */
    private static final String ROUTED = """
            module demo

            data Order    = { total: Int }
            data Domestic = { total: Int }
            data Overseas = { total: Int }
            data Priced   = { total: Int }
            data Shipped  = { total: Int }

            behavior classify : (o: Order) -> Domestic | Overseas
                constructs Domestic, Overseas

            let classify (o) = {
                guard o.total <= 100 else Overseas { total = o.total }
                Domestic { total = o.total }
            }

            behavior priceIt : (d: Domestic) -> Priced constructs Priced

            let priceIt (d) = Priced { total = d.total }

            behavior shipIt : (p: Priced) -> Shipped constructs Shipped

            let shipIt (p) = Shipped { total = p.total }

            behavior process = classify >-> priceIt >-> shipIt
            """;

    /**
     * A body that reaches the standard library two ways: an operation applied to arguments, and one
     * written on its own.
     *
     * <p>{@code Map.empty} is declared with no parameter list, so it is a value and reaches the
     * checker by a route of its own rather than as an application. It is a kernel all the same, and
     * a reader outside this compiler has no way to tell which route a call was built by.
     *
     * <p>{@code List.map} is not among them and is not missing. The derivable layer is ordinary
     * Souther over the kernels and expands where it is called (ADR-0028), so what a backend meets is
     * the walk it became.
     */
    private static final String CALLS_THE_LIBRARY = """
            module demo

            data Tidied = { label: String, items: Int }

            behavior tidy : (label: String, items: List<Int>) -> Tidied constructs Tidied

            let tidy (label, items) =
                Tidied { label = String.trim(label), items = List.length(items) }

            behavior counts : (label: String) -> Map<String, Int>

            let counts (label) = Map.insert(label, String.length(label), Map.empty)
            """;

    /**
     * A call whose argument arrives narrower than the parameter it goes into.
     *
     * <p>{@code round} declares its second parameter {@code RoundingMode}, a sum the language
     * itself gives; {@code HALF_UP} is one of its cases, so the type at the call is the case and
     * the type in the declaration is the sum.
     */
    private static final String ROUNDS = """
            module demo

            data Rate = { value: Decimal }

            behavior toCents : (r: Rate) -> Decimal

            let toCents (r) = Decimal.round(2, HALF_UP, r.value)
            """;

    private static CheckedModule demo() {
        CheckedProgram program = CheckedProgram.of(List.of(MODULE));
        CheckedModule module = program.module("demo");
        assertNotNull(module, "the compile checked this module");
        return module;
    }

    private static CheckedBehavior named(CheckedModule module, String name) {
        CheckedBehavior behavior = module.behavior(new ValueName.Behavior(module.name(), name));
        assertNotNull(behavior, name);
        return behavior;
    }

    @Test
    void theProgramHoldsTheModulesItChecked() {
        CheckedProgram program = CheckedProgram.of(List.of(MODULE));

        assertEquals(List.of("demo"), program.modules().stream().map(CheckedModule::name).toList());
    }

    @Test
    void aBehaviorIsReachedByItsResolvedNameAndSaysWhatItTakesAndAnswers() {
        CheckedBehavior measureDepth = named(demo(), "measureDepth");

        assertEquals(new ValueName.Behavior("demo", "measureDepth"), measureDepth.name());
        assertEquals(1, measureDepth.signature().takes().size(),
                "one input, as it was declared");
        assertNotNull(measureDepth.signature().answers());
    }

    /**
     * The states an implementation is in, told apart by asking rather than by finding nothing where
     * a body would be.
     *
     * <p>The switch has no {@code default}: a state added later stops this compiling, which is what
     * a consumer outside the compiler wants from a set it is meant to handle all of. The behaviors
     * asked here are this compile's own, and one implemented by another compile is a behavior of a
     * module this program does not emit —
     * {@code ACallReachesTheBehaviorItsProgramDeclaresTest} asks that one.
     */
    @Test
    void whereAnImplementationComesFromIsAskedAndNotInferredFromAnAbsence() {
        CheckedModule demo = demo();

        assertEquals("body", where(named(demo, "measureDepth")));
        assertEquals("injected", where(named(demo, "loadEmployee")));
        assertEquals("composed", where(named(demo, "measure")));
    }

    private static String where(CheckedBehavior behavior) {
        return switch (behavior.implementation()) {
            case CheckedImplementation.Body body -> {
                assertNotNull(body.body().type(), "the checker typed it");
                yield "body";
            }
            case CheckedImplementation.Composed composed -> {
                assertFalse(composed.composition().stages().isEmpty());
                yield "composed";
            }
            case CheckedImplementation.Injected ignored -> "injected";
            case CheckedImplementation.Unwritten ignored -> "unwritten";
            // Every behavior asked here is one this compile checked, and an implementation another
            // compile emitted belongs to a module this program does not hold. Answered with a word
            // of its own it would be a state this test reads as covered and never sees.
            case CheckedImplementation.ImplementedElsewhere ignored ->
                    fail("`" + behavior.name() + "` is a behavior of a checked module and its"
                            + " implementation is another compile's");
        };
    }

    /**
     * A composition arrives routed.
     *
     * <p>Which cases a stage is offered is what makes {@code >->} Railway (spec §type-routing), and
     * it is the language's answer rather than each output's. An output reads it here instead of
     * working it out from the stages' signatures, which is what the JVM emitter used to do.
     */
    @Test
    void aCompositionSaysWhatEachStageIsOfferedAndWhatItAnswers() {
        CheckedImplementation implementation = named(demo(), "measure").implementation();
        assertTrue(implementation instanceof CheckedImplementation.Composed);
        Composition composed = ((CheckedImplementation.Composed) implementation).composition();

        assertEquals(List.of(new ValueName.Behavior("demo", "measureDepth"),
                        new ValueName.Behavior("demo", "toDeep")),
                composed.stages().stream().map(Composition.Stage::behavior).toList());
        // the first stage takes the composition's own arguments, so nothing is routed into it
        assertTrue(composed.stages().get(0).routing() instanceof Composition.Routing.Always);
        assertNotNull(composed.answers());
        for (Composition.Stage stage : composed.stages()) {
            assertNotNull(stage.answers(), "what the stage answers is on the stage");
        }
    }

    /**
     * A program the language refuses is not one of these, whatever the checker made of it.
     *
     * <p>In Souther a row that disagrees is a compile error, so a model whose {@code example} does
     * not hold is a model that did not compile. Every body in this one types; the checker has
     * nothing against it; and it is refused all the same. Answering with a snapshot here would put
     * an output on the far side of a gate the JVM build stops at — one output shipping an artifact
     * for a program the other refuses to build, with nothing to say which of them is right.
     */
    @Test
    void aProgramWhoseRowDoesNotHoldIsRefusedHereToo() {
        assertThrows(CompileException.class, () -> CheckedProgram.of(List.of(WRONG_ROW)),
                "the checker typed every body of it");

        // and the batch compiler refuses it for the same reason, which is the point
        assertThrows(CompileException.class, () -> Compiler.compile(WRONG_ROW));
    }

    /**
     * And so is a program the JVM cannot emit, which is a program of a different kind.
     *
     * <p>Where the row above is refused by the language, this one is refused by the machine: a JVM
     * constructor takes at most 254 argument slots and an {@code Int} is carried as a {@code long},
     * so a record of 128 of them turns into a class no JVM would load. What this holds is the
     * boundary rather than the diagnostic — the same declaration crosses at 127 fields and is
     * refused at 128, and an output reading a checked program is told which rule stopped it.
     *
     * <p>Refused all the same, and this is the decision rather than an accident of the order things
     * happen in (ADR-0115): a checked program is reachable only through a compile that emits one for
     * the JVM, so what an output outside this compiler may be handed is bounded by what the JVM can
     * hold. A snapshot for a program the JVM build stops at would be an artifact shipped for
     * something no other reading of the same program agrees is buildable.
     *
     * <p>Which rule the width comes from is ADR-0115's to state and not this test's to demonstrate:
     * two widths would pass the same way against a language that had a width rule of its own.
     */
    @Test
    void aProgramTheJvmCannotEmitIsRefusedHereToo() {
        CheckedProgram narrower = CheckedProgram.of(List.of(wideData(127)));
        assertEquals(127, ((CheckedData.Product) narrower.module("demo").data().get(0))
                .fields().size(), "a record this wide crosses the boundary");

        CompileException refused = assertThrows(CompileException.class,
                () -> CheckedProgram.of(List.of(wideData(128))));

        assertEquals("E2101", refused.code(), refused.getMessage());
        assertTrue(refused.getMessage().contains("JVM parameter slots"),
                "the refusal names whose rule it is: " + refused.getMessage());
    }

    /** A record of {@code fields} {@code Int} fields, and a behavior so the module has one. */
    private static String wideData(int fields) {
        StringBuilder declared = new StringBuilder("module demo\n\ndata Wide = { ");
        for (int i = 0; i < fields; i++) {
            declared.append(i == 0 ? "" : ", ").append("f").append(i).append(": Int");
        }
        return declared.append(" }\n\nbehavior keep : (w: Wide) -> Wide\n\nlet keep (w) = w\n")
                .toString();
    }

    private static final String WRONG_ROW = """
            module demo

            data Amount = Int

            behavior double : (a: Amount) -> Amount constructs Amount

            let double (a) = Amount(a.value * 2)

            example double
                | "twice" : (Amount(2)) -> Amount(5)
            """;

    /**
     * Which cases a stage is offered, and which have left the main line.
     *
     * <p>The value this boundary was widened for. A composition routes by case (spec
     * §type-routing): a stage runs where the running value is one it accepts, and anything else is
     * answered with rather than offered onward. An output that emitted the stages in order and
     * applied each to whatever arrived would compile this model into a different program, and the
     * stage list alone would not say so.
     */
    @Test
    void aStageIsOfferedTheCasesItAcceptsAndTheRestHaveLeftTheMainLine() {
        CheckedModule demo = CheckedProgram.of(List.of(ROUTED)).module("demo");
        Composition composed = ((CheckedImplementation.Composed)
                named(demo, "process").implementation()).composition();

        assertEquals(List.of(new ValueName.Behavior("demo", "classify"),
                        new ValueName.Behavior("demo", "priceIt"),
                        new ValueName.Behavior("demo", "shipIt")),
                composed.stages().stream().map(Composition.Stage::behavior).toList());

        // the first stage takes the composition's own argument, so nothing is routed into it
        assertTrue(composed.stages().get(0).routing() instanceof Composition.Routing.Always);

        // `priceIt` takes a Domestic and nothing else, so an Overseas has left the main line here
        assertEquals(List.of("Domestic"), acceptedBy(composed.stages().get(1)),
                "the cases this stage is offered");

        // and it stays off it: what follows is not offered the case `priceIt` was never given
        assertFalse(acceptedBy(composed.stages().get(2)).contains("Overseas"),
                "a case that left the main line is not offered to what follows");

        // the composition still answers with it, which is what leaving the main line means
        assertTrue(answeredCases(composed).contains("Overseas"),
                "what the composition answers: " + composed.answers());
    }

    /** The cases {@code stage} is offered, by name. */
    private static List<String> acceptedBy(Composition.Stage stage) {
        assertInstanceOf(Composition.Routing.OnCases.class, stage.routing(),
                "a running value that carries cases is routed by them");
        return ((Composition.Routing.OnCases) stage.routing()).accepted().stream()
                .map(TypeSymbol::name).toList();
    }

    /** The cases the composition itself answers with, by name. */
    private static List<String> answeredCases(Composition composed) {
        Type answers = composed.answers();
        assertInstanceOf(Type.Union.class, answers, "a composition that drops a case answers a sum");
        return ((Type.Union) answers).members().stream().map(TypeSymbol::name).sorted().toList();
    }

    /**
     * A body's parameter reads resolve to the parameters the snapshot says it has.
     *
     * <p>What a helper's body already allowed. A read carries the binding it was answered with, and
     * until now nothing said which parameter that binding was: an output emitting {@code $sum}
     * could see the read and not know which of its locals it names.
     *
     * <p>An equality and not the absence of an unresolved read. {@code combine}'s body binds
     * nothing of its own, so every read in it is a parameter read, and a body whose reads all
     * resolved because it had none would answer the same as this one.
     */
    @Test
    void everyParameterReadInABodyResolvesToAParameter() {
        CheckedModule demo = CheckedProgram.of(List.of(TAKES_TWO)).module("demo");
        CheckedBehavior combine = named(demo, "combine");
        CheckedImplementation.Body body =
                (CheckedImplementation.Body) combine.implementation();

        assertEquals(2, body.parameters().size(), "as many bindings as it takes");
        assertEquals(combine.signature().takes().size(), body.parameters().size(),
                "so the ith input is parameters().get(i) and takes().get(i)");
        assertEquals(body.parameters().stream().map(Core.Binder::binding)
                        .collect(Collectors.toSet()),
                readsIn(body.body()),
                "every read in this body is a read of one of them");
        assertFalse(readsIn(body.body()).isEmpty(), "and it reads them");
    }

    /**
     * And in the order the signature is in.
     *
     * <p>A set would answer the same for a list assembled backwards, and the two inputs of
     * {@code combine} are both {@code Int}s — so a reader zipping the binders with
     * {@code takes()} would be handed the wrong local with nothing to say so.
     */
    @Test
    void theBindersAreInTheOrderTheInputsWereDeclared() {
        CheckedBehavior combine =
                named(CheckedProgram.of(List.of(TAKES_TWO)).module("demo"), "combine");
        CheckedImplementation.Body body = (CheckedImplementation.Body) combine.implementation();

        assertEquals(List.of("first", "second"),
                body.parameters().stream().map(Core.Binder::name).toList(),
                "the definition's parameters, in the order it wrote them");
        // and the body's first read is the first parameter: `first.value - second.value`
        assertEquals(body.parameters().get(0).binding(), firstReadIn(body.body()).binding());
    }

    private static final String TAKES_TWO = """
            module demo

            data Amount = Int
            data Gap    = { gap: Int }

            behavior combine : (first: Amount, second: Amount) -> Gap constructs Gap

            let combine (first, second) = Gap { gap = first.value - second.value }
            """;

    /**
     * An injected dependency is not one of these.
     *
     * <p>The definition implementing a behavior takes its declared inputs and then the behaviors it
     * depends on, and only the first are what a call supplies. A snapshot handing over the whole
     * parameter list would put a dependency at an index the signature has no type for, and
     * {@code takes()} would go on saying the behavior takes one.
     */
    @Test
    void aBehaviorsInjectedDependenciesAreNotAmongItsParameters() {
        CheckedModule demo = CheckedProgram.of(List.of(DEPENDS_ON)).module("demo");
        CheckedBehavior report = named(demo, "report");
        CheckedImplementation.Body body = (CheckedImplementation.Body) report.implementation();

        assertEquals(1, report.signature().takes().size(), "one input, as it was declared");
        assertEquals(List.of("amount"), body.parameters().stream().map(Core.Binder::name).toList(),
                "the input, and not the behavior it depends on");
        assertEquals(body.parameters().stream().map(Core.Binder::binding)
                        .collect(Collectors.toSet()),
                readsIn(body.body()),
                "the dependency is reached by name, so nothing in the body reads it as a binding");
    }

    private static final String DEPENDS_ON = """
            module demo

            data Amount = Int
            data Line   = { line: String }

            behavior render : (a: Amount) -> Line constructs Line

            behavior report : (amount: Amount) -> Line
                depends on render

            let report (amount, render) = render(amount)
            """;

    /** The binding of every {@code Core.Read} in {@code body}. */
    private static Set<BindingId> readsIn(Core body) {
        Set<BindingId> read = new LinkedHashSet<>();
        for (Core node : everyNodeOf(body)) {
            if (node instanceof Core.Read r) {
                read.add(r.binding());
            }
        }
        return read;
    }

    /** The first read the walk reaches, which for a body of one expression is its leftmost. */
    private static Core.Read firstReadIn(Core body) {
        for (Core node : everyNodeOf(body)) {
            if (node instanceof Core.Read r) {
                return r;
            }
        }
        throw new AssertionError("this body reads a parameter");
    }

    /**
     * A call in a body reaches a helper, and the helper is here to be walked.
     *
     * <p>The half a set of behaviors alone would miss. Most helpers are gone by the time a module is
     * checked; the one that is left is a recursion, and a body's call names it. An output handed
     * only the behaviors would find that call reaching something it had never been given.
     */
    @Test
    void aCallReachesAHelperTheProgramHoldsAndItsBodyIsWalkedToo() {
        CheckedModule demo = demo();
        Core body = ((CheckedImplementation.Body) named(demo, "measureDepth").implementation())
                .body();

        Set<ValueName.Helper> called = helpersCalledIn(body);
        assertEquals(Set.of(new ValueName.Helper("demo", "depth")), called,
                "the recursive helper the body calls");

        CheckedHelper depth = demo.helper(new ValueName.Helper("demo", "depth"));
        assertNotNull(depth, "and the program holds it");
        assertEquals(1, depth.parameters().size());
        assertNotNull(depth.parameters().get(0).binder().binding(), "the binding its body reads");
        assertNotNull(depth.body().type(), "what it answers, as the checker typed it");
        assertTrue(helpersCalledIn(depth.body()).contains(new ValueName.Helper("demo", "depth")),
                "and it calls itself, which is why it is a definition of its own");
    }

    /**
     * And a call reaching a kernel of the standard library says which kernel.
     *
     * <p>The operation, not a spelling of it. What is on the other side of {@code String.trim} is a
     * decision the language made, and an output that read the alias and the name back apart would be
     * resolving, by spelling, a name this compiler had resolved already.
     *
     * <p>Reached all the same, which is the shape of it: the same node still says what name the
     * module wrote and what that name denotes, so a reader with no business emitting the operation
     * asks what it always asked.
     */
    @Test
    void aCallReachingAKernelSaysWhichKernel() {
        CheckedProgram program = CheckedProgram.of(List.of(CALLS_THE_LIBRARY));
        Core body = ((CheckedImplementation.Body)
                named(program.module("demo"), "tidy").implementation()).body();

        Set<Kernel> reached = new LinkedHashSet<>();
        Set<String> named = new LinkedHashSet<>();
        for (Core node : everyNodeOf(body)) {
            if (node instanceof Core.Call call
                    && call.fn() instanceof Core.Reached.OfKernel kernel) {
                reached.add(kernel.kernel());
                named.add(kernel.rendered());
                assertInstanceOf(ValueName.Stdlib.class, kernel.denotes(),
                        "what " + kernel.rendered() + " denotes");
            }
        }

        assertEquals(Set.of(Kernel.STRING_TRIM, Kernel.LIST_LENGTH), reached,
                "the kernels this body reaches, as the operations they are");
        assertEquals(Set.of("String.trim", "List.length"), named,
                "and the same nodes still say what name the module wrote");
    }

    /**
     * And so does one written where a value goes rather than applied.
     *
     * <p>{@code Map.empty} takes no arguments, so it is not written as an application and is not
     * built as one. Two routes reach a call to a name, and a rule kept by each of them is a rule one
     * of them will be missing: what a body holds is the same node either way, and an output reading
     * it cannot tell — and must not have to tell — which route made it.
     */
    @Test
    void andSoDoesAKernelWrittenWhereAValueGoes() {
        CheckedProgram program = CheckedProgram.of(List.of(CALLS_THE_LIBRARY));
        Core body = ((CheckedImplementation.Body)
                named(program.module("demo"), "counts").implementation()).body();

        Set<Kernel> reached = new LinkedHashSet<>();
        for (Core node : everyNodeOf(body)) {
            if (node instanceof Core.Call call
                    && call.fn() instanceof Core.Reached.OfKernel kernel) {
                reached.add(kernel.kernel());
            }
        }

        assertTrue(reached.contains(Kernel.MAP_EMPTY),
                () -> "the empty map is a kernel here too, and this body reaches " + reached);
        assertEquals(Set.of(Kernel.MAP_INSERT, Kernel.STRING_LENGTH, Kernel.MAP_EMPTY), reached,
                "every kernel this body reaches, however it was written");
    }

    /**
     * And the program says what the kernel that call reaches was declared to take.
     *
     * <p>What the checker settled for each node is what arrived there. That answers the callee's
     * shape only while no value can arrive narrower than the parameter it goes into, and a
     * sum-typed parameter ends it: the argument here is a {@code HALF_UP} and the parameter is the
     * sum it is a case of. An output building a boundary form off the arguments would build one
     * naming the case, and find nothing declared that way.
     */
    @Test
    void andTheProgramSaysWhatThatKernelWasDeclaredToTake() {
        CheckedProgram program = CheckedProgram.of(List.of(ROUNDS));
        Core body = ((CheckedImplementation.Body)
                named(program.module("demo"), "toCents").implementation()).body();
        Core.Call rounds = null;
        for (Core node : everyNodeOf(body)) {
            if (node instanceof Core.Call call
                    && call.fn() instanceof Core.Reached.OfKernel kernel
                    && kernel.kernel() == Kernel.DECIMAL_ROUND) {
                rounds = call;
            }
        }
        assertNotNull(rounds, "the body reaches Decimal.round");

        KernelSignature declared = program.kernelSignature(Kernel.DECIMAL_ROUND);

        assertEquals(List.of("Int", "RoundingMode", "Decimal"),
                declared.parameters().stream().map(Type::show).toList(),
                "what the language declared the kernel to take");
        assertEquals("Decimal", Type.show(declared.result()),
                "and what it declared it answers");
        assertEquals("HALF_UP", Type.show(rounds.args().get(1).type()),
                "while what arrived at the sum-typed parameter is the case it is");
    }

    /**
     * And it says so for every kernel, not only the ones this program reaches.
     *
     * <p>Which kernels the language has is the language's answer. An output told only about the
     * ones some program happened to call would be one that could not emit the next program.
     */
    @Test
    void andItSaysSoForEveryKernelTheLanguageHas() {
        CheckedProgram program = CheckedProgram.of(List.of(ROUNDS));

        List<String> answered = new ArrayList<>();
        for (Kernel kernel : Kernel.values()) {
            // Refused rather than answered with an absence, so asking is the assertion.
            answered.add(Type.show(program.kernelSignature(kernel).result()));
        }

        assertEquals(Kernel.values().length, answered.size(),
                "every kernel the language has says what it answers");
    }

    /** Every helper a call in {@code body} reaches, walking every node of it. */
    private static Set<ValueName.Helper> helpersCalledIn(Core body) {
        Set<ValueName.Helper> called = new LinkedHashSet<>();
        for (Core node : everyNodeOf(body)) {
            if (node instanceof Core.Call call
                    && call.fn() instanceof Core.Reached reached
                    && reached.denotes() instanceof ValueName.Helper helper) {
                called.add(helper);
            }
        }
        return called;
    }

    private static List<Core> everyNodeOf(Core body) {
        List<Core> nodes = new ArrayList<>();
        collect(body, nodes);
        return nodes;
    }

    private static void collect(Core node, List<Core> into) {
        into.add(node);
        Core.forEachChild(node, child -> collect(child, into));
    }
}
