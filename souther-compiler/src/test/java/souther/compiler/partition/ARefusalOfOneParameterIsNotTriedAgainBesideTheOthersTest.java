package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.CheckSurface;
import souther.compiler.check.Prepared;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.Sig;
import souther.compiler.ast.Hir;
import souther.compiler.coverage.ArmProbe;
import souther.compiler.inputs.InputDomain;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Shapes;
import souther.compiler.reading.CoverageRead;
import souther.compiler.types.Type;

import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A parameter the model refuses is refused for what stands under it, and the positions of the
 * other parameters say nothing about it.
 *
 * <p>Each parameter is built on its own, so a search for a combination that has the first
 * parameter refused learns something about that parameter's classes and nothing about the rest.
 * Tried again for every way the other parameters' positions can be moved, the same refusal is
 * built once per assignment of theirs — a number that doubles with every field added beside it,
 * while what the model was asked stays the same.
 *
 * <p>So the same model is searched twice, once with three fields beside the refused parameter and
 * once with six, and asked how often the refused one was built. The answer is a fact about the
 * refused parameter and is the same both times.
 */
class ARefusalOfOneParameterIsNotTriedAgainBesideTheOthersTest {

    @Test
    void howOftenARefusedParameterIsBuiltDoesNotGrowWithTheFieldsBesideIt() {
        Searched three = searched(3);
        Searched six = searched(6);
        assertTrue(three.gateBuilt() > 0, "the refused parameter was built at all");
        assertEquals(three.gateBuilt(), six.gateBuilt(),
                "the refused parameter is built as often beside six fields as beside three");
    }

    @Test
    void whatTheSearchComesToIsTheSameHoweverManyFieldsAreBesideIt() {
        Searched three = searched(3);
        Searched six = searched(6);
        assertFalse(three.reasons().isEmpty(), "an arm was looked for and came to nothing");
        assertEquals(three.reasons(), six.reasons(),
                "and it came to the same thing beside six fields as beside three");
        assertTrue(three.reasons().contains(
                        Generator.UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED.name()),
                "which is that every candidate was refused: " + three.reasons());
    }

    /**
     * What is left out is the parameter at the classes it was refused at, and not the parameter.
     *
     * <p>The gate refused open and built shut. A row for a class of the first record moves the gate
     * from where the search first puts it — open, and refused — to shut, and only that row builds.
     * Left out by the parameter alone, the shut gate is never tried and no such row is offered; left
     * out by its classes, it is, beside six fields as beside three, with the open gate built as
     * often either way.
     *
     * <p>Asked of that field's classes alone. What a search learns is its own, so each class owed
     * builds the open gate for itself, and a model with more fields owes more classes.
     */
    @Test
    void aParameterRefusedAtSomeOfItsClassesIsStillBuiltAtTheOthers() {
        Offered three = offeredWithTheGateRefusedOpen(3);
        Offered six = offeredWithTheGateRefusedOpen(6);
        assertTrue(three.classes().contains("left.f0=On")
                        && three.classes().contains("left.f0=Off"),
                "a row is offered for each class of the first record's field, with the gate shut: "
                        + three.classes());
        assertEquals(three.classes(), six.classes(),
                "and the same beside six fields as beside three");
        assertTrue(three.openBuilt() > 0, "the open gate was built");
        assertEquals(three.openBuilt(), six.openBuilt(),
                "and built as often beside six fields as beside three");
    }

    private record Offered(int openBuilt, Set<String> classes) {}

    private static Offered offeredWithTheGateRefusedOpen(int fields) {
        Model model = Model.of(source(fields), "decide");
        AtomicInteger open = new AtomicInteger();
        Generator.CandidateCheck refusingAnOpenGate = (parameter, candidate) -> {
            if (parameter == 0 && candidate.text().contains("Open")) {
                open.incrementAndGet();
                return new Generator.CandidateCheck.Built.Refused("the gate is open");
            }
            return new Generator.CandidateCheck.Built.NothingBuiltIt();
        };
        List<ClassOfAPosition> owed = GenerationFixtures.everyClassNoRowSitsIn(model.subject(),
                List.of()).stream().filter(each -> each.at().term().equals("left.f0")).toList();
        assertEquals(2, owed.size(), "the first record's field is owed both its classes");
        FillResult filled = GenerationFixtures.fill(model.subject(), List.of(), refusingAnOpenGate,
                model.read(), Generator.Trial.NOTHING_RUNS, List.of(), owed, List.of(),
                Budgets.generation());
        Set<String> classes = new TreeSet<>();
        for (Generator.GeneratedRow row : filled.rows()) {
            for (Generator.Purpose purpose : row.purposes()) {
                if (purpose instanceof Generator.Purpose.ForAClass cls) {
                    classes.add(cls.label());
                }
            }
        }
        return new Offered(open.get(), classes);
    }

    /**
     * Beside forty fields apiece there are more ways to move the other parameters than any search
     * walks. What the refusal is about is settled by the combination, so it ends however many
     * there are.
     */
    @Test
    void aSearchBesideMoreFieldsThanItCouldWalkEnds() {
        Searched forty = assertTimeoutPreemptively(Duration.ofSeconds(60), () -> searched(40));
        assertEquals(searched(3).gateBuilt(), forty.gateBuilt(),
                "and builds the refused parameter as often as beside three");
    }

    /**
     * An origin that states one parameter writes it as its own value with the fields under it
     * moved, and a field two records down is not one it can write. Where a row is asked for at a
     * class of such a field the value does not have, there is nothing to write against that origin
     * whatever the other parameter's forty fields do — and the search goes on to compose from the
     * classes.
     */
    @Test
    void anOriginThatCannotWriteAParameterIsLeftHoweverManyFieldsAreBesideIt() {
        Set<String> forty = assertTimeoutPreemptively(Duration.ofSeconds(60),
                () -> besideTheOtherParameter(writtenAgainstAValueOfTheFirst(40)));
        Set<String> three = besideTheOtherParameter(writtenAgainstAValueOfTheFirst(3));
        assertTrue(three.contains("left.inner.g=Off"),
                "a row is composed for the class the stated value does not have: " + three);
        assertEquals(three, forty,
                "and the rows for the first parameter's classes and for the decisions together are"
                        + " the same beside forty fields as beside three");
    }

    /**
     * What the rows are for, less the classes of the second parameter's fields — of which there
     * are as many as it has fields.
     */
    private static Set<String> besideTheOtherParameter(List<Generator.GeneratedRow> rows) {
        Set<String> out = new TreeSet<>();
        for (Generator.GeneratedRow row : rows) {
            for (Generator.Purpose purpose : row.purposes()) {
                switch (purpose) {
                    case Generator.Purpose.ForAClass cls -> {
                        if (cls.label().startsWith("left.")) {
                            out.add(cls.label());
                        }
                    }
                    default -> out.add(purpose.toString());
                }
            }
        }
        return out;
    }

    private static List<Generator.GeneratedRow> writtenAgainstAValueOfTheFirst(int fields) {
        String source = """
                module example.nested

                data Flag = On | Off

                data Inner = { g: Flag }

                data Left = { inner: Inner }

                data Right = %s

                behavior decide : (left: Left, right: Right) -> Int

                let innerFee (f: Flag): Int =
                    match f with
                        | On -> 0
                        | Off -> 500

                let rightFee (f: Flag): Int =
                    match f with
                        | On -> 500
                        | Off -> 0

                let decide (left, right) =
                    innerFee(left.inner.g) + rightFee(right.f0)

                let usualLeft = Left { inner = Inner { g = On } }
                """.formatted(flags(fields));
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        CheckSurface surface = compilation.db().ask(new Shapes.CheckSurface(module)).value();
        assertNotNull(surface, "the module is assembled");
        Sig sig = compilation.db().ask(new Bodies.Signatures(module)).value().get("decide");
        assertNotNull(sig, "the behavior has a signature");
        Type.Ref left = assertInstanceOf(Type.Ref.class, sig.inputTypes().get(0));
        assertEquals(1, surface.typedFixtureValues().getOrDefault(left, List.of()).size(),
                "the module states one value of the first parameter, which rows are written against");
        Map<String, Adequacy.Filling> generated = Adequacy.generatedOf(compilation.db(), module);
        assertNotNull(generated, "the model compiles");
        return generated.get("decide").composed().rows();
    }

    private static String flags(int fields) {
        List<String> declared = new ArrayList<>();
        for (int i = 0; i < fields; i++) {
            declared.add("f" + i + ": Flag");
        }
        return "{ " + String.join(", ", declared) + " }";
    }

    private record Searched(int gateBuilt, Set<String> reasons) {}

    private static Searched searched(int fields) {
        Model model = Model.of(source(fields), "decide");
        AtomicInteger gate = new AtomicInteger();
        Generator.CandidateCheck refusingTheGate = (parameter, candidate) -> {
            if (parameter == 0) {
                gate.incrementAndGet();
                return new Generator.CandidateCheck.Built.Refused("the gate is shut");
            }
            return new Generator.CandidateCheck.Built.NothingBuiltIt();
        };
        Set<ArmProbe> arms = GenerationFixtures.everyArmACombinationMayTake(model.subject(),
                model.read().interactions(), Budgets.generation());
        assertFalse(arms.isEmpty(), "the two decisions meet on an arm");
        FillResult filled = GenerationFixtures.fill(model.subject(), List.of(), refusingTheGate,
                model.read(), Generator.Trial.NOTHING_RUNS, List.of(), List.of(),
                List.copyOf(arms), Budgets.generation());
        assertEquals(List.of(), filled.rows(), "nothing the gate refuses is a row");
        Set<String> reasons = new TreeSet<>();
        for (ArmDisposition each : GenerationFixtures.arms(filled.discharge()).values()) {
            ArmDisposition.Unresolved unresolved = assertInstanceOf(ArmDisposition.Unresolved.class,
                    each);
            for (CameToNothing why : unresolved.why()) {
                reasons.add(why.why().reason().name());
            }
        }
        return new Searched(gate.get(), reasons);
    }

    /** A gate the body decides on, and two records of {@code fields} flags beside it. */
    private static String source(int fields) {
        String record = flags(fields);
        return """
                module example.gate

                data Flag = On | Off

                data Gate = Open | Shut

                data Left = %s

                data Right = %s

                behavior decide : (gate: Gate, left: Left, right: Right) -> Int

                let gateFee (g: Gate): Int =
                    match g with
                        | Open -> 0
                        | Shut -> 500

                let flagFee (f: Flag): Int =
                    match f with
                        | On -> 500
                        | Off -> 0

                let decide (gate, left, right) =
                    gateFee(gate) + flagFee(left.f0)
                """.formatted(record, record);
    }

    private record Model(MeasuredInput subject, CoverageRead.Read read) {

        static Model of(String source, String behavior) {
            Compilation compilation = Compilation.ofSource(source, "Main");
            compilation.answerEverything();
            return of(compilation, compilation.modules().get(0), behavior);
        }

        static Model of(Compilation compilation, String module, String behavior) {
            Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
            RuleReadingSource rules = RuleReadings.of(compilation, module);
            Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
            assertNotNull(prepared, "the module prepared");
            assertNotNull(checked, "the module checked");
            Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                    .filter(b -> b.name().equals(behavior)).findFirst().orElseThrow();
            Map<String, InputDomain> inputs =
                    compilation.db().ask(new Adequacy.Inputs(module)).value();
            InputDomain domain = inputs.get(behavior);
            assertNotNull(domain, "the behavior's inputs were read");
            Partitions.Partitioning partitioning = Partitions.of(spec.name(), domain.reading(rules),
                    ReadAs.THE_COMPILATION_DOES);
            return new Model(MeasuredInput.of(spec.name(), domain.reading(rules), partitioning),
                    CoverageRead.of(spec.name(), checked.run(spec.name()), domain.reading(rules)));
        }
    }
}
