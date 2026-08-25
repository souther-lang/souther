package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.test.RepositoryLayout;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.TermPath;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Scopes;
import souther.compiler.query.Shapes;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a value has to be built and where a behavior's input has a position are different questions.
 *
 * <p>They are spelled with the same {@link TermPath} and they are about different things, which is
 * the defect this exists over: two walks derived the positions of one parameter, at two depths, and a
 * question the reading of an input was asked about a position the generator was working at came back
 * refused because the reading had no such position. Read as one set, the refusal looks like the model
 * having nothing there.
 *
 * <p>How the sets part is depth. The reading stops where a report stops being about one input; the
 * search goes on until there is a value to build.
 *
 * <p>How a position is <em>named</em> is the one thing they do not part over. A class that narrows a
 * sum to one of its cases puts positions under that narrowing, and both write the narrowing into the
 * path — so a class fixed at such a position is looked for at the path the plan builds it at.
 * Written flat here, the same location would have two names and the lookup would find nothing.
 *
 * <p>So what is checked here is that a path from one is not looked up in the other, and that the
 * disagreement is the design rather than a defect. The one thing they share is the step, and that is
 * checked over in {@code inputs} by
 * {@code TheReadingAndThePlanTakeOneStepDownATypeTest}.
 */
class AConstructionPositionIsNotAnInputPositionTest {

    /** Read once: what this asks of it does not change between its checks. */
    private static final RepositoryLayout REPOSITORY = RepositoryLayout.ofWorkingDirectory();

    private record Read(Hir.SpecBehavior spec, Sig sig, Symbols symbols) {}

    private static Read of(String source, String behavior) {
        Compilation compilation =
                Compilation.ofSources(List.of(source), souther.compiler.meta.ModulePath.EMPTY);
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(b -> b.name().equals(behavior)).findFirst().orElseThrow();
        return new Read(spec, sigs.get(behavior), symbols);
    }

    private static InputDomain reading(Read read) {
        return InputDomain.of(read.spec(), read.sig(), read.symbols(), ReadAs.THE_COMPILATION_DOES);
    }

    /** The plan for the behavior's one parameter, with nothing decided and the given
     *  requirements. */
    private static ConstructionPlan plan(Read read, Requirements required) {
        ConstructionPlan.Result planned = ConstructionPlan.of(read.sig().inputTypes().get(0),
                TermPath.of(read.spec().params().get(0).name()), read.symbols(), Set.of(), required,
                (_, _) -> 0);
        return assertInstanceOf(ConstructionPlan.Result.Planned.class, planned,
                "nothing here asks one position to be two things").plan();
    }

    private static List<String> slots(ConstructionPlan plan) {
        return plan.slots().stream().map(each -> each.at().toString()).toList();
    }

    private static final String NESTED = """
            module g

            data Zip = { code: String }
            data Address = { zip: Zip }
            data Person = { home: Address }
            data Order = { who: Person }
            data Ack = { at: String }

            behavior place : (o: Order) -> Ack
            """;

    /**
     * The reading stops where a report stops, and every position it does have answers for itself.
     *
     * <p>The first half of the rule. A path this reading holds is one it can be asked about, which
     * is what makes the other half a statement about something and not about a lookup that never
     * worked.
     */
    @Test
    void everyPositionTheReadingHasIsOneItAnswersFor() {
        InputDomain reading = reading(of(NESTED, "place"));
        assertEquals(List.of("o", "o.who", "o.who.home"),
                reading.positions().stream().map(each -> each.path().toString()).toList());
        for (Position each : reading.positions()) {
            assertNotNull(reading.at(each.path()), () -> "no position at " + each.path());
        }
    }

    /**
     * And a position the search builds at below that is not one of them.
     *
     * <p>Not a lookup that failed. The report is about {@code o.who.home} and the row still has to
     * carry a {@code Zip} with a {@code code} in it, so the search reaches two levels the reading
     * declines to describe. Asking this reading about {@code o.who.home.zip.code} and taking the
     * answer for the model's is what the two walks were doing to each other.
     */
    @Test
    void theSearchBuildsAtPositionsTheReadingDoesNotDescribe() {
        Read read = of(NESTED, "place");
        assertEquals(List.of("o.who.home.zip.code"), slots(plan(read, Requirements.NONE)));
        assertNull(reading(read).at(TermPath.of("o").then("who").then("home").then("zip")),
                "the reading stops at the second level and does not answer below it");
        assertNull(reading(read).at(
                        TermPath.of("o").then("who").then("home").then("zip").then("code")),
                "a position a value is built at is not a position of the input");
    }

    private static final String SUM = """
            module g

            data Approved = { id: Int }
            data Rejected = { why: String }
            data Decision = Approved | Rejected
            data Ack = { at: String }

            behavior decide : (d: Decision) -> Ack
            behavior probe : (a: Approved) -> Ack
            """;

    /**
     * A recipe puts positions under a sum, and no depth would have found them.
     *
     * <p>The half that says the two sets are not one set with a bound on it. {@code Decision} is a
     * sum and nothing is under it — the reading says so, and a reading that went on for ever would
     * say the same. What the row is building is an {@code Approved}, because a class of the position
     * said which case its witness takes, and {@code d.id} is a position of that and of nothing the
     * behavior declares.
     */
    @Test
    void aRecipePutsPositionsWhereTheDeclarationHasNone() {
        Read read = of(SUM, "decide");
        assertEquals(List.of("d"), slots(plan(read, Requirements.NONE)),
                "with no class choosing a constructor there is one thing to build, the sum itself");

        ConstructionPlan built = plan(read, throughApproved(read));
        assertEquals(List.of("d@Approved.id"), slots(built),
                "a narrowed position is written with the narrowing, as the reading writes it");

        InputDomain reading = reading(read);
        assertNotNull(reading.at(TermPath.of("d")), "the sum itself is a position of the input");
        assertNull(reading.at(TermPath.of("d").then("id")),
                "what is built under the sum is not at a name the declaration puts nothing at");
    }

    /**
     * And nothing that holds a plan can ask the reading about one of its positions.
     *
     * <p>The tests above say the two sets are two. What they cannot say is that nobody writes
     * {@code inputDomain.at(slot.at())} — the coordinate is one type on purpose, so that call
     * compiles, and what comes back is null for a construction position and a position of the input
     * for a path that happens to be both.
     *
     * <p>Asked of the sources at the grain the reading's own rule is asked at. Naming the file that
     * holds a plan is where such a call would be written, so the first line of it turns this red;
     * a helper in between defeats it, as it defeats every check of this kind here.
     *
     * <p>Asked of the code and not of the comments. Saying that the two are different things means
     * naming both, and a file doing that was the one thing this could not tell from a file asking
     * one about the other — answered by exempting the file that said it, which is an exemption that
     * grows by one every time somebody writes the sentence down.
     */
    @Test
    void nothingThatHoldsAPlanConsultsTheReading() throws IOException {
        List<Path> sources = mainSources();
        assertTrue(sources.size() > 20,
                () -> "the scan found only " + sources.size() + " sources, which is not the tree");

        List<String> both = new ArrayList<>();
        for (Path source : sources) {
            String text = code(Files.readString(source, StandardCharsets.UTF_8));
            if (!text.contains("ConstructionPlan") || !text.contains("InputDomain")) {
                continue;
            }
            both.add(source.getParent().getFileName() + "/" + source.getFileName());
        }
        assertEquals(List.of(), both,
                "a coordinate of the plan is not a position of the input, and these could ask");
    }

    /** {@code source} with its comments taken out, which is what this reads. */
    private static String code(String source) {
        return source.replaceAll("(?s)/\\*.*?\\*/", " ").replaceAll("//[^\n]*", " ");
    }

    private static List<Path> mainSources() throws IOException {
        return REPOSITORY.mainJavaSources();
    }

    /** The requirement a class of {@code d} states by being the {@code Approved} case of it. */
    private static Requirements throughApproved(Read read) {
        return Requirements.NONE.and(TermPath.of(read.spec().params().get(0).name()),
                Refinement.sumCase(caseNamed(SUM, "probe")));
    }

    /** The name of the case to build through, taken off a behavior that is declared to take one. */
    private static TypeSymbol caseNamed(String source, String behavior) {
        Read read = of(source, behavior);
        return assertInstanceOf(ConstructionPlan.Built.class,
                plan(read, Requirements.NONE).root()).of();
    }

    /** And the declared type of the position does not move when a recipe chooses a case for it. */
    @Test
    void theRecipeRefinesWhatIsBuiltAndNotWhatIsDeclared() {
        Read read = of(SUM, "decide");
        Type declared = read.sig().inputTypes().get(0);
        assertEquals(declared, reading(read).at(TermPath.of("d")).view().declared());

        ConstructionPlan built = plan(read, throughApproved(read));
        assertEquals(declared, reading(read).at(TermPath.of("d")).view().declared(),
                "the position is still declared to hold a Decision");
        ConstructionPlan.Built root = assertInstanceOf(ConstructionPlan.Built.class, built.root(),
                "an `Approved` is composed out of its fields");
        assertEquals("Approved", Type.show(root.type()),
                "and what is built there is the case the class named");
    }
}
