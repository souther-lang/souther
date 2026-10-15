package souther.compiler.report;

import souther.compiler.DocumentShape;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ExpansionSite;
import souther.compiler.types.ParameterSlot;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.SourceReferenceOrigin;
import souther.compiler.types.StepOfACopy;
import souther.compiler.types.ValueName;
import souther.compiler.types.WrittenOwner;

import org.junit.jupiter.api.Test;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;
import tools.jackson.databind.node.ObjectNode;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A step of a copy is said by every field that tells it from the steps beside it, in the document
 * and on a page alike.
 *
 * <p>Steps that differ in one field only — the module, the definition, the call, how far it was
 * lowered, which reference, which copy a block was handed to, which parameter it filled, where it
 * was applied — are written as different fields and said in different words.
 */
class AStepOfACopyIsSaidByEveryFieldThatTellsItApartTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final ValueName PRICE = new ValueName.Helper("m", "price");
    private static final ValueName APPLY = new ValueName.Helper("m", "apply");

    /** Steps alike but for one field each, against the first. */
    private static final List<StepOfACopy> STEPS = List.of(
            new StepOfACopy.ACall(PRICE, called("m", "f", 0, 0)),
            new StepOfACopy.ACall(PRICE, called("n", "f", 0, 0)),
            new StepOfACopy.ACall(PRICE, called("m", "g", 0, 0)),
            new StepOfACopy.ACall(PRICE, called("m", "f", 1, 0)),
            new StepOfACopy.ACall(PRICE, called("m", "f", 0, 1)),
            new StepOfACopy.ACall(PRICE, named("m", "f", 0)),
            new StepOfACopy.ACall(PRICE, named("n", "f", 0)),
            new StepOfACopy.ACall(PRICE, named("m", "f", 1)),
            handed(0, 0, called("m", "apply", 0, 0)),
            handed(1, 0, called("m", "apply", 0, 0)),
            handed(0, 1, called("m", "apply", 0, 0)),
            handed(0, 0, called("m", "apply", 1, 0)),
            handed(0, 0, named("m", "apply", 0)));

    @Test
    void stepsThatDifferInOneFieldAreWrittenApart() {
        List<JsonNode> written = new ArrayList<>();
        for (StepOfACopy step : STEPS) {
            ObjectNode one = JSON.createObjectNode();
            StepIdentity.of(new StepIdentity.InTheDocument(one), step);
            written.add(one);
        }
        assertEquals(STEPS.size(), new HashSet<>(written).size(),
                () -> "each step written as its own: " + written);
    }

    @Test
    void stepsThatDifferInOneFieldAreSaidApart() {
        List<String> said = STEPS.stream().map(StepIdentity::inWords).toList();
        assertEquals(STEPS.size(), new HashSet<>(said).size(),
                () -> "each step said as its own: " + said);
    }

    /**
     * A document naming a combination whose decisions stand in a value passed by name to one that
     * applies it writes the name and the handing over as fields, and is shaped as the schema says.
     */
    @Test
    void aCopyMadeAtANameAndAHandingOverIsWrittenAsFields() {
        Compilation compilation = Compilation.ofSource("""
                module p
                behavior f : (a: Int, b: Int) -> Int
                let big (k: Int): Int = if k > 5 then 10 else 1
                let apply (g: (Int) -> Int, k: Int): Int = g(k)
                let f (a, b) = apply(big, a) + apply(big, b)
                example f
                    | (6, 6) -> 20
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors());
        JsonNode document = JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));

        List<JsonNode> steps = document.findValues("through").stream()
                .flatMap(through -> through.valueStream()).toList();
        assertTrue(steps.stream().anyMatch(step -> step.path("name").isObject()),
                () -> "a copy made at a name: " + steps);
        assertTrue(steps.stream().anyMatch(step -> step.path("supplied").path("handedTo")
                        .isObject() && step.path("supplied").path("appliedAt").isObject()),
                () -> "a copy made at a block handed over and applied: " + steps);
        DocumentShape.assertShapedLikeTheSchema(document);
    }

    private static ExpansionSite.Written called(String module, String definition, int call,
                                                int lowered) {
        return new ExpansionSite.Written(new SourceConstructOrigin(
                new WrittenOwner.Body(module, definition), call, lowered, SourceConstruct.CALL));
    }

    private static ExpansionSite.Named named(String module, String definition, int reference) {
        return new ExpansionSite.Named(new SourceReferenceOrigin(
                new WrittenOwner.Body(module, definition), reference));
    }

    /** A copy of {@code price} handed to the copy of {@code apply} made at call {@code call} of
     *  {@code f}, as its parameter {@code parameter}, and applied at {@code applied}. */
    private static StepOfACopy handed(int call, int parameter, ExpansionSite.Direct applied) {
        return new StepOfACopy.ACall(PRICE, new ExpansionSite.Supplied(
                new ExpansionSite.Supplied.Handover(
                        new ExpansionLineage.Step(APPLY, called("m", "f", call, 0)),
                        new ParameterSlot(parameter)),
                applied));
    }
}
