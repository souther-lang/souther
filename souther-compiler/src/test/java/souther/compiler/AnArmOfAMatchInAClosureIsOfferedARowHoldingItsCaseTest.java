package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.partition.GenerationOutcome;
import souther.compiler.partition.Generator;
import souther.compiler.partition.ObligationIdentity;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Offering;
import souther.compiler.query.OfferingRequest;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * An arm of a {@code match} on what a closure was handed out of a list is offered a row whose list
 * holds an element of the arm's case, under what holds on the way to the closure.
 *
 * <p>The reading of the runs names no way into the arm: the closure runs where the operation calls
 * it. The tree the operations stand in names the arm a case of the element, and a run down it is one
 * application handed one such element — so a row holding one is where to look, and the run through
 * it is what says it went down the arm.
 *
 * <p>Two closures over one list, one inside the other, ask a case of one element or of two, which
 * is not read. An arm only such a way leads to is offered nothing, and is this compiler's shortfall.
 */
class AnArmOfAMatchInAClosureIsOfferedARowHoldingItsCaseTest {

    private static final String MODEL = """
            module offered
            data Yes
            data No
            data Flag = Yes | No
            data North
            data South
            data Region = North | South
            data Ok = { n: Int }

            behavior judge : (f: Flag, xs: List<Region>) -> Ok
                constructs Ok
            let judge (f, xs) = {
                guard (match f with | Yes -> true | No -> false) else Ok { n = 0 }
                Ok { n = List.fold((acc, r) -> match r with
                    | North -> acc + 1
                    | South -> acc, 0, xs) }
            }

            example judge
                | "no" : (No, []) -> Ok { n = 0 }
                | "one north" : (Yes, [North]) -> Ok { n = 1 }
            """;

    private static final String NESTED = """
            module nested
            data North
            data South
            data Region = North | South
            data Ok = { n: Int }

            behavior judge : (xs: List<Region>) -> Ok
                constructs Ok
            let judge (xs) = Ok { n = List.fold((acc, r) -> match r with
                | North -> List.fold((inner, s) -> match s with
                    | North -> inner
                    | South -> inner + 1, acc, xs)
                | South -> acc, 0, xs) }

            example judge
                | "none" : ([]) -> Ok { n = 0 }
            """;

    @Test
    void theArmIsOfferedAListHoldingItsCaseUnderTheGuardAboveIt() {
        List<Adequacy.GenerationDisposition> arms = armsOwed(generated(MODEL, "offered"));

        assertEquals(1, arms.size(), () -> "`case South` is the one arm no row went down: " + arms);
        GenerationOutcome.Generated south = assertInstanceOf(GenerationOutcome.Generated.class,
                arms.getFirst().outcome(), () -> "and it is offered a row: " + arms);
        assertEquals(List.of(List.of("Yes", "[South]")), rowsOf(south),
                () -> "a list with a `South` in it, past the guard on `f`: " + arms);
    }

    @Test
    void anArmOnlyTwoApplicationsOverOneListLeadToIsOfferedNothing() {
        List<Adequacy.GenerationDisposition> arms = armsOwed(generated(NESTED, "nested"));

        assertEquals(4, arms.size(), () -> "no row went down any arm: " + arms);
        // Each outer arm is one application, and a list of one `North` goes down the outer
        // `North` and then, the inner closure running over the same list, the inner `North` —
        // which watching the row says. The inner `South` needs a `North` and a `South`.
        List<Adequacy.GenerationDisposition> none = arms.stream()
                .filter(each -> !(each.outcome() instanceof GenerationOutcome.Generated))
                .toList();
        assertEquals(1, none.size(), () -> "one arm is offered nothing: " + arms);
        assertEquals(1, ((ObligationIdentity.OfAnArm) none.getFirst().item().orElseThrow())
                .arm().part(), () -> "and it is a `South`: " + none);
        GenerationOutcome.NotSupported inner = assertInstanceOf(
                GenerationOutcome.NotSupported.class, none.getFirst().outcome());
        assertEquals(List.of(
                        GenerationOutcome.NotSupported.Reason.THE_ARM_RUNS_WHERE_SOMETHING_CALLS_IT),
                List.copyOf(inner.reasons()));
    }

    /** What was offered for each arm owed a row. */
    private static List<Adequacy.GenerationDisposition> armsOwed(
            List<Adequacy.GenerationDisposition> said) {
        List<Adequacy.GenerationDisposition> arms = new ArrayList<>();
        for (Adequacy.GenerationDisposition each : said) {
            if (each.item().orElse(null) instanceof ObligationIdentity.OfAnArm) {
                arms.add(each);
            }
        }
        return arms;
    }

    private static List<List<String>> rowsOf(GenerationOutcome.Generated generated) {
        List<List<String>> out = new ArrayList<>();
        for (Generator.GeneratedRow row : generated.candidates()) {
            out.add(row.inputs().stream().map(input -> input.text()).toList());
        }
        return out;
    }

    private static List<Adequacy.GenerationDisposition> generated(String model, String module) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Offering offering = Adequacy.offeredFor(compilation.db(),
                OfferingRequest.overTheModule(module));
        List<Adequacy.GenerationDisposition> out = new ArrayList<>();
        offering.searched().values().forEach(filling -> out.addAll(filling.generation()));
        return out;
    }
}
