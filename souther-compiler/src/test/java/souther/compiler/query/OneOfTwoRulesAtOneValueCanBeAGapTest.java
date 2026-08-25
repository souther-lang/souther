package souther.compiler.query;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two rules drawing a line at one value are two obligations, and a row can meet one of them.
 *
 * <p>Which is what the origins have always said: a type's invariant and a {@code guard} that repeats
 * it merge into one partition and stay separate obligations, because reaching one says nothing about
 * the other. Meeting them is not the same work either — an invariant's is met by writing the value,
 * a guard's takes getting the comparison to answer — so a row at the value can settle one while the
 * one beside it is still owed.
 *
 * <p>What is generated for a gap looked the pair up by the value alone. It took whichever assessment
 * came first, and where that was the met one it read its own answer as a contradiction and refused
 * to go on: {@code the assessment at charge/a.n = 100 says A_ROW_IS_ALREADY_THERE, which is not a
 * gap}. Nothing about the report was wrong — both lines were counted and printed — so what showed
 * was the failure after them and not the reading that caused it.
 *
 * <p>The model here is the smallest one that gets there. The row writes a hundred, which is
 * {@code N}'s own minimum, and takes the branch above the guard: the invariant's line at a hundred
 * is met, the guard's at the same hundred is not.
 */
class OneOfTwoRulesAtOneValueCanBeAGapTest {

    private static final String MODULE = """
            module demo

            data N = Int invariant value >= 100
            data Amount = { flag: Bool, n: N }
            data Ok = { n: Int }
            data Refused = { why: String }

            behavior charge : (a: Amount) -> Ok | Refused
                constructs Ok, Refused
            let charge (a) =
                if a.flag then
                    Ok { n = 1 }
                else
                    if a.n.value > 100 then Ok { n = 2 } else Refused { why = "small" }

            example charge
                | (Amount { flag = true, n = N(100) }) -> Ok { n = 1 }
            """;

    @Test
    void theGapIsAnsweredByItsOwnRuleAndNotByTheOneBesideIt() {
        Compilation compilation = Compilation.ofSource(MODULE, "Main");
        // Set before anything is asked. The lines are measured only where the arms are, and that is
        // what puts two obligations at one value in front of the reading under test.
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String module = compilation.modules().get(0);

        // Both halves. That the gap exists is what makes the lookup happen at all, and a model
        // whose lines were all met would pass this without the reading under test having run.
        assertTrue(compilation.db().ask(new Adequacy.Findings(module)).value().stream()
                        .filter(each -> each.subject().isBehavior("charge"))
                        .anyMatch(each -> each.kind() == Adequacy.Kind.BOUNDARY_UNMET),
                "the guard's line at a hundred is the gap this is about");
        assertDoesNotThrow(() -> Adequacy.generatedOf(compilation.db(), module),
                "the two obligations at one value were read as contradicting each other");
    }
}
