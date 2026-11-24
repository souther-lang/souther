package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.types.ValueName;

import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A parameter is one the body does not read where no name in the body is that parameter's binding:
 * a name of the same spelling bound further in is another, and a read in any arm, let or closure is
 * a read. Only these are left standing by a search over what the body answers, so each way a body
 * reads one has to be one that keeps it moved.
 */
class TheParametersABodyDoesNotReadAreTheOnesNoNameInItStandsForTest {

    private static Set<String> unread(String parameters, String body) {
        Compilation compilation = ACompiledModel.answered("""
                module example.reads

                behavior f : (%s) -> Int

                let f (%s) = %s
                """.formatted(parameters, names(parameters), body));
        return Adequacy.unreadParametersOf(compilation.db(),
                new ValueName.Behavior(compilation.modules().get(0), "f"));
    }

    private static String names(String parameters) {
        StringBuilder out = new StringBuilder();
        for (String each : parameters.split(", ")) {
            out.append(out.isEmpty() ? "" : ", ").append(each.substring(0, each.indexOf(':')));
        }
        return out.toString();
    }

    @Test
    void aParameterNothingNamesIsNotRead() {
        assertEquals(Set.of("b", "c"), unread("a: Int, b: Int, c: Int", "a"));
    }

    @Test
    void aParameterReadOnlyInOneArmIsRead() {
        assertEquals(Set.of("c"), unread("a: Int, b: Int, c: Int",
                "if a > 0 then b else 0"));
    }

    @Test
    void aParameterReadThroughALetIsRead() {
        assertEquals(Set.of("b"), unread("a: Int, b: Int", "{ let twice = a + a\n twice }"));
    }

    @Test
    void aParameterReadInsideAClosureIsRead() {
        assertEquals(Set.of("b"), unread("a: Int, b: Int, xs: List<Int>",
                "List.fold((acc, x) -> acc + x + a, 0, xs)"));
    }

    @Test
    void aNameBoundFurtherInIsNotTheParameter() {
        assertEquals(Set.of("b"), unread("a: Int, b: Int", "{ let b = 1\n a + b }"));
    }

    @Test
    void whichParametersAreUnreadDoesNotTurnOnTheirOrder() {
        assertEquals(unread("a: Int, b: Int, c: Int", "b"),
                unread("c: Int, b: Int, a: Int", "b"));
        assertEquals(Set.of("a", "c"), unread("c: Int, b: Int, a: Int", "b"));
    }
}
