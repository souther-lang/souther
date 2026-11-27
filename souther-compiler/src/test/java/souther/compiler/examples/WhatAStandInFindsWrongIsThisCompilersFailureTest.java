package souther.compiler.examples;

import souther.compiler.Compiler;
import souther.compiler.evaluate.EvaluationContext;
import souther.compiler.generated.GeneratedImplementations;
import souther.compiler.generated.GeneratedLinkage.GeneratedClassDefect;
import souther.compiler.generated.MemoryClassLoader;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * What a stand-in this compile made finds wrong inside a call the generated code made on it is
 * this compiler failing, and not something the applied code ended with.
 *
 * <p>The call into the generated code is reflective, and what the code ends with comes back as an
 * {@link InvocationFailure} a row reads as the model's. A stand-in answers inside that call, so what
 * it finds wrong arrives the same way; it has to come out as the compiler's own failure however the
 * call wrapped it.
 */
class WhatAStandInFindsWrongIsThisCompilersFailureTest {

    private static final String MODEL = """
            module probe.defect

            behavior lookup : (key: Int) -> Int

            behavior convert : (a: Int, b: Int) -> Int
                depends on lookup
            let convert (a, b, lookup) = lookup(a) + b

            behavior top : (a: Int, b: Int) -> Int
                depends on convert
            let top (a, b, convert) = convert(a, b)
            """;

    /** A stand-in answering a value of another type than the method it answers returns. */
    @Test
    void anAnswerTheMethodDoesNotReturnIsThisCompilersFailure() {
        GeneratedImplementation answerer = new GeneratedImplementation(
                new GeneratedImplementations("probe.defect", Set.of("top"), Set.of()),
                new MemoryClassLoader(Compiler.compile(MODEL), getClass().getClassLoader()));
        Answerer.Answer.Something top =
                assertInstanceOf(Answerer.Answer.Something.class, answerer.of("top"));
        Answerer.Applying applying = top.applying(List.of(new DependencyStandin(
                new ValueName.Behavior("probe.defect", "convert"), _ -> "twelve")));

        EvaluationContext.begin(1_000, 100);
        try {
            assertThrows(GeneratedClassDefect.class, () -> applying.to(List.of(
                    new Handed(1L, () -> null), new Handed(2L, () -> null))),
                    "not carried out as what the applied code ended with");
        } finally {
            EvaluationContext.end();
        }
    }
}
