package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.carrier.Membership;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.TypeCardinality;
import souther.compiler.inputs.InputDomain;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule that a string match one pattern or another offers a value one of the patterns accepts.
 *
 * <p>The strings either pattern accepts are one set of strings, so a value is composed out of it as
 * out of a single pattern. Read as no predicate at all, the position is offered the value its type
 * stands for, which neither pattern accepts, and every row through it is refused at construction.
 */
class AChoiceBetweenPatternsOffersAValueOneOfThemAcceptsTest {

    private static String model(String rule) {
        return """
                module example.codes

                data Code = String
                    invariant %s

                data Grade = Low | High

                data Holder = { code: Code, grade: Grade }

                data Ok

                behavior take : (h: Holder) -> Ok

                let take (h) = Ok
                """.formatted(rule);
    }

    @Test
    void aChoiceBetweenTwoPatternsOffersAValueOneOfThemAccepts() {
        String code = offeredCode(model("String.matches(\"[A-Z]{2}-[0-9]{4}\", value)\n"
                + "           || String.matches(\"[0-9]{6}\", value)"));

        assertTrue(code.matches("[A-Z]{2}-[0-9]{4}|[0-9]{6}"),
                "the code is one a pattern of the choice accepts: " + code);
    }

    /** A choice among three is a choice whose one side is a choice, and is read the same way. */
    @Test
    void aChoiceAmongThreePatternsOffersAValueOneOfThemAccepts() {
        String code = offeredCode(model("String.matches(\"[A-Z]{3}\", value)\n"
                + "           || String.matches(\"[0-9]{6}\", value)\n"
                + "           || String.matches(\"x-[a-z]{2}\", value)"));

        assertTrue(code.matches("[A-Z]{3}|[0-9]{6}|x-[a-z]{2}"),
                "the code is one a pattern of the choice accepts: " + code);
    }

    /** The code the first row composed writes, as the text between the quotes of {@code Code(...)}. */
    private static String offeredCode(String source) {
        FillResult filled = filled(source);
        assertFalse(filled.rows().isEmpty(), "the generation wrote rows");
        String row = filled.rows().get(0).inputs().get(0).text();
        int open = row.indexOf("Code(\"");
        assertTrue(open >= 0, "the row writes a code: " + row);
        int from = open + "Code(\"".length();
        return row.substring(from, row.indexOf('"', from));
    }

    private static FillResult filled(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        assertNotNull(sigs, "the model did not compile");
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext reading =
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        InputDomain domain = InputDomain.of(sigs.get("take"), reading,
                TypeCardinality.Counts.workedOutIn(reading), Membership.none());
        Partitions.Partitioning partitioning =
                Partitions.of("take", domain.reading(rules), ReadAs.THE_COMPILATION_DOES);
        MeasuredInput subject = MeasuredInput.of("take", domain.reading(rules), partitioning);
        return GenerationFixtures.fill(subject, List.of(), Generator.CandidateCheck.ANY,
                Budgets.generation());
    }
}
