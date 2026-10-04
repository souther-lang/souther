package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.ClauseName;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.InputDomain;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A pattern written with a value of the module offers a value the pattern accepts.
 *
 * <p>The checker folds the pattern where it settles the call, so what the rule accepts is known
 * however the author built the text — a literal joined to a named value is a pattern like any other.
 * A row is composed out of what the rule accepts, so the value it proposes has to come from the same
 * reading: proposed out of a weaker reading of the text, the position is offered the value its type
 * stands for and every row through it is refused at construction.
 */
class APatternWrittenWithANamedValueOffersWhatItAcceptsTest {

    private static final String JOINED = """
            module example.ids

            let tail = "[0-9]{3}"

            data Code = String
                invariant String.matches("00Q" ++ tail, value)

            data Grade = Low | High

            data Holder = { code: Code, grade: Grade }

            data Ok

            behavior take : (h: Holder) -> Ok

            let take (h) = Ok
            """;

    /** The same pattern written out as one literal, which is what the rule above accepts. */
    private static final String WRITTEN_OUT = JOINED.replace("\"00Q\" ++ tail", "\"00Q[0-9]{3}\"");

    @Test
    void aPatternJoinedOutOfANamedValueOffersAValueItAccepts() {
        FillResult filled = filled(JOINED);

        assertFalse(filled.rows().isEmpty(), "the generation wrote rows");
        String row = filled.rows().get(0).inputs().get(0).text();
        assertTrue(row.matches(".*Code\\(\"00Q[0-9]{3}\"\\).*"),
                "the code is one the pattern accepts: " + row);
    }

    /** And the value is the one the same pattern offers written out, since it is the same rule. */
    @Test
    void itOffersWhatTheSamePatternWrittenOutOffers() {
        assertEquals(filled(WRITTEN_OUT).rows().get(0).inputs().get(0).text(),
                filled(JOINED).rows().get(0).inputs().get(0).text());
    }

    /**
     * And a rule the checker has no form for is a rule not read, said under the rule.
     *
     * <p>The value is read off what the checker typed, so a clause it could not type offers no
     * value — and a search that had every other value refused has not shown the model refuses them.
     * Here the rule calls a recursive helper, which the reading of a declaration's clauses leaves
     * standing and has no signature for; the model itself compiles.
     */
    @Test
    void aRuleTheCheckerHasNoFormForIsSaidToBeNotRead() {
        RuleReadingSource rules = RuleReadings.ofSource("""
                module demo

                data Empty
                data More = { next: Chain }
                data Chain = Empty | More

                let reaches (c: Chain, s: String): Bool = match c with
                    | More as m -> reaches(m.next, s)
                    | Empty -> String.length(s) == 7

                data A = String
                    invariant ended = reaches(Empty, value)
                """);
        TypeSymbol at = TypeSymbols.declared(new TypeKey(rules.symbols().module(), "A"));

        StringOfferShortfall shortfall = Partitions.notOffered(Type.ref(at),
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES));

        assertEquals(List.of("ended"), shortfall.these().stream()
                .map(each -> each.of() instanceof StringOfferShortfall.Subject.ARule rule
                        ? rule.part().rule().clause().name().map(ClauseName::value).orElse("?")
                        : each.of().toString())
                .toList(), "the one rule about the strings is named as not read");
        // And not read because no reading reached it, which is not a form nothing takes apart: an
        // author told the second rewrites a rule whose form was never the matter. Said in the
        // reason the reading of the position gives the same clause.
        assertEquals(List.of(new StringOfferShortfall.Why.NotRead(
                        new BlockReason.ValueRulesNotReached())),
                shortfall.these().stream().map(StringOfferShortfall.NotOffered::why).toList(),
                "said as rules no reading reached");
    }

    private static FillResult filled(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        assertNotNull(sigs, "the model did not compile");
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        InputDomain domain = InputDomain.of(sigs.get("take"),
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES));
        Partitions.Partitioning partitioning =
                Partitions.of("take", domain.reading(rules), ReadAs.THE_COMPILATION_DOES);
        MeasuredInput subject = MeasuredInput.of("take", domain.reading(rules), partitioning);
        return GenerationFixtures.fill(subject, List.of(), Generator.CandidateCheck.ANY,
                Budgets.generation());
    }
}
