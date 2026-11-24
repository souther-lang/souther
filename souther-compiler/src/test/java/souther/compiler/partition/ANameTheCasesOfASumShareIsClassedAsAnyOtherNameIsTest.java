package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.check.RuleKey;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.TermPath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the rules of a value around a place say of it does not depend on whether the name the rule
 * reads it by is one field or a field the cases of a sum share.
 *
 * <p>A name is written once and a value is of one case, so a rule over {@code q.limit} reads the
 * place {@code limit} under each case of {@code q} alone, as it reads {@code q.limit} alone where
 * {@code q} is a record. The place a name stands at is asked of the one crossing from names to
 * positions ({@code InputDomain#positionsNamed}), and not matched by the fields of its path, which
 * do not go through a case.
 */
class ANameTheCasesOfASumShareIsClassedAsAnyOtherNameIsTest {

    private static final String CASES = """
            data Paging = { limit: Int, offset: Int }
            data A = { ...Paging, x: Int }
            data B = { ...Paging, y: Int }
            data Q = A | B
            data Yes
            """;

    private static final RuleKey THE_LIMIT = RuleKey.of("q").then("limit");

    private static final RuleKey THE_OFFSET = RuleKey.of("q").then("offset");

    /** What is said of each place the name stands at, one for each case. */
    private static List<UndividedByARelation.Named> saidOf(String rule, RuleKey name) {
        InputReading read = reading("""
                module m

                %s
                data Holder = { q: Q } invariant %s

                behavior f : (h: Holder) -> Yes
                let f (h) = Yes
                """.formatted(CASES, rule));
        List<TermPath> places = read.domain().positionsNamed(TermPath.of("h"), name);
        assertEquals(2, places.size(), "the name stands under each case: " + places);
        List<UndividedByARelation.Named> out = new ArrayList<>();
        places.forEach(place -> out.add(UndividedByARelation.namedByTheDeclarations(place, read)));
        return out;
    }

    @Test
    void aRuleReadingTheSharedNameAloneIsARuleOfThePlaceUnderEachCase() {
        assertEquals(List.of(UndividedByARelation.Named.BY_ONE_PLACE,
                        UndividedByARelation.Named.BY_ONE_PLACE),
                saidOf("q.limit >= 0 && q.limit <= 100", THE_LIMIT));
    }

    @Test
    void aRuleReadingTwoSharedNamesMayTieThemWhicheverCaseTheyAreUnder() {
        for (RuleKey name : List.of(THE_LIMIT, THE_OFFSET)) {
            for (UndividedByARelation.Named said : saidOf("q.limit <= q.offset", name)) {
                assertTrue(said.mayBeTied(), name + " is " + said);
            }
        }
    }

    private static InputReading reading(String model) {
        Compilation compilation = ACompiledModel.compiles(Compilation.ofSource(model, "Main"));
        var inputs = compilation.db().ask(new Adequacy.Inputs("m")).value().get("f");
        assertNotNull(inputs, "the model under test compiles");
        return inputs.reading(RuleReadings.of(compilation, "m"));
    }
}
