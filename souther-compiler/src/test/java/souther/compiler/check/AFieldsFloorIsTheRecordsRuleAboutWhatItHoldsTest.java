package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.numeric.Count;
import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;
import souther.compiler.types.TypeName;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;

import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How much a field has to hold, where the record it sits in is what says so.
 *
 * <p>A rule counting a field — {@code List.length(xs) >= 2} — bounds the count and not the field, so
 * it reaches the domain under an atom of its own and a reader asking what the field can hold is told
 * nothing. That is a different question from {@link FieldDomains#at}, which answers what the value at
 * a position is, and the two are kept apart here because the same numbers stand for different things.
 */
class AFieldsFloorIsTheRecordsRuleAboutWhatItHoldsTest {

    private static FieldDomains domainsIn(String source, String type) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Symbols symbols = compilation.db().ask(new Shapes.Scope(module)).value();
        assertNotNull(symbols, "the model did not compile");
        TypeName named = new TypeName(module, type);
        Ast.Data data = (Ast.Data) symbols.get(named);
        assertNotNull(data, "no `" + type + "` in " + module);
        return FieldDomains.of(named, data, symbols);
    }

    @Test
    void aRecordsCountRuleIsWhatItsFieldHasToHold() {
        FieldDomains domains = domainsIn("""
                module example.bag

                data Bag =
                    { xs: List<Int>
                    }
                    invariant atLeastTwo = List.length(xs) >= 2
                """, "Bag");

        FieldDomains.Held held = domains.heldAt("xs");
        assertNotNull(held, "the record says how much the list holds");
        assertEquals(0, BigDecimal.valueOf(2).compareTo(Count.number(held.bounds().min().at()).at()),
                "two, which is what the rule counts");
        assertTrue(held.bounds().min().inclusive(), "and a list of two is one the rule admits");
    }

    /**
     * A field is in one of the two answers or in neither, and never in both.
     *
     * <p>The numbers are the same numbers, so a caller that could get both from one field would be a
     * caller that has to decide which of them a bound is about. What settles it is the position's own
     * type: a number is its own value and a list is counted by how much of it there is.
     */
    @Test
    void aFieldIsEitherANumberOrSomethingCountedAndNotBoth() {
        FieldDomains domains = domainsIn("""
                module example.mixed

                data Mixed =
                    { n: Int
                    , xs: List<Int>
                    }
                    invariant bigEnough = n >= 5
                    invariant atLeastTwo = List.length(xs) >= 2
                """, "Mixed");

        assertNotNull(domains.at("n"), "a number is bounded as the value it is");
        assertNull(domains.heldAt("n"), "and nothing counts what a number holds");
        assertNotNull(domains.heldAt("xs"), "a list is bounded by how much of it there is");
        assertNull(domains.at("xs"), "and a list is no number to bound");
    }

}
