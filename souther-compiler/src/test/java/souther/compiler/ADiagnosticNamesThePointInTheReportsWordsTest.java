package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.msg.ExampleMessage;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Db;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A border's point is named in the diagnostic by the word the report gives it.
 *
 * <p>One finding is told twice. {@code souther examples} writes {@code no row is at the ON point}
 * and the warning built from the same {@code BOUNDARY_UNMET} wrote nothing about which point it
 * was, so a reader handed the technique's vocabulary by the report was asked to work it out again
 * at the diagnostic. The role travels with the finding already; what was missing is a sentence
 * reading it.
 *
 * <p>{@code ON} and {@code OFF} are the same word in every catalog. They are the syllabus's terms
 * for the two points against the line (ISTQB CTAL-TA v4.0 §3.1.1) rather than English words for
 * them, and the report writes them untranslated in both of its forms — so they are handed over as
 * a name is, and what each catalog holds is the sentence around them.
 *
 * <p>Both origins, because which point this is and how the rule is named are separate questions.
 * A fork of a body has a place and no name, so its sentence says the construct and points at where
 * it is written; an {@code ensures} has a name and no place. Naming the point must not decide
 * either of those, and a test taking both roles off one origin would not say so.
 */
class ADiagnosticNamesThePointInTheReportsWordsTest {

    /**
     * Two borders, one drawn by a fork and one by a clause, neither of them reached.
     *
     * <p>The guard's line is closed at a hundred, so its {@code ON} point is a hundred and its
     * {@code OFF} point is one over. The clause's is open at zero, so its {@code OFF} point is zero
     * and its {@code ON} point is one. The single row writes five and is at none of the four.
     */
    private static final String MODULE = """
            module demo

            data TodoId = Int
            data Todo = { id: TodoId }
            data NotFound = { asked: TodoId }

            behavior findTodo : (id: TodoId) -> Todo | NotFound
                ensures asked = NotFound -> id.value > 0
                constructs Todo, NotFound
            let findTodo (id) = {
                guard id.value <= 100 else NotFound { asked = id }
                Todo { id = id }
            }

            example findTodo | (TodoId(5)) -> Todo { id = TodoId(5) }
            """;

    /** The point a fork's line is on, in the word the report uses for it. */
    @Test
    void aForksOnPointSaysItIsTheOnPoint() {
        Diagnostic said = theOneAt("100");

        assertInstanceOf(ExampleMessage.NoRowIsAtThePointOfTheBorderAConstructDrew.class, said.said(),
                () -> "a fork has no name, so its sentence says the construct: " + said.said());
        assertEquals("ON", said.values().get("point"),
                () -> "the report calls this the ON point: " + said.values());
    }

    /** And the point one step outside a clause's line, which is the other role and the other origin. */
    @Test
    void aClausesOffPointSaysItIsTheOffPoint() {
        Diagnostic said = theOneAt("0");

        assertInstanceOf(ExampleMessage.NoRowIsAtThePointOfTheBorderARuleDrew.class, said.said(),
                () -> "a clause has a name, so its sentence names the rule: " + said.said());
        assertEquals("OFF", said.values().get("point"),
                () -> "the report calls this the OFF point: " + said.values());
    }

    /**
     * What a row at the point shows is asked of the point and not of the border.
     *
     * <p>The hint used to be said of both: a row on the line is what tells {@code <=} from
     * {@code <}, which is true of the {@code ON} point and is not what a row one step outside it
     * shows. Two points, two things to say.
     */
    @Test
    void theHintIsAboutThePointTheSentenceNames() {
        assertInstanceOf(ExampleMessage.ARowOnTheLineTellsTwoRulesApart.class,
                theOneAt("100").notes().get(0).said(),
                "a row on the line is what the ON point is for");
        assertInstanceOf(ExampleMessage.ARowPastTheLineShowsWhereTheRuleStops.class,
                theOneAt("0").notes().get(0).said(),
                "a row one step outside it is the other half of the pair");
    }

    /** The one E1916 whose sentence carries that value, which is what names the border's point. */
    private static Diagnostic theOneAt(String value) {
        List<Diagnostic> found = new ArrayList<>();
        for (Diagnostic d : WARNED) {
            if ("E1916".equals(d.code()) && value.equals(d.values().get("value"))) {
                found.add(d);
            }
        }
        assertEquals(1, found.size(), () -> "one point is at " + value + ": " + found);
        return found.get(0);
    }

    private static final List<Diagnostic> WARNED = warnings();

    private static List<Diagnostic> warnings() {
        Compilation compilation = Compilation.ofSource(MODULE, "Main");
        compilation.measure(Adequacy.Asked.warningsAt(Adequacy.Level.ALL));
        compilation.answerEverything();
        List<Diagnostic> out = new ArrayList<>();
        for (Db.Found found : compilation.db().allReports()) {
            if (!found.report().isError()) {
                out.add(found.report().diagnostic());
            }
        }
        assertTrue(out.stream().anyMatch(d -> "E1916".equals(d.code())),
                () -> "no border went unmet: " + out);
        return out;
    }
}
