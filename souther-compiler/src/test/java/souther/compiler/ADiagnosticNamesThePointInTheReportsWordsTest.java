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

        assertInstanceOf(ExampleMessage.NoRowIsAtThePointOfTheLineAConstructDrew.class, said.said(),
                () -> "a fork has no name, so its sentence says the construct: " + said.said());
        assertEquals("ON", said.values().get("point"),
                () -> "the report calls this the ON point: " + said.values());
    }

    /** And the point one step outside a clause's line, which is the other role and the other origin. */
    @Test
    void aClausesOffPointSaysItIsTheOffPoint() {
        Diagnostic said = theOneAt("0");

        assertInstanceOf(ExampleMessage.NoRowIsAtThePointOfTheLineARuleDrew.class, said.said(),
                () -> "a clause has a name, so its sentence names the rule: " + said.said());
        assertEquals("OFF", said.values().get("point"),
                () -> "the report calls this the OFF point: " + said.values());
    }

    /**
     * The hint is keyed on the role, and the open border is what says so.
     *
     * <p>Which point carries the line's own value turns on the border being closed or open: the
     * guard's line is closed, so its {@code ON} point is the value it was written with, and the
     * clause's is open, so its {@code OFF} point is. A hint about where the value falls against the
     * line would therefore be inverted on one of the two borders while reading correctly on the
     * other — and the four points here are two of each, so a hint keyed on the wrong axis cannot
     * pass this.
     */
    @Test
    void everyOnPointGetsTheInsideHintAndEveryOffPointTheOutsideOne() {
        for (String inside : List.of("100", "1")) {
            assertInstanceOf(ExampleMessage.ARowJustInsideShowsTheBorderIsNotFurtherIn.class,
                    theOneAt(inside).notes().get(0).said(),
                    () -> "the ON point at " + inside + ": " + theOneAt(inside).said());
        }
        for (String outside : List.of("101", "0")) {
            assertInstanceOf(ExampleMessage.ARowJustOutsideShowsTheBorderIsNotFurtherOut.class,
                    theOneAt(outside).notes().get(0).said(),
                    () -> "the OFF point at " + outside + ": " + theOneAt(outside).said());
        }
    }

    /** And the four are two roles on two borders, which is what makes the loop above a control. */
    @Test
    void theFourPointsAreTwoRolesOnAClosedBorderAndAnOpenOne() {
        assertEquals(List.of("ON", "OFF", "OFF", "ON"),
                List.of("100", "101", "0", "1").stream()
                        .map(at -> theOneAt(at).values().get("point")).toList(),
                "the closed border is at its ON point and the open one at its OFF point");
    }

    /** The one E1916 whose sentence carries that value, which is what names the border's point. */
    private static Diagnostic theOneAt(String value) {
        List<Diagnostic> found = new ArrayList<>();
        for (Diagnostic d : WARNED) {
            // Asked of what the readings say, because that is where a value is written. The
            // sentence names which point and which rule and no quantity: writing where the point
            // is takes a quantity, and a quantity belongs to the position that read the line.
            if ("E1916".equals(d.code()) && d.notes().stream()
                    .anyMatch(note -> note.said()
                            instanceof ExampleMessage.TheLineAsReadAt(var _, var asks)
                            && asks.equals("= " + value))) {
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
