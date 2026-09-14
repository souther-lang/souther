package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.PointRole;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a build measures, and what somebody has to ask for.
 *
 * <p>Composing a value at a boundary puts it through the module's own decoders and costs a decoder
 * run for each point it settles. That is work, and this holds the line between the two things it
 * could be: a measurement everybody pays for, or a request whoever wants it pays for.
 *
 * <p>Asked of a compilation rather than of the source of one. Whether a query reads a dial is a
 * property of what it does when it runs, and a check that read the text for the name of the dial
 * would pass the day somebody spelled it differently.
 */
class ASearchIsAskedForAndAMeasurementIsNotTest {

    private static final String MODULE = "example.edges";

    private static final String MODEL = """
            module example.edges

            data Request = { rank: Int, cost: Int }

            data Auto
            data Manual

            behavior keep : (r: Request) -> Auto | Manual
            let keep (r) =
                if r.rank >= 0 && r.cost <= 100000 then Auto else Manual

            example keep
                | "one row" : (Request { rank = 1, cost = 2 }) -> Auto
            """;

    private static Compilation measured(Adequacy.Level level) {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.reportOnly(level));
        compilation.answerEverything();
        // What a report reads, which is what puts the questions this is about. A compile answers it
        // when something asks for the report, and nothing here is printing one.
        assertNotNull(compilation.db().ask(new Adequacy.Coverage(MODULE)).value(),
                "the model under test compiles");
        return compilation;
    }

    /** Every question one compilation put, by the name of the key that asks it. */
    private static Set<String> asked(Compilation compilation) {
        Set<String> out = new TreeSet<>();
        compilation.db().everyAnswer().keySet()
                .forEach(key -> out.add(key.getClass().getSimpleName()));
        return out;
    }

    /**
     * A build that measures does not compose, whatever else it measures.
     *
     * <p>The line is which question is put and not what the answer to one does. A search that read
     * the level to find out how much to compose would leave a caller who wanted the values with
     * nowhere to say so, and one who did not still paying for the decision to be made inside it.
     */
    @Test
    void measuringABoundaryDoesNotComposeAValueAtIt() {
        Set<String> witness = asked(measured(Adequacy.Level.WITNESS));
        assertTrue(witness.contains("Boundaries"), "the lines are measured: " + witness);
        assertFalse(witness.contains("BoundarySearch"),
                "and nothing composed a value at one: " + witness);

        Set<String> all = asked(measured(Adequacy.Level.ALL));
        assertTrue(all.contains("BoundarySearch"),
                "a build held to the arms asks for the values: " + all);
    }

    /**
     * And a search adds to the measurement rather than making one of its own.
     *
     * <p>Every border, every demand, every coverage and every reading of what the rules prove comes
     * through untouched; the only thing that moves is the attempt, and only at the points the
     * measurement itself says are worth one. So the two answers are ordered rather than rival, and
     * a verdict read off the evidence can gain a witness and never lose one.
     */
    @Test
    void whatASearchAddsIsTheAttemptAndNothingElse() {
        Compilation compilation = measured(Adequacy.Level.ALL);
        List<BorderAssessment> measured =
                compilation.db().ask(new Adequacy.Boundaries(MODULE, "keep")).value();
        List<BorderAssessment> searched =
                compilation.db().ask(new Adequacy.BoundarySearch(MODULE, "keep")).value();
        assertNotNull(measured, "the model under test compiles");
        assertNotNull(searched, "and its lines were searched");
        assertEquals(measured.size(), searched.size(), "the same lines");
        assertFalse(measured.isEmpty(), "the model draws lines to be about");

        boolean anySearched = false;
        for (int i = 0; i < measured.size(); i++) {
            BorderAssessment before = measured.get(i);
            BorderAssessment after = searched.get(i);
            assertEquals(before.border(), after.border(), "the line itself");
            for (PointRole role : PointRole.values()) {
                ItemAssessment was = before.at(role);
                ItemAssessment is = after.at(role);
                if (!(was instanceof ItemAssessment.Owed owed)) {
                    assertEquals(was, is, "a point nothing is owed at");
                    continue;
                }
                ItemAssessment.Owed now = (ItemAssessment.Owed) is;
                assertEquals(owed.criterion(), now.criterion(), "what the point asks of a row");
                assertEquals(owed.coverage(), now.coverage(), "what the rows came to");
                assertEquals(owed.projection(), now.projection(),
                        "what reading the rules established on its own");
                assertFalse(owed.searches().ran(), "nothing was searched for while measuring");
                if (owed.worthSearching()) {
                    assertTrue(now.searches().ran(), "and a point worth searching was searched");
                    anySearched = true;
                } else {
                    assertFalse(now.searches().ran(),
                            "a point not worth searching was left alone");
                }
                // Nothing a search does is evidence against a point, so the grounds can only be
                // added to. A superset and not a rank: the grounds are not alternatives, so there is
                // no order to compare them under — and inventing one, which this did, is how a
                // search that replaced a proof with a witness read as a search that strengthened it.
                assertTrue(now.writabilityEvidence().grounds().written()
                                .containsAll(owed.writabilityEvidence().grounds().written()),
                        "the search took a ground away at " + before.label());
            }
        }
        assertTrue(anySearched, "the model has a point worth searching, or this asserts nothing");
    }

    /**
     * A generation is about the behavior it was asked about.
     *
     * <p>Searching the pair space and composing at the edges is what a generation costs, and asking
     * about one behavior used to have every behavior of the module pay it.
     */
    @Test
    void generatingForOneBehaviorSearchesNoOther() {
        Compilation compilation = Compilation.ofSource(TWO, "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        compilation.answerEverything();
        compilation.db().ask(new Adequacy.Generated("example.two", "first"));

        Map<Key<?>, Answer<?>> answered = compilation.db().everyAnswer();
        Set<String> searched = new TreeSet<>();
        answered.keySet().stream()
                .filter(key -> key instanceof Adequacy.BoundarySearch)
                .map(key -> ((Adequacy.BoundarySearch) key).behavior())
                .forEach(searched::add);
        assertEquals(Set.of("first"), searched,
                "only the behavior that was asked about had its edges composed");
    }

    private static final String TWO = """
            module example.two

            data Request = { rank: Int, cost: Int }

            data Auto
            data Manual

            behavior first : (r: Request) -> Auto | Manual
            let first (r) =
                if r.rank >= 0 then Auto else Manual

            behavior second : (r: Request) -> Auto | Manual
            let second (r) =
                if r.cost <= 100000 then Auto else Manual
            """;
}
