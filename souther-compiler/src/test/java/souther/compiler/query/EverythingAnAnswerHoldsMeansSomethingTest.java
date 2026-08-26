package souther.compiler.query;

import souther.compiler.conformance.ConformanceCorpus;
import souther.compiler.report.AdequacyReport;
import souther.compiler.diag.SourceNameResolver;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Everything a store holds means something by {@code equals}, and what does not is written down.
 *
 * <p>What an edit costs rests on an answer that means what the last one meant coming out equal to
 * it. One object under an answer that compares by address is enough to lose that: the answer above
 * it can never equal its own recomputation, so every key that read it runs again on every revision
 * over a model nobody edited. Nothing else here sees that happen — every check stays green and every
 * reader of the answer runs forever.
 *
 * <p><b>Both detectors over both scenarios.</b> The two walks see different things and neither is
 * the other's superset, so the register under them is worth what both are worth together. Run over
 * different inputs, a difference between them would be a difference of stimulus as much as of
 * detector, and no reading of the register could tell which. So the scenarios are the axis and the
 * detectors are applied across all of it.
 *
 * <p>The scenarios are two because an answer is two things. {@code Answer} is what a question came
 * to and what the compile said getting there, and {@code Db} compares both — so a corpus of models
 * nothing is said about exercises one half of every answer in the store.
 */
class EverythingAnAnswerHoldsMeansSomethingTest {

    /**
     * A module the compiler has something to say about.
     *
     * <p>What is wanted is an answer whose reports are not empty, and a warning rather than an error
     * is what puts one there without taking anything else away: a module with a mistake in it is
     * still answered about, and it is answered about less — the questions past the mistake come back
     * absent, and the places they hold go unvisited. So the model is one nothing is wrong with except
     * a name it brought in and never used.
     *
     * <p>Which diagnostic it is does not matter, and the register says so: what a report holds sits
     * in the half of an answer every answer has, so it is one place whichever question happened to
     * speak.
     */
    private static final String SPOKEN_ABOUT = """
            module m.spoken

            import Bool ( not )

            data R = { a: Int }

            behavior f : (r: R) -> Int
            let f (r) = r.a

            example f
                | "one" : (R { a = 1 }) -> 1
            """;

    /** One compilation of one scenario, analysed the way that scenario is analysed. */
    private static List<Db> storesOf(AnswerClosure.Scenario scenario) {
        List<Db> out = new ArrayList<>();
        switch (scenario) {
            case VALID_CORPUS -> ConformanceCorpus.all()
                    .forEach(corpus -> out.add(corpus.analyse().compilation().db()));
            case A_MODULE_SPOKEN_ABOUT -> {
                Compilation compilation = Compilation.ofSource(SPOKEN_ABOUT, "Main");
                compilation.measure(Adequacy.Asked.fullReport());
                compilation.answerEverything();
                AdequacyReport.of(compilation).json(SourceNameResolver.identity());
                out.add(compilation.db());
            }
        }
        return out;
    }

    /**
     * Every place a detector met something, which detector met it where, and what got in the way.
     *
     * @param asDifferently questions the two stores were not both asked, which is the ground the
     *                      comparison stands on rather than something it can report on
     */
    private record Met(Map<Locus.Place, Set<String>> byPlace, Set<String> fellShort,
                       Map<Locus.Place, Set<String>> differentThings, int visited) {}

    private static Met met() {
        Map<Locus.Place, Set<String>> byPlace = new TreeMap<>();
        Map<Locus.Place, Set<String>> differentThings = new TreeMap<>();
        Set<String> fellShort = new TreeSet<>();
        int visited = 0;
        for (AnswerClosure.Scenario scenario : AnswerClosure.Scenario.values()) {
            for (Db one : storesOf(scenario)) {
                AnswerWalk.Walked walked = AnswerWalk.of(one);
                visited += walked.visited();
                List<AnswerWalk.Found> found = switch (walked.covered()) {
                    case Covered.Whole<AnswerWalk.Found>(List<AnswerWalk.Found> all) -> all;
                    case Covered.Partly<AnswerWalk.Found>(List<AnswerWalk.Found> all,
                            List<Gap> gaps) -> {
                        gaps.forEach(each -> fellShort.add(each + " in " + scenario));
                        yield all;
                    }
                };
                found.forEach(each -> byPlace
                        .computeIfAbsent(each.place(), _ -> new TreeSet<>())
                        .add(new AnswerClosure.Observation(
                                AnswerClosure.Detector.ONE_ANSWER_WALKED, scenario).toString()));
            }
            // And the same scenario compiled twice, which is what the other detector needs.
            List<Db> first = storesOf(scenario);
            List<Db> again = storesOf(scenario);
            for (int i = 0; i < first.size(); i++) {
                List<TwoStores.Found> found = switch (TwoStores.compared(first.get(i), again.get(i))) {
                    case Covered.Whole<TwoStores.Found>(List<TwoStores.Found> all) -> all;
                    case Covered.Partly<TwoStores.Found>(List<TwoStores.Found> all,
                            List<Gap> gaps) -> {
                        gaps.forEach(each -> fellShort.add(each + " in " + scenario));
                        yield all;
                    }
                };
                for (TwoStores.Found each : found) {
                    if (each.kind() == Divergence.Kind.DIFFERENT_THINGS) {
                        differentThings.computeIfAbsent(each.place(), _ -> new TreeSet<>())
                                .add(scenario.toString());
                        continue;
                    }
                    byPlace.computeIfAbsent(each.place(), _ -> new TreeSet<>())
                            .add(new AnswerClosure.Observation(
                                    AnswerClosure.Detector.TWO_ANSWERS_COMPARED,
                                    scenario).toString());
                }
            }
        }
        return new Met(byPlace, fellShort, differentThings, visited);
    }

    /**
     * A walk that stopped is asked about before anything it found is.
     *
     * <p>What was found is the whole of what is there only where the walk reached the end of it, so a
     * register agreeing with a walk that gave up somewhere agrees about less than it names.
     */
    @Test
    void bothDetectorsGetToTheEndOfBothScenarios() {
        Met met = met();

        // What an answer was built from is what an edit is absorbed by, so which questions a
        // compile reaches is as much what it did as what it said: two stores over one input
        // reaching different graphs would mean the dependencies recorded in one are not the ones
        // the other would keep. Asked of every scenario, because every scenario is compiled twice.
        assertEquals(Set.of(), met.fellShort(),
                "somewhere a search of the answers fell short of what it was asked to cover");
        assertEquals(Map.of(), met.differentThings(),
                "one input compiled twice answered two different things, which no equality can fix");
    }

    /**
     * And the walk reaches the answers this is about.
     *
     * <p>The control the two assertions below need. Every object a walk visits passing says nothing
     * while the objects worth asking are not among them, and a measure that came to an absence — an
     * arm carrying a proof and no numbers — is the shape where identity is easiest to leave in
     * place.
     */
    @Test
    void theWalkReachesTheAnswersThisIsAbout() {
        int visited = 0;
        Set<String> classes = new TreeSet<>();
        for (AnswerClosure.Scenario scenario : AnswerClosure.Scenario.values()) {
            for (Db one : storesOf(scenario)) {
                AnswerWalk.Walked walked = AnswerWalk.of(one);
                visited += walked.visited();
                classes.addAll(walked.classes());
            }
        }

        int reached = visited;
        org.junit.jupiter.api.Assertions.assertTrue(visited > 1000,
                () -> "a walk that reached " + reached + " objects is not reaching the answers"
                        + " this is about");
        org.junit.jupiter.api.Assertions.assertTrue(
                classes.contains(Measurement.NotApplicable.class.getName()),
                () -> "no measure came to an absence, over " + classes.size() + " classes");
    }

    /** And what they found is the places written down, and no others. */
    @Test
    void theOnlyThingsThatMeanNothingAreTheOnesWrittenDown() {
        Met met = met();
        Map<Locus.Place, String> reasons = AnswerClosure.reasons();

        assertEquals(AnswerClosure.places(), met.byPlace().keySet(),
                () -> "a place in an answer holding something that means nothing by equals. "
                        + "What each written-down place is: " + reasons);
    }

    /**
     * And each is met by the detectors and scenarios written down beside it.
     *
     * <p>Its own sentence rather than a line of the one above. A detector that stopped finding
     * something the other still finds leaves the places exactly as they were, so a register of
     * places alone cannot tell a fixed defect from a blinded detector.
     */
    @Test
    void andEachIsMetByWhatIsWrittenDownBesideIt() {
        Met met = met();

        assertEquals(new LinkedHashMap<>(AnswerClosure.observations()),
                new LinkedHashMap<>(met.byPlace()),
                "who meets each of them");
    }
}
