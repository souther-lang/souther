package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value its own type refuses is refused in every value holding it, and a search composes none of
 * those.
 *
 * <p>A position of a format-checked type is offered a value meeting the format and one that does
 * not, the second as a proposal the decoder answers. Walked as a product, the second would be
 * composed beside every combination of the other positions, and nine such fields come to more
 * assignments than the bound — all of them spent on values their own fields refuse.
 *
 * <p>Here the parameter is refused whatever it holds, so what is left to see is what the search
 * composed on the way to finding that out. The same search with nothing said about the values on
 * their own is the control: it is what shows the fixture offers the refused values at all.
 *
 * <p>Asked of both searches that compose a parameter: the one for a class nothing reaches, and the
 * one for a point a term is to stand at. The second hands the search a check of its own, which is
 * where what a value's type says could be dropped on the way.
 */
class AValueItsOwnTypeRefusesIsNotComposedBesideTheOthersTest {

    private static final String NINE_CODES = """
            module example.codes

            data Ok
            data Yes
            data No
            data Flag = Yes | No
            data Code = String
                invariant String.matches("[A-Z]{3}", value)
            data Amount = Int
                invariant value >= 0 && value <= 100

            data Codes = { a: Code, b: Code, c: Code, d: Code, e: Code, f: Code, g: Code, h: Code,
                           i: Code, flag: Flag, cost: Amount }

            behavior take : (codes: Codes) -> Ok
            """;

    private static final Pattern UNFORMATTED_CODE =
            Pattern.compile("Code\\(\"(?![A-Z]{3}\")[^\"]*\"\\)");

    /** Refuses every parameter it is asked about, and writes down what it was asked about. */
    private static class RefusingEverything implements Generator.CandidateCheck {

        final List<String> composed = new ArrayList<>();

        @Override
        public Built build(int parameter, FixtureTemplate candidate) {
            composed.add(candidate.text());
            return new Built.Refused("not any of them");
        }
    }

    /** The same, with a {@code Code} that does not meet its format refused on its own. */
    private static final class RefusingEverythingAndSayingWhatACodeRefuses
            extends RefusingEverything {

        @Override
        public Admissibility admissibility(Type type, FixtureTemplate candidate) {
            if (!Type.show(type).equals("Code")) {
                return Admissibility.UNKNOWN;
            }
            return candidate.text().matches("Code\\(\"[A-Z]{3}\"\\)")
                    ? Admissibility.ADMITTED : Admissibility.REFUSED;
        }
    }

    @Test
    void aSearchForAClassComposesNoValueItsOwnTypeRefused() {
        RefusingEverything control = new RefusingEverything();
        GenerationFixtures.fill(subject(), List.of(), control, Budgets.generation());
        RefusingEverythingAndSayingWhatACodeRefuses saying =
                new RefusingEverythingAndSayingWhatACodeRefuses();
        GenerationFixtures.fill(subject(), List.of(), saying, Budgets.generation());

        composedNoneOfThem(control, saying);
    }

    @Test
    void aSearchForAPointComposesNoValueItsOwnTypeRefused() {
        RefusingEverything control = new RefusingEverything();
        probeAt(Count.of(100), control);
        RefusingEverythingAndSayingWhatACodeRefuses saying =
                new RefusingEverythingAndSayingWhatACodeRefuses();
        probeAt(Count.of(100), saying);

        composedNoneOfThem(control, saying);
    }

    private static void composedNoneOfThem(RefusingEverything control,
                                           RefusingEverything saying) {
        assertFalse(unformatted(control.composed).isEmpty(),
                "the fixture offers a code that does not meet the format: " + control.composed);
        assertFalse(saying.composed.isEmpty(), "the search composed something");
        assertEquals(List.of(), unformatted(saying.composed),
                "no assignment holding a code its type refused is composed");
        assertTrue(saying.composed.size() < control.composed.size(),
                "and the search composed less: " + saying.composed.size() + " against "
                        + control.composed.size());
    }

    private static List<String> unformatted(List<String> composed) {
        return composed.stream().filter(each -> UNFORMATTED_CODE.matcher(each).find()).toList();
    }

    private record Read(MeasuredInput subject, InputDomain domain, RuleReadingSource rules,
                        Partitions.Partitioning partitioning) {}

    private static Read read() {
        Compilation compilation = Compilation.ofSource(NINE_CODES, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        InputDomain domain =
                compilation.db().ask(new Adequacy.Inputs(module)).value().get("take");
        assertNotNull(domain, "the model under test compiles");
        Partitions.Partitioning partitioning =
                Partitions.of("take", domain.reading(rules), ReadAs.THE_COMPILATION_DOES);
        return new Read(MeasuredInput.of("take", domain.reading(rules), partitioning), domain,
                rules, partitioning);
    }

    private static MeasuredInput subject() {
        return read().subject();
    }

    private static void probeAt(Place at, Generator.CandidateCheck check) {
        Read read = read();
        Axis axis = read.partitioning().axes().stream()
                .filter(each -> each.path().toString().equals("codes.cost"))
                .findFirst().orElseThrow();
        Generator.probeFixing(read.subject(), "codes.cost = " + at,
                Map.of(new RealizationTarget.AtOnePosition(axis.term()), at),
                NumbersAskedFor.of(LevelRegion.point(new Level.OnACarrier(
                        read.domain().quantities(read.rules()).ordersOf(axis.term()).answered(),
                        at))),
                Reachability.untouched(read.domain().quantities(read.rules()).region()), check);
    }
}
