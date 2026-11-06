package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.meaning.WhereEachLineDecides;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A weekday between Monday and Friday written as its two bounds, {@code Int.floorMod(d, 7) >= 1 &&
 * Int.floorMod(d, 7) <= 5}, and as one comparison of the remainder moved by one,
 * {@code Int.floorMod(d - 1, 7) < 5}, cuts the weekday of the first candidate at the same whole
 * numbers: the two writings of a search over candidates draw the same lines.
 *
 * <p>Each candidate's remainder is read as comparisons of the first's, {@code Int.floorMod(base,
 * 7)}, against numbers moved round the divisor, and one writing says a cut as above a number where
 * the other says it as at least the next. No whole number stands between the two, so they are one
 * line, which is held here against the rows: two lines are one where no whole value of what they
 * are over tells them apart.
 *
 * <p>Of the lines, and not of how many ways the cases they decide in are chosen in. Those are
 * counted over the statement as written, and the two writings put their comparisons together
 * differently.
 */
class AWeekdayWrittenAsOneRemainderDrawsTheLinesOfItsTwoBoundsTest {

    private static final String TWO_BOUNDS = "Int.floorMod(d, 7) >= 1 && Int.floorMod(d, 7) <= 5";
    private static final String ONE_REMAINDER = "Int.floorMod(d - 1, 7) < 5";

    /** The lines of {@code g} searching {@code candidates} for a weekday not the given one. */
    private static List<Proposition.Compared> lines(String weekday, int candidates) {
        String source = """
                module demo exposing (g)

                let first (base: Int, h: Int): Int = Option.withDefault(base,
                    List.find(d -> WEEKDAY && Bool.not(d == h), List.map(k -> base + k, [KS])))

                behavior g : (base: Int, h: Int) -> Bool
                let g (base, h) = Bool.not(first(base, h) == base)
                """.replace("WEEKDAY", weekday).replace("KS", IntStream.range(0, candidates)
                .mapToObj(Integer::toString).collect(Collectors.joining(", ")));
        Compilation compilation = Compilation.ofSource(source, "Main");
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("demo")).value();
        assertNotNull(checked, "the model compiles: " + compilation.errors());
        AnalysisBody analysis = checked.analysisBodies().get("g");
        RuleReadingSource rules = RuleReadings.of(compilation, "demo");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs("demo")).value().get("g");
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                inputs.dependencies());
        Proposition stated = Pullback.ofATruth(Core.withoutStanding(analysis.core()), reads,
                inputs.reading(rules), Optional.empty()).proposition();
        List<Proposition.Compared> out = new ArrayList<>();
        for (WhereEachLineDecides.Decides each : WhereEachLineDecides.in(stated,
                inputs.reading(rules).quantities()::countsWhole)) {
            out.add(each.line());
        }
        return out;
    }

    /** Whether {@code line} holds where each of what it is over is {@code at}. */
    private static boolean holds(Proposition.Compared line, Map<Quantity, Integer> at) {
        Relation.Affine affine = (Relation.Affine) line.relation();
        ExactAnswer<ExactRatio> value = new ExactAnswer.Held<>(affine.form().constant());
        for (Map.Entry<Quantity, ExactRatio> each : affine.form().coefs().entrySet()) {
            ExactRatio weighed = ExactRatio.of(at.get(each.getKey()));
            value = value.flatMap(sum -> each.getValue().times(weighed)
                    .flatMap(sum::plus));
        }
        if (!(value instanceof ExactAnswer.Held<ExactRatio>(ExactRatio held))) {
            throw new AssertionError("a small whole number of a line is held: " + line);
        }
        return affine.proposition().holds(held.signum()) == line.holds();
    }

    /** Whether some whole values, small enough to stand on either side of each line, tell the two
     *  apart. */
    private static boolean toldApart(Proposition.Compared one, Proposition.Compared other) {
        Map<Quantity, ExactRatio> over = ((Relation.Affine) one.relation()).form().coefs();
        if (!over.keySet().equals(((Relation.Affine) other.relation()).form().coefs().keySet())) {
            return true;
        }
        List<Quantity> atoms = new ArrayList<>(over.keySet());
        int[] at = new int[atoms.size()];
        Arrays.fill(at, -9);
        while (true) {
            Map<Quantity, Integer> row = new HashMap<>();
            for (int i = 0; i < atoms.size(); i++) {
                row.put(atoms.get(i), at[i]);
            }
            if (holds(one, row) != holds(other, row)) {
                return true;
            }
            int i = 0;
            while (i < at.length && at[i] == 9) {
                at[i++] = -9;
            }
            if (i == at.length) {
                return false;
            }
            at[i]++;
        }
    }

    @Test
    void theTwoWritingsDrawTheSameLines() {
        for (int candidates : new int[] {2, 3}) {
            List<Proposition.Compared> bounds = lines(TWO_BOUNDS, candidates);
            List<Proposition.Compared> remainder = lines(ONE_REMAINDER, candidates);
            assertTrue(bounds.size() > 2, "the search draws lines: " + bounds);
            for (List<List<Proposition.Compared>> pair : List.of(List.of(bounds, remainder),
                    List.of(remainder, bounds))) {
                for (Proposition.Compared line : pair.getFirst()) {
                    assertTrue(pair.getLast().stream().anyMatch(other -> !toldApart(line, other)),
                            candidates + ": " + line + " among " + pair.getLast());
                }
            }
            assertEquals(bounds.size(), remainder.size(), candidates + ": " + bounds + " and "
                    + remainder);
        }
    }
}
