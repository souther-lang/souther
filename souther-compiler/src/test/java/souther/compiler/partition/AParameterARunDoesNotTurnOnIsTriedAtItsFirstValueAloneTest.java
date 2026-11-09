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
import souther.compiler.observe.Figure;
import souther.compiler.observe.ObservedValue;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.IntPredicate;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A parameter a run of the behavior does not turn on is tried with its first value alone, so the
 * rows a search tries are spent on the parameters that can decide what it looks for. And how many
 * parameters there are is no depth of anything: rows over a great many of them are walked without
 * a call for each.
 */
class AParameterARunDoesNotTurnOnIsTriedAtItsFirstValueAloneTest {

    private static final String FLAGS = """
            module example.m

            data On
            data Off
            data Flag = On | Off

            behavior f : (a: Flag, b: Flag, c: Flag) -> Flag

            let f (a, b, c) = a
            """;

    private static List<List<RowSearch.Built>> triedWith(IntPredicate atFirst) {
        Compilation compilation = Compilation.ofSource(FLAGS, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingContext context =
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        InputDomain domain = InputDomain.of(sigs.get("f"), context,
                TypeCardinality.Counts.workedOutIn(context), Membership.none());
        Partitions.Partitioning partitioning =
                Partitions.of("f", domain.reading(rules), ReadAs.THE_COMPILATION_DOES);
        MeasuredInput subject = MeasuredInput.of("f", domain.reading(rules), partitioning);
        List<List<FixtureTemplate>> named = new ArrayList<>();
        subject.types().forEach(_ -> named.add(
                List.of(FixtureTemplate.string("p"), FixtureTemplate.string("q"))));
        return RowSearch.tried(subject.types(), named, List.of(), subject.types()::get,
                _ -> null, atFirst, subject.ruleReading(),
                (_, fixture) -> Optional.of(new ObservedValue.Text(fixture.text())),
                new HashSet<>());
    }

    @Test
    void aParameterTheRunDoesNotTurnOnHasOneValueAndTheOthersKeepTheirs() {
        List<List<RowSearch.Built>> every = triedWith(_ -> false);
        List<List<RowSearch.Built>> standing = triedWith(at -> at != 0);

        assertTrue(every.get(1).size() > 1, "a parameter has more than one value to try");
        assertEquals(every.get(0).size(), standing.get(0).size());
        assertEquals(1, standing.get(1).size());
        assertEquals(1, standing.get(2).size());
        assertEquals(every.get(1).getFirst(), standing.get(1).getFirst());
    }

    @Test
    void theRowsTriedAreOnlyThoseOverTheParametersThatCanDecide() {
        List<List<RowSearch.Built>> every = triedWith(_ -> false);
        List<List<RowSearch.Built>> standing = triedWith(at -> at != 0);

        assertEquals(every.get(0).size() * every.get(1).size() * every.get(2).size(),
                RowSearch.rowsOf(every, new HashSet<>()).size());
        assertEquals(standing.get(0).size(),
                RowSearch.rowsOf(standing, new HashSet<>()).size());
    }

    @Test
    void rowsOverAGreatManyParametersAreNoDepthOfTheStack() {
        List<RowSearch.Built> one = List.of(new RowSearch.Built(FixtureTemplate.string("v"), null));
        List<List<RowSearch.Built>> each = new ArrayList<>();
        for (int i = 0; i < 50_000; i++) {
            each.add(one);
        }
        Set<Figure> stopped = new HashSet<>();

        List<List<RowSearch.Built>> rows = RowSearch.rowsOf(each, stopped);

        assertEquals(1, rows.size());
        assertTrue(stopped.isEmpty());
    }
}
