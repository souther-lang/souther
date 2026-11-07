package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermPath;
import souther.compiler.query.Compilation;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A total taken over a run is read across every run of values it is made of — the place it is
 * read from and, for a join, the map it is joined to — and nothing else. Whether it turns on the
 * elements of a container ({@link AStatementAtARow#readOf}), and whether it is read off nothing
 * but them ({@link NumericTerm#isReadOffOnlyTheElementsOf}), is what those runs say, worked out
 * here from the runs each source is written over and not from the source.
 */
class WhatATotalOfARunReadsIsEveryRunItIsReadAcrossTest {

    private static final List<TermPath> CONTAINERS =
            List.of(TermPath.of("a"), TermPath.of("b"), TermPath.of("c"));

    /** A source and the containers whose elements each of its runs is, as written here. */
    private record Written(RunSource source, List<TermPath> runs) {}

    private static TermPath valuesOf(String container) {
        return TermPath.of(container).element().then("v");
    }

    private static List<Written> sources() {
        return List.of(
                new Written(new RunSource.ProjectedOccurrences(valuesOf("a")),
                        List.of(TermPath.of("a"))),
                new Written(new RunSource.ProjectedOccurrences(valuesOf("b")),
                        List.of(TermPath.of("b"))),
                new Written(new RunSource.JoinedOccurrences(valuesOf("a"), valuesOf("b")),
                        List.of(TermPath.of("a"), TermPath.of("b"))),
                new Written(new RunSource.JoinedOccurrences(valuesOf("b"), valuesOf("a")),
                        List.of(TermPath.of("a"), TermPath.of("b"))));
    }

    @Test
    void aTotalOfARunReadsEveryRunItIsMadeOf() {
        Compilation compilation = Compilation.ofSource("""
                module probe

                data Item = { v: Int }

                data Taken

                behavior take : (a: List<Item>, b: List<Item>, c: List<Item>) -> Taken
                """, "Main");
        RuleReadingSource rules = RuleReadings.of(compilation, compilation.modules().get(0));
        ValueName.Stdlib sum = ValueName.Stdlib.operation("List", "sum");
        for (Written written : sources()) {
            NumericTerm total = NumericTerm.TakenOver.of(sum, written.source(), Type.Prim.INT,
                    rules.inners(), rules.symbols());
            assertNotNull(total, written::toString);
            for (TermPath container : CONTAINERS) {
                boolean acrossIt = written.runs().contains(container);
                assertEquals(acrossIt ? AStatementAtARow.TurnsOn.OTHER_ELEMENTS
                                : AStatementAtARow.TurnsOn.THE_ELEMENT,
                        AStatementAtARow.readOf(total, container, null, Optional.empty())
                                .turnsOn(),
                        () -> total + " among the elements of " + container);
                assertEquals(written.runs().equals(List.of(container)),
                        total.isReadOffOnlyTheElementsOf(container),
                        () -> total + " read off the elements of " + container + " alone");
            }
        }
    }
}
