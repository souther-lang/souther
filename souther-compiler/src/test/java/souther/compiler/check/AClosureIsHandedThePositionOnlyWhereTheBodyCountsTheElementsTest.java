package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.semantics.Combinator;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.atomic.AtomicBoolean;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which parameter of a closure an operation hands the element's position on is read off the
 * operation's body, and is what the library computes.
 *
 * <p>Read off the body: a walk carrying a whole number that starts at nought, that every step
 * answers one more of, and that the closure is handed before the step answers the next. So a body
 * counting from one, counting by two, or handing the closure the next count hands it no position,
 * whatever its signature says it could be handed. And what the library computes: each operation
 * said to hand one is run over elements whose total, weighed by the square of where each stands,
 * comes out one way counted from nought in the order written and other ways counted from one or
 * from the end.
 */
class AClosureIsHandedThePositionOnlyWhereTheBodyCountsTheElementsTest {

    private static final ValueName.Stdlib.Operation MAP_INDEXED =
            ValueName.Stdlib.operation("List", "mapIndexed");

    /** The step and the seed of {@code mapIndexed} as the library writes them. */
    private static final String SHIPPED = """
                        let mapped = ys ++ [f(i, x)]
                        (i + 1, mapped)
                    },
                    (0, []),
            """;

    /** Control: the library as shipped hands its position to {@code mapIndexed}'s closure first,
     *  and hands no other closure one. */
    @Test
    void theShippedLibraryHandsThePositionToMapIndexedAlone() {
        Set<String> handing = new TreeSet<>();
        Combinators.all().forEach((operation, rule) -> {
            if (rule.handsAPosition()) {
                handing.add(operation + "@" + rule.positionParam() + "/" + rule.elementParam());
            }
        });
        assertEquals(Set.of("List.mapIndexed@0/1"), handing);
    }

    /** The count written the other way round is the same count. */
    @Test
    void aCountWrittenFromTheOtherSideIsTheSameCount() {
        assertEquals(0, positionHandedBy(SHIPPED.replace("(i + 1, mapped)", "(1 + i, mapped)")));
    }

    /** A count from one, a count by two and the next count handed are no position. */
    @Test
    void aBodyThatDoesNotCountFromNoughtOneByOneHandsNone() {
        assertEquals(Combinator.NO_POSITION,
                positionHandedBy(SHIPPED.replace("(0, []),", "(1, []),")), "from one");
        assertEquals(Combinator.NO_POSITION,
                positionHandedBy(SHIPPED.replace("(i + 1, mapped)", "(i + 2, mapped)")), "by two");
        assertEquals(Combinator.NO_POSITION,
                positionHandedBy(SHIPPED.replace("[f(i, x)]", "[f(i + 1, x)]")),
                "the next count");
    }

    /** A closure handed the count where it is applied once and a number where it is applied
     *  again is handed something other than the position on some application. */
    @Test
    void aClosureHandedTheCountAtOnePlaceAndNotAtAnotherIsHandedNone() {
        assertEquals(Combinator.NO_POSITION,
                positionHandedBy(SHIPPED.replace("[f(i, x)]", "[f(i, x), f(0, x)]")));
    }

    /** Each operation said to hand the position hands where the element stands, from nought. */
    @Test
    void thePositionHandedIsWhereTheElementStandsCountedFromNought() throws Exception {
        List<String> unwritten = new ArrayList<>();
        int ran = 0;
        for (ValueName.Stdlib.Operation operation : Combinators.named()) {
            Combinator rule = Combinators.of(operation);
            Stdlib.Entry entry = DefaultStdlib.get().entry(operation);
            if (!rule.handsAPosition() || entry == null) {
                continue;
            }
            String name = operation.alias() + "." + operation.name();
            // 0·0·5 + 1·1·6 + 2·2·7, where counting from one comes to 92 and from the end to 26.
            String counted = weighed(name, entry.signature(), rule, 34);
            if (counted == null) {
                unwritten.add(name);
                continue;
            }
            assertTrue(HowFarAnOperationAppliesItsClosureIsWhatTheLibraryComputesTest
                    .aborts(counted), name + " counts from nought in the order written");
            for (long otherwise : List.of(92L, 26L)) {
                assertFalse(HowFarAnOperationAppliesItsClosureIsWhatTheLibraryComputesTest
                        .aborts(weighed(name, entry.signature(), rule, otherwise)), name);
            }
            ran++;
        }
        assertEquals(List.of(), unwritten, "an operation whose arguments this cannot write");
        assertTrue(ran > 0, "the run is what is asked, so it has to have asked something");
    }

    /**
     * What the library's {@code mapIndexed}, with its step and seed written {@code as}, hands its
     * position on.
     *
     * <p>Only where the body as shipped was found and rewritten: a rewrite that found nothing
     * would ask the shipped body again, and a variant answering what the shipped one does would
     * say nothing.
     */
    private static int positionHandedBy(String as) {
        AtomicBoolean rewritten = new AtomicBoolean();
        Stdlib stdlib = StdlibLoader.load(text -> {
            if (!text.contains(SHIPPED)) {
                return text;
            }
            rewritten.set(true);
            return text.replace(SHIPPED, as);
        });
        assertTrue(rewritten.get(), "the library writes mapIndexed's step as this test does");
        Map<ValueName.Stdlib.Operation, Combinator> rules =
                Combinators.read(stdlib, OperationFactBinder.bindAll(stdlib));
        return rules.get(MAP_INDEXED).positionParam();
    }

    /**
     * A module running {@code name} over {@code [5, 6, 7]}, its closure answering the element
     * weighed by the square of the position, and aborting exactly where the total of those comes
     * to {@code expected}. Null where an argument is one this does not write.
     */
    private static String weighed(String name, Stdlib.Signature signature, Combinator rule,
                                  long expected) {
        if (!(signature.params().get(rule.closureArg()) instanceof Type.FnOf closure)
                || !(signature.result() instanceof Type.ListOf)) {
            return null;
        }
        List<String> parameters = new ArrayList<>();
        for (int at = 0; at < closure.params().size(); at++) {
            parameters.add("p" + at);
        }
        List<String> arguments = new ArrayList<>();
        for (int at = 0; at < signature.params().size(); at++) {
            if (at == rule.closureArg()) {
                String position = "p" + rule.positionParam();
                arguments.add("(" + String.join(", ", parameters) + ") -> " + position + " * "
                        + position + " * p" + rule.elementParam());
            } else if (at == rule.containerArg()) {
                arguments.add("[5, 6, 7]");
            } else {
                return null;
            }
        }
        return """
                module demo

                data In = { n: Int }
                data Out = { n: Int }

                behavior run : (i: In) -> Out constructs Out
                let run (i) = {
                    let total = List.sum(%s(%s))
                    let applied = Int.floorMod(1, total - %d)
                    Out { n = i.n + applied }
                }
                """.formatted(name, String.join(", ", arguments), expected);
    }
}
