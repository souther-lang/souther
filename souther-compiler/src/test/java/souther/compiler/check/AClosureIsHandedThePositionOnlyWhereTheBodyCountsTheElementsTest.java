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

    /**
     * A helper written the way {@code mapIndexed} is, under {@code name}: a walk carrying a count
     * from {@code seed}, whose step adds {@code applied} to what it has built and answers
     * {@code next}.
     */
    private static String counting(String name, String applied, String next, String seed) {
        return """
                let %s (f: (Int, 'a) -> 'b, xs: List<'a>): List<'b> = {
                    let (_, out) = List.fold(
                        (acc, x) -> {
                            let (i, ys) = acc
                            let mapped = ys ++ %s
                            %s
                        },
                        %s,
                        xs
                    )
                    out
                }
                """.formatted(name, applied, next, seed);
    }

    /**
     * What each operation hands its closure, of the library as shipped with every helper this
     * asks about declared beside {@code mapIndexed}: one library read once, since reading one
     * binds every fact the library states.
     */
    private static final Map<ValueName.Stdlib.Operation, Combinator> READ = read(String.join("\n",
            counting("asWritten", "[f(i, x)]", "(i + 1, mapped)", "(0, [])"),
            counting("fromTheOtherSide", "[f(i, x)]", "(1 + i, mapped)", "(0, [])"),
            counting("fromOne", "[f(i, x)]", "(i + 1, mapped)", "(1, [])"),
            counting("byTwo", "[f(i, x)]", "(i + 2, mapped)", "(0, [])"),
            counting("theNextCount", "[f(i + 1, x)]", "(i + 1, mapped)", "(0, [])"),
            counting("twoSites", "[f(i, x), f(0, x)]", "(i + 1, mapped)", "(0, [])"),
            counting("crossed", "List.map(y -> f(i, y), xs)", "(i + 1, mapped)", "(0, [])"),
            """
            let handedOn (f: (Int, 'a) -> 'b, xs: List<'a>): List<'b> =
                List.mapIndexed((i, x) -> f(i, x), xs)
            """));

    private static Combinator rule(String helper) {
        return READ.get(ValueName.Stdlib.operation("List", helper));
    }

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

    /** Control: a helper written as {@code mapIndexed} is hands the position, and written the
     *  other way round the count is the same count. */
    @Test
    void aCountWrittenEitherWayRoundIsThePosition() {
        assertEquals(0, rule("asWritten").positionParam());
        assertEquals(0, rule("fromTheOtherSide").positionParam());
    }

    /** A count from one, a count by two and the next count handed are no position — though the
     *  element is still the element. */
    @Test
    void aBodyThatDoesNotCountFromNoughtOneByOneHandsNone() {
        for (String helper : List.of("fromOne", "byTwo", "theNextCount")) {
            assertEquals(Combinator.NO_POSITION, rule(helper).positionParam(), helper);
            assertEquals(1, rule(helper).elementParam(), helper);
        }
    }

    /** A closure handed the count where it is applied once and a number where it is applied
     *  again is handed something other than the position on some application. */
    @Test
    void aClosureHandedTheCountAtOnePlaceAndNotAtAnotherIsHandedNone() {
        assertEquals(Combinator.NO_POSITION, rule("twoSites").positionParam());
    }

    /**
     * A count of one walk's elements is the position of the element that walk's step is handed,
     * and of no element another walk hands — even one walking the same list.
     *
     * <p>Here the closure is applied inside a walk nested in the step, beside that inner walk's
     * element and the outer walk's count: it is handed every element of {@code xs} at each outer
     * element, all at the same count.
     */
    @Test
    void aCountOfOneWalkIsNoPositionOfTheElementsAnotherWalkHands() {
        assertEquals(Combinator.NO_POSITION, rule("crossed").positionParam());
    }

    /** A closure handed on to an operation that hands its closure the position, inside a closure
     *  of the operation's own, is handed the position where that closure hands it on. */
    @Test
    void aClosureHandedOnBesideThePositionIsHandedThePosition() {
        assertEquals(0, rule("handedOn").positionParam());
        assertEquals(1, rule("handedOn").elementParam());
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

    /** What each operation of the library hands its closure, with {@code helpers} declared after
     *  the rest of the module {@code mapIndexed} is in. */
    private static Map<ValueName.Stdlib.Operation, Combinator> read(String helpers) {
        AtomicBoolean added = new AtomicBoolean();
        Stdlib stdlib = StdlibLoader.load(text -> {
            if (!text.contains("let mapIndexed ")) {
                return text;
            }
            added.set(true);
            return text + "\n" + helpers;
        });
        assertTrue(added.get(), "the helpers are declared in the module mapIndexed is in");
        return Combinators.read(stdlib, OperationFactBinder.bindAll(stdlib));
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
