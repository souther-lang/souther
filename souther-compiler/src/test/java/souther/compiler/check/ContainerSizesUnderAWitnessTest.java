package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.abort.GetsPast;
import souther.compiler.core.Core;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.types.ValueName;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a union a walk takes at each element answers on a run whose input sets hold as many as
 * the caller says, read by induction on what the walk carries.
 *
 * <p>The walk is the one a body writes, read off the tree a behavior is checked as; how many the
 * list and each set it holds have is handed in, as a witness would be.
 */
class ContainerSizesUnderAWitnessTest {

    private static final BigInteger HALF_OF_WHAT_A_SET_HOLDS = BigInteger.TWO.pow(30);

    /** The body of {@code run}, taking {@code xs}, a list of sets, and answering {@code body}. */
    private static Core bodyOf(String body) {
        Compilation compilation = ACompiledModel.answered("""
                module demo
                data Ids = Set<String>
                behavior run : (xs: List<Ids>) -> Int
                let run (xs) = %s
                """.formatted(body));
        return compilation.db().ask(new Bodies.CheckedBehavior("demo", "run")).value().body();
    }

    /** The body the analysis reads of {@code run}, answering {@code body}, a {@code type}: the
     *  tree a stop is owed on, where the language's operations stand as themselves. */
    private static Core bodyOf(String type, String body) {
        Compilation compilation = ACompiledModel.answered("""
                module demo
                behavior run : (n: Int) -> %s
                let run (n) = %s
                """.formatted(type, body));
        return compilation.db().ask(new Bodies.Checked("demo")).value().analysisBodies()
                .get("run").core();
    }

    /** The one {@code List.sum} under {@code body}. */
    private static Core theSum(Core body) {
        List<Core> out = new ArrayList<>();
        collect(body, ValueName.Stdlib.operation("List", "sum"), out);
        assertEquals(1, out.size(), "one sum");
        return out.getFirst();
    }

    /** Whether the one sum in {@code body} answers, read with nothing of the input. */
    private static boolean theSumAnswers(String body) {
        Core run = bodyOf("Int", body);
        Core sum = theSum(run);
        return ContainerSizesUnderAWitness.answersOn(run, sum,
                WhatARunMayEndFor.completionApartFromTheClosuresWrittenAtIt(sum),
                node -> Optional.empty(), node -> Optional.empty());
    }

    /** A total of whole numbers written out is the one it comes to, however the list reaches the
     *  sum: past the greatest {@code Int} it does not answer. */
    @Test
    void aTotalOfNumbersWrittenOutIsReadThroughTheNameItIsGiven() {
        assertTrue(theSumAnswers("List.sum([1, 2, 3])"));
        assertTrue(theSumAnswers("{ let ns = [1, 2, 3] \n List.sum(ns) }"));
        assertFalse(theSumAnswers("{ let ns = [9223372036854775807, 1] \n List.sum(ns) }"),
                "control");
    }

    /** A list of lists written out under a name holds, flattened, no more than as many as it
     *  holds times the most any of them holds. */
    @Test
    void theListsAListWrittenOutUnderANameHoldsAreReadThroughTheName() {
        assertEquals(Optional.of(BigInteger.valueOf(4)), ContainerSizesUnderAWitness.mostHeld(
                bodyOf("List<Int>", "{ let xss = [[1], [2, 3]] \n List.concat(xss) }"),
                node -> Optional.empty()));
    }

    /** Every union under {@code body}, outermost first. */
    private static List<Core> unions(Core body) {
        List<Core> out = new ArrayList<>();
        collect(body, ValueName.Stdlib.operation("Set", "union"), out);
        return out;
    }

    /** Every application of {@code operation} under {@code e}, outermost first. */
    private static void collect(Core e, ValueName operation, List<Core> out) {
        Core node = Core.withoutStanding(e);
        AnOperationApplied applied = AnOperationApplied.of(node);
        if (applied != null && applied.operation().equals(operation)) {
            out.add(node);
        }
        Core.forEachChild(node, child -> collect(child, operation, out));
    }

    /** The list holds {@code list} sets, and each set an element hands the step holds
     *  {@code each}. */
    private static Function<Core, Optional<BigInteger>> holding(BigInteger list, BigInteger each) {
        return node -> switch (node) {
            case Core.Read read when read.name().equals("xs") -> Optional.of(list);
            case Core.FieldAccess _ -> Optional.of(each);
            default -> Optional.empty();
        };
    }

    private static boolean answers(Core body, Core union,
                                   Function<Core, Optional<BigInteger>> witness) {
        GetsPast completion = WhatARunMayEndFor.completionApartFromTheClosuresWrittenAtIt(union);
        return completion instanceof GetsPast.WhereTheAnswerFits fits
                && ContainerSizesUnderAWitness.answersOn(body, union, fits, witness,
                        node -> Optional.empty());
    }

    private static final String WALK =
            "Set.size(List.fold((acc, x) -> Set.union(acc, x.value), Set.empty, xs))";

    /**
     * What the walk carries holds no more than the sets it was handed together: two of one
     * element each fit, two of half of what a set holds come to one past it, and one such fits.
     */
    @Test
    void whatTheWalkCarriesHoldsNoMoreThanTheSetsItWasHanded() {
        Core body = bodyOf(WALK);
        Core union = unions(body).getFirst();

        assertTrue(answers(body, union, holding(BigInteger.TWO, BigInteger.ONE)));
        assertFalse(answers(body, union, holding(BigInteger.TWO, HALF_OF_WHAT_A_SET_HOLDS)));
        assertTrue(answers(body, union, holding(BigInteger.ONE, HALF_OF_WHAT_A_SET_HOLDS)));
    }

    /** A step that joins what it carries to something made of it puts in no number of elements
     *  of its own, and nothing is said of the walk, however few the sets hold. */
    @Test
    void aStepJoiningWhatItCarriesToItselfIsNotRead() {
        Core body = bodyOf("Set.size(List.fold((acc, x) -> Set.union(acc, Set.union(acc, x.value)),"
                + " Set.empty, xs))");

        assertEquals(2, unions(body).size());
        assertFalse(answers(body, unions(body).getFirst(),
                holding(BigInteger.ONE, BigInteger.ONE)));
    }

    /**
     * Where how many the list holds is not handed in, it holds no more than any list does: sets of
     * one element each come together to no more than a set holds, and sets of two may come past
     * it.
     */
    @Test
    void aListOfNoKnownSizeHoldsNoMoreThanAnyListDoes() {
        Core body = bodyOf(WALK);
        Function<Integer, Function<Core, Optional<BigInteger>>> eachHolding = each -> node ->
                node instanceof Core.FieldAccess ? Optional.of(BigInteger.valueOf(each))
                        : Optional.empty();

        assertTrue(answers(body, unions(body).getFirst(), eachHolding.apply(1)));
        assertFalse(answers(body, unions(body).getFirst(), eachHolding.apply(2)));
    }
}
