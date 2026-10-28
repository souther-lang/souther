package souther.architecture;

import org.junit.jupiter.api.Test;

import souther.compiler.meaning.DecidingCase;

import java.lang.classfile.ClassModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeInstruction;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The cases a line decides in are read as a graph, and the only readers that take their parts out
 * of one are the fold that visits each case once and the choosing that counts a step for every
 * alternative it takes.
 *
 * <p>The cases of a line are a graph: the state a choice leaves is one value every way to it
 * shares, so the ways of choosing grow as the product of the choices while the cases that hold them
 * grow as their sum. A reader that takes {@code alternatives} or {@code factors} out of a case and
 * goes into each is walking the product, whatever it is written to answer, and one that walks it
 * for the figures it ran out of steps at walks it after the steps are spent. Every question asked of
 * all the cases is {@code DecidingCase.Cases#fold}, so that each case is worked out once; the one
 * walk that is not a fold chooses among them and is bound by steps.
 *
 * <p>Asked of the compiled code and not of the source: a record pattern reads the parts of a case
 * through its accessors, and so does a call, and both are an invocation.
 */
class TheCasesOfALineAreReadOnlyThroughTheirFoldTest {

    private static final String CASES = "souther/compiler/meaning/DecidingCase$Cases";

    private static final String EACH_OF = CASES + "$EachOf";

    private static final String TOGETHER = CASES + "$Together";

    private static final String CHOOSING = AMethod.of("souther/compiler/meaning/CasesOfALineAsked",
            "chosen", "(Ljava/util/List;Ljava/util/List;Ljava/util/function/Predicate;"
                    + "Ljava/util/function/Consumer;)V");

    private static final CompiledOutputs PUBLISHED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    private static final CompiledOutputs AND_BESIDE_IT = CompiledOutputs.ofEverythingCompiledHere();

    /** Every method that takes the parts out of a case, outside the cases themselves. */
    private static Set<String> whoTakesThePartsOut(CompiledOutputs outputs) {
        Set<String> found = new TreeSet<>();
        for (ClassModel owner : outputs.all()) {
            String self = owner.thisClass().asInternalName();
            if (self.equals(CASES) || self.startsWith(CASES + "$")) {
                continue;
            }
            WhereALambdaIsWritten lambdas = WhereALambdaIsWritten.in(owner);
            for (MethodModel method : owner.methods()) {
                if (method.code().isEmpty()) {
                    continue;
                }
                for (var element : method.code().orElseThrow()) {
                    if (element instanceof InvokeInstruction call && takesPartsOut(call)) {
                        found.add(lambdas.enclosing(AMethod.of(owner, method)));
                    }
                }
            }
        }
        return found;
    }

    private static boolean takesPartsOut(InvokeInstruction call) {
        String owner = call.owner().asInternalName();
        return (owner.equals(EACH_OF) && call.name().equalsString("alternatives"))
                || (owner.equals(TOGETHER) && call.name().equalsString("factors"));
    }

    /**
     * Outside the cases, the choosing is the one that takes their parts out. Equal and not
     * contained: the choosing is a reader of them today, so a rule that found nobody would be
     * answering about nothing.
     */
    @Test
    void onlyTheChoosingTakesThePartsOutOfACaseOutsideTheCases() {
        assertEquals(Set.of(CHOOSING), whoTakesThePartsOut(PUBLISHED),
                "a question asked of all the cases is asked through DecidingCase.Cases#fold,"
                        + " which works out each case once however many ways lead to it");
    }

    /**
     * And a reader that does take them out is one this finds, whatever it is written to answer.
     *
     * <p>The positive control: finding the choosing alone does not say the rule could find
     * another, and a reader written beside this test is one nobody may call.
     */
    @Test
    void andAReaderThatTakesThePartsOutIsOneThisFinds() {
        String here = TakesThePartsOut.class.getName().replace('.', '/');

        List<String> found = whoTakesThePartsOut(AND_BESIDE_IT).stream()
                .filter(each -> each.startsWith(here + "#")).toList();

        assertTrue(found.stream().anyMatch(each -> each.contains("#alternativesOf(")),
                "a reader of the alternatives of a case was not found: " + found);
        assertTrue(found.stream().anyMatch(each -> each.contains("#factorsOf(")),
                "a reader of the factors of a case was not found: " + found);
    }

    /** Readers of the parts of a case, written to be found. Nothing calls them and nothing may. */
    static final class TakesThePartsOut {

        private TakesThePartsOut() {
        }

        static int alternativesOf(DecidingCase.Cases.EachOf cases) {
            return cases.alternatives().size();
        }

        static int factorsOf(DecidingCase.Cases.Together cases) {
            return cases.factors().size();
        }
    }
}
