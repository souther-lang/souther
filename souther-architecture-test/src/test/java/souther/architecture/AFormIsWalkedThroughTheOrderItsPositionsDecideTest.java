package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeInstruction;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A reader that walks a form's positions asks the atom domain what order to walk them in.
 *
 * <p>A {@link souther.compiler.numeric.CanonicalForm} is a mapping and holds no order of its own.
 * Two writings of one rule are one form, and which of them a caller typed is not something the form
 * kept — so a reader that walks the positions as the mapping hands them over has an order in its
 * answer that the form it read cannot see, and two callers that wrote one rule two ways are
 * answered two ways.
 *
 * <p><b>Which is why the walk is a question about the atom domain.</b> {@code entriesIn} and
 * {@code atomsIn} take a {@link souther.compiler.numeric.CanonicalOrder}, the domain says what its
 * own is, and a pair of positions that order cannot tell apart is refused rather than walked as one.
 * What is left of {@code coefs()} is what a mapping answers: what a position weighs, whether the
 * form names one, and how many there are.
 *
 * <p><b>Asked of whether the walk happens and not of what it comes to.</b> A walk whose answer is a
 * sum, a conjunction or a set is one whose result does not depend on the order — and reading a
 * method well enough to know that is reading it, which is the thing that goes wrong once and is not
 * noticed for a year. So the raw walk is what is named, and a reader that is sure the order cannot
 * reach its answer says so here, once, with the reason — rather than each of them being re-read
 * whenever somebody wonders.
 *
 * <p><b>Every one of those is something to close and not a shape to keep.</b> The list below is
 * what is still to move, and a reader taken off it is one fewer place where the order a form does
 * not hold can start being read again.
 */
class AFormIsWalkedThroughTheOrderItsPositionsDecideTest {

    private static final String THE_FORM = "souther/compiler/numeric/CanonicalForm";

    /** What a mapping is asked, which says nothing about what order it holds. */
    private static final Set<String> ASKED_NOT_WALKED =
            Set.of("get", "getOrDefault", "containsKey", "containsValue", "size", "isEmpty",
                    "equals", "hashCode", "toString", "copyOf", "of");

    /** What takes the positions out in the order the mapping happens to hold them. */
    private static final Set<String> WALKS_IT =
            Set.of("keySet", "entrySet", "values", "forEach", "iterator", "stream",
                    "sequencedKeySet", "sequencedEntrySet", "sequencedValues");

    /**
     * The readers that still walk a form's coefficients as the mapping hands them over.
     *
     * <p>None, which is where this was headed. A reader put here would be one somebody read and
     * found the order could not reach the answer of — a sum, a conjunction, a pick by the weight at
     * a position — and that is a fact about the body as it stands rather than about the reader, so
     * it is a place to move rather than a shape to keep.
     */
    private static final List<String> STILL_TO_MOVE = List.of();

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    private static final CompiledOutputs AND_WHAT_IS_COMPILED_BESIDE_IT =
            CompiledOutputs.ofEverythingCompiledHere();

    @Test
    void everyReaderThatWalksAFormsPositionsIsOneOfTheOnesStillToMove() {
        assertEquals(STILL_TO_MOVE.stream().sorted().toList(), whoWalksAForm(COMPILED),
                "a reader that walks a form's positions as the mapping hands them over has an"
                        + " order in its answer that the form cannot see — it asks the atom domain"
                        + " for one (CanonicalForm#entriesIn), or it is named above with why the"
                        + " order cannot reach what it answers");
    }

    /**
     * And the rule was asked of classes that were read.
     *
     * <p>A walk finding no class that mentions a form would find no reader walking one, and would
     * pass while answering about nothing.
     */
    @Test
    void andTheClassesThatReadAFormWereRead() {
        List<String> mentioning = new ArrayList<>();
        for (ClassModel read : COMPILED.all()) {
            if (read.methods().stream().anyMatch(each -> asks(each, ASKED_NOT_WALKED)
                    || asks(each, WALKS_IT))) {
                mentioning.add(read.thisClass().name().stringValue());
            }
        }

        assertFalse(mentioning.isEmpty(),
                "nothing here reads a form's coefficients at all, which is not what this"
                        + " repository holds");
        assertTrue(COMPILED.all().size() > 1, "the classes this rule is about were not built here");
    }

    /**
     * And a reader that does take the walk is one this finds.
     *
     * <p>The positive control, and the reason there is a subject beside this test. With nobody left
     * to move, a rule that had stopped looking for anything would name nobody and would read as
     * every reader having moved — which is the one answer it must not be able to give by accident.
     * So one reader that walks a form is compiled here, and the rule is asked of what was compiled
     * beside the test as well as of what this repository publishes.
     */
    @Test
    void andAReaderThatDoesTakeTheWalkIsOneThisFinds() {
        List<String> found = whoWalksAForm(AND_WHAT_IS_COMPILED_BESIDE_IT);

        assertTrue(found.contains(AFormWalkedAsItIsHeld.class.getName().replace('.', '/')
                        + "#positionsAsTheyCome"),
                "the one reader written here to walk a form as it is held was not found, so what"
                        + " this rule looks for is not what such a reader does: " + found);
    }

    /**
     * A reader of a form that takes its positions as the mapping hands them over.
     *
     * <p>Written to be found. Nothing calls it and nothing may: what it is for is that the rule
     * above has something to find, so that finding nothing in what this repository publishes is an
     * answer about the readers rather than about the rule.
     */
    static final class AFormWalkedAsItIsHeld {

        private AFormWalkedAsItIsHeld() {
        }

        static <A> List<A> positionsAsTheyCome(souther.compiler.numeric.CanonicalForm<A> form) {
            return new ArrayList<>(form.coefs().keySet());
        }
    }

    /** Every method that asks a form for its coefficients and then walks what it was handed. */
    private static List<String> whoWalksAForm(CompiledOutputs where) {
        List<String> walking = new ArrayList<>();
        for (ClassModel read : where.all()) {
            for (MethodModel each : read.methods()) {
                if (asksAForm(each) && asks(each, WALKS_IT)) {
                    walking.add(read.thisClass().name().stringValue() + "#"
                            + each.methodName().stringValue());
                }
            }
        }
        return walking.stream().sorted().distinct().toList();
    }

    /** Whether this method asks a form for the mapping it holds. */
    private static boolean asksAForm(MethodModel method) {
        return method.code().stream().flatMap(code -> code.elementStream())
                .anyMatch(element -> element instanceof InvokeInstruction call
                        && call.owner().asInternalName().equals(THE_FORM)
                        && call.name().stringValue().equals("coefs"));
    }

    /** Whether this method calls one of {@code names} on something that is a mapping or a set. */
    private static boolean asks(MethodModel method, Set<String> names) {
        return method.code().stream().flatMap(code -> code.elementStream())
                .anyMatch(element -> element instanceof InvokeInstruction call
                        && (call.owner().asInternalName().equals("java/util/Map")
                                || call.owner().asInternalName().equals("java/util/Set"))
                        && names.contains(call.name().stringValue()));
    }
}
