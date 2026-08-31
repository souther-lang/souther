package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.WhatWasCompiled;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Each question about a shape is asked of the one that answers it, and of nothing else.
 *
 * <p>Four are asked: what is readable off a value standing at a position, what a value there is
 * composed out of, which positions a reading has under it, and where a step into a written value
 * lands. They come to the same fields at a record and part at a sum whose cases share a spread, and
 * that agreement is a law over the answers — checked as one in
 * {@code WhatIsReadableAndWhatIsBuiltAgreeAtARecordAndPartAtASumTest}, which holds however the four
 * are worked out.
 *
 * <p>Which is why that law is not enough on its own. A question answered out of another's answer
 * satisfies it exactly while the two agree at a record: the reading of a value or the walk into a
 * written one could take the plan's answer again and nothing about the results would say so. So each
 * of the four has an owner and says who asks it — an exact set apiece, which is a rule about the
 * others as much as about itself.
 *
 * <p>The pair that part at a sum is the pair to watch. What is readable off a value there is what
 * its cases share, and the positions under it are under each of the cases; a reader that wanted the
 * first and took the second, or the other way about, is a reader for whom a name a clause writes and
 * a place a row writes a value at are one word.
 *
 * <p>Read off what javac made of the module rather than off the source. A call is in the constant
 * pool however it was written — under an import, through a variable of any name, from inside a
 * lambda — where a text scan reads the spellings that are there today and answers about every
 * variable that happens to be named alike.
 *
 * <p>An entry added to one of these lists is a finding and not a formality: it says a reader of that
 * question arrived, and whether it wanted the question or wanted one of its own is the thing to
 * answer before the list is edited.
 */
class NoQuestionAboutAShapeIsAnsweredOutOfAnothersAnswerTest {

    /** Who asks what is readable off a value: the elaboration of a field read, the accessor a sum's
     *  interface declares, what a construction may spread, what the model writes where a value
     *  stands, and the reading of a behavior's inputs. */
    private static final List<String> ASK_WHAT_IS_READABLE = List.of(
            "souther.compiler.check.DataChecker",
            "souther.compiler.check.Elaborator",
            "souther.compiler.check.ValueReading",
            "souther.compiler.codegen.ValueClassGen",
            "souther.compiler.inputs.InputDomain");

    /** Who asks what a value is composed out of. Composing one is what the question is for, so there
     *  is one asker, and a second is a reader with some other question. */
    private static final List<String> ASK_WHAT_IS_BUILT =
            List.of("souther.compiler.partition.ConstructionPlan");

    /** Who asks which positions stand under one. The derivation of a partition, which is what walks
     *  them; a second asker is a reader that wanted one of the other three. */
    private static final List<String> ASK_WHAT_STANDS_UNDER =
            List.of("souther.compiler.inputs.InputDomain");

    /** Who asks where a step into a written value lands. Nobody outside the walk that takes the
     *  step — a reader working it out again turns a row's own path into a second reading of the
     *  declarations. */
    private static final List<String> ASK_WHERE_A_STEP_LANDS = List.of();

    @Test
    void whatIsReadableIsAskedOfTheOneThatAnswersIt() {
        assertEquals(ASK_WHAT_IS_READABLE, callersOf(ReadableFields.class, "of"),
                "these ask what is readable off a value, and this is who does");
    }

    @Test
    void whatAValueIsBuiltOutOfIsAskedOfTheOneThatAnswersIt() {
        assertEquals(ASK_WHAT_IS_BUILT, callersOf(ConstructionDescent.class, "toBuild"),
                "a reader here either composes a value or answered its own question out of how one "
                        + "is composed");
    }

    /**
     * And the two that had no owner named.
     *
     * <p>Which positions stand under one is a sum's cases and what they put there, and it is
     * answered where a partition is derived. A reading that wants the names a clause may write asks
     * what is readable and never this: a sum states what its cases share at the sum, and the
     * positions those names stand at are under each case.
     */
    @Test
    void whatStandsUnderAPositionIsAskedOfTheOneThatAnswersIt() {
        assertEquals(ASK_WHAT_STANDS_UNDER,
                callersOf(souther.compiler.inputs.StructuralInspection.class, "of"),
                "these ask which positions stand under one, and this is who does");
    }

    /**
     * Where a step into a written value lands, asked by the walk that takes the step.
     *
     * <p>Both halves, because the expected set is empty and an empty set is what a question nobody
     * can name comes to as well: the first says the question is asked at all, the second that it is
     * asked nowhere but inside its owner.
     */
    @Test
    void whereAStepIntoAWrittenValueLandsIsAskedOfTheOneThatAnswersIt() {
        Class<?> owner = souther.compiler.partition.BehaviorInputs.class;
        assertFalse(WhatWasCompiled.callersOf(owner, "stepWrittenValue").isEmpty(),
                "a step into a written value is turned into a type somewhere, or this is watching a"
                        + " name nothing calls");
        assertEquals(ASK_WHERE_A_STEP_LANDS, callersOf(owner, "stepWrittenValue"),
                "a step into what a row wrote is turned into a type in one place");
    }

    /**
     * And the fact the readable surface is made of is reached where it is made.
     *
     * <p>A tripwire over {@link Shape.CommonProduct.Shared} and not a claim that a sum's shared
     * spread may only ever be read for this one question: it says the cases spread a declaration,
     * which a question about provenance or about how a shared part is written could read with every
     * right. An owner of one of those belongs in this list; a reader that wanted
     * {@link ReadableFields} and worked the answer out again does not.
     */
    @Test
    void nothingElseWorksTheSharedSpreadOutForItself() {
        assertEquals(List.of(ReadableFields.class.getName()),
                callersOf(Shape.CommonProduct.Shared.class, "fields"),
                "the fields a sum's cases share are read where the readable surface is made");
    }

    /** Who calls {@code method} on {@code on}, leaving out the class that declares it and anything
     *  nested inside it — a record holds its own accessor, a lambda is compiled into the class that
     *  wrote it, and naming itself is not reading itself. */
    private static List<String> callersOf(Class<?> on, String method) {
        Set<String> found = WhatWasCompiled.callersOf(on, method);
        return found.stream()
                .filter(each -> !each.equals(on.getName()) && !each.startsWith(on.getName() + "$"))
                .sorted().toList();
    }
}
