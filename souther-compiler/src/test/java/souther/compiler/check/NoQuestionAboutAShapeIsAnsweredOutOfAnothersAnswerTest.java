package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.WhatWasCompiled;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

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
 * satisfies it exactly while the two agree at a record: the reading of a position or the walk into a
 * written value could take the plan's answer again and nothing about the results would say so. What
 * the two owners with an answer to hand out can say is who asks them, so that is what is held here —
 * an exact set apiece, which is a rule about the other two as much as about them.
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
     *  interface declares, what a construction may spread, what the model writes at a position, and
     *  the reading of a behavior's inputs. */
    private static final List<String> ASK_WHAT_IS_READABLE = List.of(
            "souther.compiler.check.DataChecker",
            "souther.compiler.check.Elaborator",
            "souther.compiler.check.PositionReading",
            "souther.compiler.codegen.ValueClassGen",
            "souther.compiler.inputs.InputDomain");

    /** Who asks what a value is composed out of. Composing one is what the question is for, so there
     *  is one asker, and a second is a reader with some other question. */
    private static final List<String> ASK_WHAT_IS_BUILT =
            List.of("souther.compiler.partition.ConstructionPlan");

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

    /** Who calls {@code method} on {@code on}, leaving out the class that declares it — a record
     *  holds its own accessor, and naming itself is not reading itself. */
    private static List<String> callersOf(Class<?> on, String method) {
        Set<String> found = WhatWasCompiled.callersOf(on, method);
        return found.stream().filter(each -> !each.equals(on.getName())).sorted().toList();
    }
}
