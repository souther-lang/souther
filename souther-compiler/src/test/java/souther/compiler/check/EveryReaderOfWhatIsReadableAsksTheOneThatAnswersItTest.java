package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.WhatWasCompiled;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What is readable off a value is asked of {@link ReadableFields}, and the shared spread it is
 * worked out from is read there and nowhere else by accident.
 *
 * <p>Two checks, and they are not the same rule. The first names the readers: which names a value
 * carries is asked in the elaboration of a field read, in the accessor the sum's interface declares,
 * in what a construction may spread, in what the model writes at a position, and in the reading of a
 * behavior's inputs — and those five agreeing is the point of there being an owner, since the
 * language, the analysis and the code generator would otherwise be kept in step by hand.
 *
 * <p>The second is a tripwire over the fact underneath. {@link Shape.CommonProduct.Shared} says the
 * cases of a sum spread a declaration, which is a fact about the shape and not the readable surface
 * itself — a question about provenance or about how a shared part is written on the wire could read
 * it with every right. What this stops is a new reader arriving unexamined: a class that reaches the
 * raw fields is either an owner admitted here on purpose or a reader that wanted
 * {@link ReadableFields} and worked the answer out again.
 *
 * <p>Read off what javac made of the module rather than off the source. A call is in the constant
 * pool however it was written — under an import, through a variable of any name, from inside a
 * lambda — where a text scan reads the spellings that are there today and answers about every
 * variable that happens to be named alike.
 *
 * <p><b>What is not checked here.</b> That the four questions about a shape agree at a record is a
 * law over their answers and is checked as one, in
 * {@code WhatIsReadableAndWhatIsBuiltAgreeAtARecordAndPartAtASumTest}. Each of the four reads a
 * record's fields where it needs them, so a rule counting who does that would be a rule against the
 * design rather than for it.
 */
class EveryReaderOfWhatIsReadableAsksTheOneThatAnswersItTest {

    /** Who asks what is readable off a value. */
    private static final List<String> THE_READERS = List.of(
            "souther.compiler.check.DataChecker",
            "souther.compiler.check.Elaborator",
            "souther.compiler.check.PositionReading",
            "souther.compiler.codegen.ValueClassGen",
            "souther.compiler.inputs.InputDomain");

    @Test
    void theReadersOfWhatIsReadableAskTheOneThatAnswersIt() {
        assertEquals(THE_READERS, WhatWasCompiled.callersOf(ReadableFields.class, "of").stream()
                        .sorted().toList(),
                "these ask what is readable off a value, and this is who does");
    }

    @Test
    void nothingElseWorksTheSharedSpreadOutForItself() {
        Set<String> reaching = WhatWasCompiled.callersOf(Shape.CommonProduct.Shared.class, "fields");
        assertEquals(List.of(ReadableFields.class.getName()), reaching.stream()
                        // The record holds its own accessor, and naming itself is not reading
                        // itself.
                        .filter(each -> !each.equals(Shape.CommonProduct.Shared.class.getName()))
                        .sorted().toList(),
                "the fields a sum's cases share are read where the readable surface is made; "
                        + "a reader here wanted that and worked it out again, or is an owner of a "
                        + "question of its own and belongs in this list");
    }
}
