package souther.compiler.inputs;

import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.ValueName;
import souther.compiler.types.WrittenOwner;

/**
 * An evaluation of a dependency for a test that needs an answer to hang something on and reads no
 * body to find one.
 *
 * <p>Here and not in the compiler, which makes one only where a value is found to be a call or a
 * name for one ({@link InputReads#answerAt}). A test of what is said about an answer — a sentence, a
 * value composed for a demand — needs an answer and nothing about where it came from.
 */
public final class Evaluations {

    private Evaluations() {
    }

    /** The {@code ordinal}th construct of a body {@code dependency}'s module writes, as a call of
     *  {@code dependency}. */
    public static AnEvaluation of(ValueName.Behavior dependency, int ordinal) {
        return new AnEvaluation(dependency, new ModelOccurrence(new SourceConstructOrigin(
                new WrittenOwner.Body(dependency.module(), "b"), ordinal, 0,
                SourceConstruct.CALL), ExpansionLineage.ORIGINAL));
    }
}
