package souther.compiler.codegen;

import java.lang.constant.ConstantDesc;
import java.lang.constant.DynamicConstantDesc;
import java.util.HashMap;
import java.util.Map;
import net.unit8.notation199x.pattern.PatternImage;
import net.unit8.notation199x.pattern.PatternMachine;
import net.unit8.notation199x.pattern.PatternMeaning;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.msg.DeclarationMessage;

import static souther.compiler.codegen.Descriptors.BSM_pattern;
import static souther.compiler.codegen.Descriptors.CD_Predicate;

/**
 * A pattern as the constant a class loads the machine it runs from.
 *
 * <p>The one place this backend turns a pattern's meaning into what a class holds. A call of
 * {@code String.matches} and a decoder's format constraint both load their pattern from here, so
 * there is one answer to which machine a class runs and one refusal where there is none.
 *
 * <p>Every pattern the checker read has a machine, since the reader holds a pattern to the states
 * every implementation runs. What this can refuse is only what a class carries: a machine whose
 * image is longer than a class is given for one pattern.
 *
 * <p>A dynamic constant: the JVM builds the pattern the first time the constant is loaded and
 * answers from the pool after that, so a class keeps no field for it and builds nothing it does not
 * run.
 *
 * <p>Kept for the compile it is part of, keyed by the meaning. A body is emitted more than once —
 * a helper inlined at each call, a clause in a value class and in its decoder — and each would
 * otherwise build the same machine again.
 */
final class PatternConstants {

    private final Map<PatternMeaning, PatternImage> images = new HashMap<>();

    /**
     * The constant for {@code meaning}, or the refusal where a class cannot carry its machine.
     *
     * @param written what the author wrote, which is what a refusal quotes
     * @param where   where a refusal is reported
     */
    DynamicConstantDesc<Object> of(PatternMeaning meaning, String written, Diagnostic.Builder where) {
        return switch (images.computeIfAbsent(meaning, read -> PatternMachine.of(read).image())) {
            case PatternImage.Written image -> DynamicConstantDesc.ofNamed(BSM_pattern,
                    "pattern", CD_Predicate, image.strings().toArray(new ConstantDesc[0]));
            case PatternImage.MoreCharacters more -> throw CompileException.of(where
                    .say(new DeclarationMessage.APatternsMachineIsWrittenInMoreThanAClassHolds(
                            written, String.valueOf(more.most())))
                    .hint(new DeclarationMessage.WriteTheRepetitionsOfAPatternSmaller())
                    .build());
        };
    }
}
