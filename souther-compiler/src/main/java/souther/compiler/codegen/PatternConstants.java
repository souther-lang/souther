package souther.compiler.codegen;

import java.lang.constant.ConstantDesc;
import java.lang.constant.DynamicConstantDesc;
import java.util.HashMap;
import java.util.Map;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.msg.DeclarationMessage;
import souther.compiler.regex.PatternImage;
import souther.compiler.regex.PatternMeaning;

import static souther.compiler.codegen.Descriptors.BSM_stringPattern;
import static souther.compiler.codegen.Descriptors.CD_StringPattern;

/**
 * A pattern as the constant a class loads the machine it runs from.
 *
 * <p>The one place this backend turns a pattern's meaning into what a class holds. A call of
 * {@code String.matches} and a decoder's format constraint both load their pattern from here, so
 * there is one answer to which machine a class runs and one refusal where there is none.
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
     * The constant for {@code meaning}, or the refusal where this backend writes no machine for it.
     *
     * @param written what the author wrote, which is what a refusal quotes
     * @param where   where a refusal is reported
     */
    DynamicConstantDesc<Object> of(PatternMeaning meaning, String written, Diagnostic.Builder where) {
        return switch (images.computeIfAbsent(meaning, PatternImage::of)) {
            case PatternImage.Written image -> DynamicConstantDesc.ofNamed(BSM_stringPattern,
                    "pattern", CD_StringPattern, image.strings().toArray(new ConstantDesc[0]));
            case PatternImage.MoreStates more -> throw CompileException.of(where
                    .say(new DeclarationMessage.APatternsMachineHasMoreStatesThanAClassRuns(
                            written, String.valueOf(more.most())))
                    .hint(new DeclarationMessage.WriteTheRepetitionsOfAPatternSmaller())
                    .build());
            case PatternImage.MoreCharacters more -> throw CompileException.of(where
                    .say(new DeclarationMessage.APatternsMachineIsWrittenInMoreThanAClassHolds(
                            written, String.valueOf(more.most())))
                    .hint(new DeclarationMessage.WriteTheRepetitionsOfAPatternSmaller())
                    .build());
        };
    }
}
