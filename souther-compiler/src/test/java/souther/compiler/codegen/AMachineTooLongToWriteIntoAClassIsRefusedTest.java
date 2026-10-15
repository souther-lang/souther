package souther.compiler.codegen;

import java.util.ArrayList;
import java.util.List;
import net.unit8.notation199x.pattern.CodePoints;
import net.unit8.notation199x.pattern.PatternImage;
import net.unit8.notation199x.pattern.PatternMeaning;
import org.junit.jupiter.api.Test;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.SourcePos;
import souther.compiler.diag.msg.DeclarationMessage;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A pattern within every limit on what a pattern may be can still have a machine longer, written
 * out, than a class is given for one pattern, and that is refused where the pattern is lowered
 * (spec {@code [#a-pattern-runs-as-a-machine-a-class-holds]}).
 *
 * <p>What makes a machine long is the sets it steps over and not its states, so the pattern here
 * is a short sequence of wide classes, each of them different. Written as text it would be longer
 * than one constant of a class holds, so it is put together as what it means and handed to the one
 * place a meaning becomes what a class loads.
 */
class AMachineTooLongToWriteIntoAClassIsRefusedTest {

    @Test
    void aSequenceOfWideClassesIsRefusedAsTooLongForAClass() {
        PatternMeaning wide = wideClassesInTurn(200, 4000);
        CompileException refused = assertThrows(CompileException.class, () -> new PatternConstants()
                .of(wide, "[…]{…}", Diagnostic.at(new SourcePos(1, 1))));
        assertEquals("E2109", refused.code());
        assertEquals(new DeclarationMessage.APatternsMachineIsWrittenInMoreThanAClassHolds(
                        "[…]{…}", String.valueOf(PatternImage.MOST_CHARACTERS)),
                refused.diagnostic().said());
    }

    /** And the same shape with narrower classes is written, so what refused the wide one is its
     *  length. */
    @Test
    void theSameShapeNarrowerIsWritten() {
        PatternMeaning narrow = wideClassesInTurn(200, 40);
        assertEquals("pattern", new PatternConstants()
                .of(narrow, "[…]{…}", Diagnostic.at(new SourcePos(1, 1))).constantName());
    }

    /**
     * {@code classes} classes in turn, each of {@code width} characters none of which is beside
     * another and one character no other class holds, all past the basic plane so that none is half
     * of a pair.
     */
    private static PatternMeaning wideClassesInTurn(int classes, int width) {
        CodePoints shared = CodePoints.NONE;
        for (int i = 0; i < width; i++) {
            shared = shared.or(CodePoints.of(0x20000 + 2 * i));
        }
        List<PatternMeaning> parts = new ArrayList<>();
        for (int i = 0; i < classes; i++) {
            parts.add(new PatternMeaning.Symbols(shared.or(CodePoints.of(0x30000 + 2 * i))));
        }
        return new PatternMeaning.InTurn(parts);
    }
}
