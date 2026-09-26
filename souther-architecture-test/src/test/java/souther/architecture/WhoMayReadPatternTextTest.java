package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.constantpool.MemberRefEntry;
import java.lang.classfile.constantpool.PoolEntry;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Pattern text is read by the compiler alone, and by the few places of it that hold no settled call.
 *
 * <p>What a pattern means is read once where a {@code String.matches} call is settled, and the call
 * carries it — the emitted one and the one kept standing for the readings alike. Anything holding a
 * checked call takes the meaning from there. A class that asks the reader again is working out from
 * the text what the call already says, and an output that does it is an output reading pattern text,
 * which is the one thing no carrier may do. Each row below is a place that holds text and no
 * settled call, and says why.
 */
class WhoMayReadPatternTextTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    private static final String READER = "souther/compiler/regex/PatternParser";

    /**
     * The places that read a pattern's text.
     *
     * <p>{@code CallElaborator} is where a call's pattern is settled. {@code ConstantAlgebra} folds
     * the written tree, which is evaluated before any call in it is settled. {@code StringPredicates}
     * reads a declaration's rules off the written tree for the same reason. Nothing in an output is
     * here.
     */
    private static final List<String> READS_PATTERN_TEXT = List.of(
            "souther/compiler/check/CallElaborator",
            "souther/compiler/check/ConstantAlgebra",
            "souther/compiler/check/StringPredicates");

    @Test
    void everyPlaceThatReadsPatternTextIsWrittenDownHere() {
        assertEquals(READS_PATTERN_TEXT, readingPatternText(),
                "a place holding a settled call takes the pattern's meaning from the call; asking"
                        + " the reader again is working out a second time what the checker settled");
    }

    /** And the walk sees a reader at all, so an empty answer above would mean something. */
    @Test
    void theWalkFindsTheReader() {
        assertTrue(readingPatternText().contains("souther/compiler/check/CallElaborator"),
                "the checker reads a pattern where it settles a call, so a walk not finding that is"
                        + " finding nothing");
    }

    private static List<String> readingPatternText() {
        Set<String> out = new TreeSet<>();
        for (Path module : COMPILED.modules()) {
            for (ClassModel each : COMPILED.classesOf(module)) {
                String reader = each.thisClass().asInternalName();
                // The reader's own package is the reader: what it names of itself is not a reading.
                if (reader.startsWith("souther/compiler/regex/")) {
                    continue;
                }
                for (PoolEntry entry : each.constantPool()) {
                    if (entry instanceof MemberRefEntry member
                            && member.owner().name().stringValue().equals(READER)
                            && member.name().stringValue().equals("read")) {
                        out.add(reader);
                    }
                }
            }
        }
        return new ArrayList<>(out);
    }
}
