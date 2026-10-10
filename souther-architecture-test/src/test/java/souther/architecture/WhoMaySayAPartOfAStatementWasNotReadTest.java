package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.NewObjectInstruction;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Who may say why a part of a statement was not read: the reading of what the conditions state,
 * and nobody that takes a statement into words of its own.
 *
 * <p>A reason a part was not read ({@code WhyUnread}) is a fact about the reading, and the reading
 * is where it is met: a step it has no rule for, a value at no position, a clause of an invariant.
 * A reader that takes a statement into a row, a column, a way through or what a path knows passes
 * on the reasons the reading recorded. Where such a reader stops on its own, that is an edge of the
 * words it writes in, and saying it as a part not read would send an author to a reading that read
 * the whole statement.
 *
 * <p>Read off the compiled classes, each construction where it is written. A class that is new here
 * is a finding: either it is part of the reading and belongs on the list, or it is a reader that
 * made up a reason for something the reading never left unread.
 */
class WhoMaySayAPartOfAStatementWasNotReadTest {

    private static final String WHY_UNREAD = "souther/compiler/meaning/WhyUnread";

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    /**
     * The reading, and only the reading.
     *
     * <p>What a body's conditions state is read in {@code Pullback} and filed by
     * {@code MeaningsOfABodyReading}; and a site nothing was filed at, or two readings of one site
     * that disagree, is said by {@code MeaningsOfABody}.
     */
    private static final List<String> THE_READING = List.of(
            "souther/compiler/meaning/MeaningsOfABody",
            "souther/compiler/partition/MeaningsOfABodyReading",
            "souther/compiler/partition/Pullback");

    @Test
    void onlyTheReadingSaysAPartWasNotRead() {
        assertEquals(THE_READING, sayingAPartWasNotRead(),
                "a class that says a part of a statement was not read and is not the reading of"
                        + " it. A reader that stops on its own meets an edge of its own words");
    }

    /** And the walk sees a sayer that is there, or every list would be empty and agree. */
    @Test
    void andTheWalkSeesASayerThatIsThere() {
        assertTrue(sayingAPartWasNotRead().contains("souther/compiler/partition/Pullback"),
                "the reading says why a part was not read, so a walk that cannot find it finds"
                        + " nothing");
    }

    /** Every class, as the top-level class it is written in, that makes a reason a part was not
     *  read — and not the type that declares them. */
    private static List<String> sayingAPartWasNotRead() {
        Set<String> out = new TreeSet<>();
        for (Path module : COMPILED.modules()) {
            for (ClassModel each : COMPILED.classesOf(module)) {
                String sayer = each.thisClass().asInternalName();
                String written = sayer.contains("$") ? sayer.substring(0, sayer.indexOf('$'))
                        : sayer;
                if (written.equals(WHY_UNREAD)) {
                    continue;
                }
                for (MethodModel method : each.methods()) {
                    method.code().ifPresent(code -> {
                        for (CodeElement element : code) {
                            if (element instanceof NewObjectInstruction made
                                    && made.className().asInternalName()
                                            .startsWith(WHY_UNREAD + "$")) {
                                out.add(written);
                            }
                        }
                    });
                }
            }
        }
        return new ArrayList<>(out);
    }
}
