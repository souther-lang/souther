package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The run time does not depend on Raoh (spec §non-functional). The decoder a data derives is the
 * run time's own, and Raoh is one decoder binding: {@code souther-raoh} adapts what Raoh reads to a
 * {@code TreeReader} and says a refusal in Raoh's codes.
 *
 * <p>A class of the run time that names one of Raoh's types has made the run time a reader of one
 * binding's library, and the binding stops being the one place that says how a refusal is
 * reported. What the run time answers is the refusal, and how it is reported is the binding's.
 *
 * <p>Read off the compiled classes rather than the source, so that a type reached through a
 * descriptor or a method reference is a row here whatever it is spelled as.
 */
class TheRuntimeDoesNotKnowRaohTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    private static final String RAOH = "net/unit8/raoh/";

    @Test
    void noClassOfTheRuntimeNamesATypeOfRaoh() {
        assertEquals(List.of(), namingRaoh(),
                "the run time answers the fact and a decoder reports it: what a refusal is"
                        + " reported as is not the run time's to say");
    }

    private static List<String> namingRaoh() {
        Set<String> out = new TreeSet<>();
        for (ClassModel each : COMPILED.classesOf(COMPILED.module("souther-runtime"))) {
            for (String named : CompiledOutputs.classesNamedBy(each)) {
                if (named.startsWith(RAOH)) {
                    out.add(each.thisClass().asInternalName() + " -> " + named);
                }
            }
        }
        return new ArrayList<>(out);
    }
}
