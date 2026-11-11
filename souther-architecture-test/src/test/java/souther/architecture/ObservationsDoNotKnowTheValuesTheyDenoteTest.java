package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.constantpool.ClassEntry;
import java.lang.classfile.constantpool.PoolEntry;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * What a run observed does not name what a rule writes; the values that name what a run observed.
 *
 * <p>{@code values} reads observations ({@code StoppedReading}, {@code TextExtents},
 * {@code WrittenValues}), so a class of {@code observe} naming a class of {@code values} makes the
 * two packages depend on each other. Which written value an observation denotes is answered in
 * {@code values}, and an observation that answered it would be the second place that is answered.
 *
 * <p>Read off the compiled classes rather than the source, so that a type reached through a
 * descriptor or a method reference is a row here whatever it is spelled as.
 */
class ObservationsDoNotKnowTheValuesTheyDenoteTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    private static final String OBSERVE = "souther/compiler/observe/";
    private static final String VALUES = "souther/compiler/values/";

    @Test
    void noClassOfObserveNamesAClassOfValues() {
        assertEquals(List.of(), naming(OBSERVE, VALUES),
                "an observation does not answer which written value it denotes: that is"
                        + " WrittenValues, which reads observations and is not read by them");
    }

    /** The direction that is allowed is there, so the question above is asked of classes that
     *  would have shown the other. */
    @Test
    void valuesDoReadObservations() {
        assertFalse(naming(VALUES, OBSERVE).isEmpty(),
                "values reads observations, so a read of the classes that finds none is not"
                        + " reading them");
    }

    private static List<String> naming(String from, String to) {
        Set<String> out = new TreeSet<>();
        for (ClassModel each : COMPILED.classesOf(COMPILED.module("souther-compiler"))) {
            if (!each.thisClass().asInternalName().startsWith(from)) {
                continue;
            }
            for (PoolEntry entry : each.constantPool()) {
                if (entry instanceof ClassEntry named
                        && named.asInternalName().startsWith(to)) {
                    out.add(each.thisClass().asInternalName() + " -> " + named.asInternalName());
                }
            }
        }
        return new ArrayList<>(out);
    }
}
