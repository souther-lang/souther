package souther.compiler.diag;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Constructor;
import java.lang.reflect.Modifier;
import java.lang.reflect.Parameter;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * No value in the diagnostics layer takes a source identity beside something that already answers
 * for one.
 *
 * <p>This is the shape #760 turned out to be, and it was found four times by eye before it was
 * written down. Each time the answer was the same: a value held a source next to a region or a
 * coordinate that carries one, the two could disagree, and nothing kept them the same. The renderer
 * takes them apart again — the file to quote from, the numbers to quote at — so a pair that
 * disagrees is a marker put in one file with its line read from another.
 *
 * <p>It was written down as a rule on {@code WrittenAt}: <em>a source location has exactly one
 * authority for its provenance</em>. A rule a reviewer has to notice is a rule that gets noticed
 * four times and missed the fifth, so it is checked here instead.
 *
 * <p>Asked of the constructors, because the constructor is where the pair would have to be handed
 * over. A type that derives its source from what it holds cannot take one, and a type that takes one
 * has nothing else to derive it from — {@link Spot#primary} is the case that legitimately does, and
 * it takes no region beside it.
 */
class NoValueHoldsASourceBesideOneThatAnswersForItTest {

    /** What the diagnostics layer says a place is with. Named rather than scanned for: a scan of the
     *  package is a list of the classes it happens to hold, and what this is about is the two kinds
     *  of value that can disagree. */
    private static final List<Class<?>> PLACES = List.of(
            Diagnostic.class, DiagnosticPlace.class, DiagnosticPlace.InSource.class,
            DiagnosticPlace.Unavailable.class, DiagnosticView.class,
            DiagnosticView.Unquotable.class, LabeledRegion.class, Located.class, Region.class,
            SourcePos.class, SourceProvenance.APublishedModule.class,
            SourceProvenance.TheStandardLibrary.class, Spot.class, TextRead.class);

    /** The types that answer for a source of their own, so holding one beside them is holding two
     *  answers to one question. */
    private static final Set<Class<?>> ANSWERS_FOR_A_SOURCE =
            Set.of(Region.class, SourcePos.class, DiagnosticPlace.InSource.class);

    /**
     * The one exception, and it is a defect rather than a shape this rule does not cover.
     *
     * <p>{@code SourceRef(String sourceId, SourcePos pos)} puts an identity beside a coordinate that
     * carries one. Measured across this suite: 14002 of 14017 constructions redundant, and the 15
     * that disagree mix a compilation identity with a caller-supplied name. Filed as #762 with the
     * evidence, and left out of #760 because it reaches into the example and partition layers.
     */
    private static final Set<Class<?>> KNOWN_AND_FILED = Set.of(SourceRef.class);

    @Test
    void noConstructorTakesASourceBesideSomethingThatCarriesOne() {
        List<String> holding = new ArrayList<>();
        for (Class<?> type : PLACES) {
            if (KNOWN_AND_FILED.contains(type)) {
                continue;
            }
            for (Constructor<?> made : type.getDeclaredConstructors()) {
                if (!Modifier.isPublic(made.getModifiers())) {
                    continue;   // a private constructor is reached through named ways of building
                }
                if (namesASource(made) && carriesASource(made)) {
                    holding.add(type.getSimpleName() + made.toGenericString());
                }
            }
        }
        assertEquals(List.of(), holding,
                "a value taking both is two answers to one question with nothing keeping them the"
                        + " same, which is what #760 was");
    }

    /** And the exception is one this names on purpose, so it goes when #762 does rather than
     *  outliving it as a rule nobody remembers writing. */
    @Test
    void theOneExceptionIsStillTheOneThatWasFiled() {
        assertEquals(Set.of(SourceRef.class), KNOWN_AND_FILED);
        assertFalse(PLACES.contains(SourceRef.class),
                "SourceRef is named as the exception rather than checked and skipped");
    }

    private static boolean namesASource(Constructor<?> made) {
        for (Parameter p : made.getParameters()) {
            if (p.getType() == String.class) {
                return true;
            }
        }
        return false;
    }

    private static boolean carriesASource(Constructor<?> made) {
        for (Parameter p : made.getParameters()) {
            if (ANSWERS_FOR_A_SOURCE.contains(p.getType())) {
                return true;
            }
        }
        return false;
    }
}
