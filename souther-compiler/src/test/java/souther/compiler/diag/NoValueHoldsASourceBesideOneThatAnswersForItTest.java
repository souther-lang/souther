package souther.compiler.diag;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Constructor;
import java.lang.reflect.Executable;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.Parameter;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Nothing in the diagnostics layer takes a source identity beside something that already answers
 * for one.
 *
 * <p>This is the shape #760 turned out to be, and it was found four times by eye before it was
 * written down. Each time the answer was the same: a value held a source next to a region or a
 * coordinate that carries one, the two could disagree, and nothing kept them the same. A renderer
 * takes them apart again — the file to quote from, the numbers to quote at — so a pair that
 * disagrees is a marker put in one file with its line read from another.
 *
 * <p>It is written as a rule on {@link WrittenAt}: <em>a source location has exactly one authority
 * for its provenance</em>. A rule a reviewer has to notice is a rule that gets noticed four times
 * and missed the fifth, so it is checked here as well.
 *
 * <p>Two questions rather than one, because a source is a {@code String} and so is a message, and
 * nothing in a signature tells them apart — the build keeps no parameter names, and there is no type
 * that means "a source". So each half is
 * asked where the answer follows from what the thing is: a value that <em>is</em> a place must not
 * take a source at all beside what it holds, and a builder of places must not take one beside a
 * region.
 */
class NoValueHoldsASourceBesideOneThatAnswersForItTest {

    /** The values that say where something is. Named rather than scanned for: a scan of the package
     *  is a list of what it happens to hold, and this is about the values that can disagree. */
    private static final List<Class<?>> PLACES = List.of(
            DiagnosticPlace.InSource.class, DiagnosticPlace.Unavailable.class,
            DiagnosticView.Unquotable.class, LabeledRegion.class, Located.class, Region.class,
            SourcePos.class, SourceProvenance.APublishedModule.class,
            SourceProvenance.TheStandardLibrary.class, Spot.class, TextRead.class);

    /** What builds them for a report. Asked of its methods, because the pair reached a label through
     *  {@code secondaryIn(String, Region, Message)} as readily as through a constructor, and a check
     *  that read constructors alone would let that entry back in without noticing. */
    private static final List<Class<?>> BUILD_PLACES = List.of(Diagnostic.Builder.class);

    /** The types that answer for a source of their own, so holding one beside them is holding two
     *  answers to one question. */
    private static final Set<Class<?>> ANSWERS_FOR_A_SOURCE =
            Set.of(Region.class, SourcePos.class, DiagnosticPlace.InSource.class);

    @Test
    void noValueThatIsAPlaceTakesASourceBesideWhatItHolds() {
        List<String> holding = new ArrayList<>();
        for (Class<?> type : PLACES) {
            for (Constructor<?> made : type.getDeclaredConstructors()) {
                if (Modifier.isPublic(made.getModifiers()) && takesBoth(made)) {
                    holding.add(made.toGenericString());
                }
            }
        }
        assertEquals(List.of(), holding,
                "taking both is two answers to one question with nothing keeping them the same,"
                        + " which is what #760 was");
    }

    @Test
    void nothingThatBuildsAPlaceTakesASourceBesideARegion() {
        List<String> holding = new ArrayList<>();
        for (Class<?> type : BUILD_PLACES) {
            for (Method called : type.getDeclaredMethods()) {
                if (Modifier.isPublic(called.getModifiers()) && takesBoth(called)) {
                    holding.add(called.toGenericString());
                }
            }
        }
        assertEquals(List.of(), holding,
                "a site handing over a source and a region separately is a marker in one file with"
                        + " its line read from another");
    }

    private static boolean takesBoth(Executable made) {
        boolean names = false;
        boolean carries = false;
        for (Parameter p : made.getParameters()) {
            names |= p.getType() == String.class;
            carries |= ANSWERS_FOR_A_SOURCE.contains(p.getType());
        }
        return names && carries;
    }
}
