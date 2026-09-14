package souther.compiler.codegen;

import org.junit.jupiter.api.Test;

import souther.compiler.check.StringPredicates;
import souther.compiler.regex.Language;
import souther.compiler.regex.PatternPlan;
import souther.compiler.regex.PatternSyntax;

import java.lang.constant.ClassDesc;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The strings a predicate is read as are the strings it accepts when the row runs.
 *
 * <p>What {@link StringPredicates} lowers a call to is used as the set of values a position admits:
 * a row is composed out of it, and a value outside it is one the rules are taken to refuse. So a
 * language narrower than the predicate is not a witness this compiler failed to offer — it is a
 * value the model allows and the reading says it does not.
 *
 * <p><b>Checked against what runs, and not against a second telling of what the predicate means.</b>
 * The two answers are independent: one is the shape composed here, the other is the method the
 * emitter calls, read out of {@link Intrinsics#emitters()} rather than named again. A test that
 * wrote out what {@code contains} means would agree with a lowering that had drifted, since the
 * same hand writes both.
 *
 * <p>Newlines are in the probes on purpose. A pattern's {@code .} is the universe less the line
 * terminators, and what stands either side of text somebody looked for is any string at all — two
 * things that read alike and are not the same set. The one written into the lowering was the first,
 * which quietly made `String.contains("x", "\nx")` a rule this compiler said no value satisfies
 * (issue #1249).
 */
class AStringPredicateAdmitsWhatItAcceptsAtRunTimeTest {

    /** Strings that tell the two universes apart, and a few that tell the shapes apart. */
    private static final List<String> PROBES = List.of(
            "", "x", "xx", "ax", "xa", "axa",
            "\n", "\nx", "x\n", "\nx\n", "a\nx", "x\na",
            "\r", "\rx", "\u2028x", "x\u0085");

    /** The text each predicate is asked about, chosen so every probe above is on one side or the
     *  other for at least one of them. */
    private static final String NEEDLE = "x";

    @Test
    void everyPredicateAdmitsWhatItsOwnEmissionAccepts() {
        List<String> wrong = new ArrayList<>();
        for (StringPredicates predicate : StringPredicates.values()) {
            if (predicate.takesAPattern()) {
                // What a pattern accepts is the pattern's, read by the parser rather than composed
                // here, so there is no shape of this test's to check against the run.
                continue;
            }
            Method runs = emittedFor(predicate);
            Language admits = languageOf(predicate.accepting(NEEDLE));
            for (String probe : PROBES) {
                boolean atRunTime = answers(runs, probe, NEEDLE);
                if (admits.has(probe) != atRunTime) {
                    wrong.add(predicate + " on " + written(probe) + ": read as "
                            + admits.has(probe) + ", answers " + atRunTime);
                }
            }
        }
        assertEquals(List.of(), wrong,
                "a predicate admits the strings it accepts, and no others");
    }

    /** And the probes really do reach both answers, so agreement above is not two constants. */
    @Test
    void theProbesReachBothAnswers() {
        Language admits = languageOf(StringPredicates.CONTAINS.accepting(NEEDLE));

        assertTrue(PROBES.stream().anyMatch(admits::has), "some probe is in");
        assertTrue(PROBES.stream().anyMatch(each -> !admits.has(each)), "some probe is out");
        assertTrue(PROBES.stream().anyMatch(each -> each.contains("\n") && admits.has(each)),
                "and one of the ones that is in holds a newline");
    }

    /** The method the emitter calls for this predicate, read off the table it emits from. */
    private static Method emittedFor(StringPredicates predicate) {
        Intrinsics.Emit emit = Intrinsics.emitters().get(predicate.kernel());
        assertNotNull(emit, predicate + " is emitted by nothing");
        return switch (emit) {
            case Intrinsics.JdkVirtual it -> declared(it.owner(), it.method(), true);
            case Intrinsics.RuntimeStatic it -> declared(it.owner(), it.method(), false);
            default -> throw new AssertionError(predicate + " is emitted as " + emit
                    + ", which this test has no way to run");
        };
    }

    /** Whether the emitted method says the probe holds, called the way the emitter calls it. */
    private static boolean answers(Method method, String subject, String needle) {
        try {
            Object answer = java.lang.reflect.Modifier.isStatic(method.getModifiers())
                    ? method.invoke(null, subject, needle)
                    : method.invoke(subject, needle);
            return (Boolean) answer;
        } catch (ReflectiveOperationException e) {
            throw new AssertionError("could not run " + method, e);
        }
    }

    private static Method declared(ClassDesc owner, String name, boolean virtual) {
        String binary = owner.packageName().isEmpty() ? owner.displayName()
                : owner.packageName() + "." + owner.displayName();
        try {
            Class<?> type = Class.forName(binary);
            for (Method each : type.getMethods()) {
                if (each.getName().equals(name)
                        && each.getParameterCount() == (virtual ? 1 : 2)
                        && each.getReturnType() == boolean.class) {
                    return each;
                }
            }
            throw new AssertionError("no " + name + " on " + binary);
        } catch (ClassNotFoundException e) {
            throw new AssertionError(binary + " is not on the test's path", e);
        }
    }

    private static Language languageOf(PatternSyntax syntax) {
        Language made = PatternPlan.of(syntax).compile(PatternPlan.Budget.OF_A_WITNESS.meter());
        assertNotNull(made, "the lowering is a language this compiler can build");
        return made;
    }

    private static String written(String probe) {
        return "\"" + probe.replace("\n", "\\n").replace("\r", "\\r")
                .replace("\u2028", "\\u2028").replace("\u0085", "\\u0085") + "\"";
    }
}
