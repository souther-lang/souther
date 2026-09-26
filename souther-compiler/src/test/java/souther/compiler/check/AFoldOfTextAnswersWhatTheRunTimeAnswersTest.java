package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.core.Kernel;
import souther.compiler.numeric.Rel;
import souther.compiler.types.BinOp;
import souther.runtime.Strings;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What the compiler folds of text at compile time is what the program computes of the same text
 * when it runs.
 *
 * <p>A fold is the operation written a second time, in the compiler, where the language's own
 * definition is not at hand — and a {@code java.lang.String} method is: {@code length} counts UTF-16
 * units where {@code String.length} counts scalar values, and {@code compareTo} orders units where
 * {@code <} orders scalar values. Each is right for every string of the basic plane and wrong past
 * it, so each fold is held to the run time's answer over text on both sides of that line.
 *
 * <p>And every kernel a fold answers is one this holds. A kernel the algebra learns to fold without
 * a witness here fails {@link #everyKernelAFoldAnswersIsOneThisHolds}, rather than being right for
 * as long as nobody writes a character past the basic plane.
 */
class AFoldOfTextAnswersWhatTheRunTimeAnswersTest {

    private static String text(int... codePoints) {
        return new String(codePoints, 0, codePoints.length);
    }

    /** Text either side of the basic plane's end, and where UTF-16's order parts from the language's. */
    private static final List<String> TEXTS = List.of(
            "", "a", "ab", "JP", text(0x20BB7), text(0xFFE5), text(0x20BB7, 'a'), "a" + text(0x10000),
            text(0xE000), text(0x10FFFF), text(0x10000, 0x10000), "[a-z]+", ".{2}", "..");

    /**
     * What the run time computes for each kernel the algebra folds, over the arguments in the order
     * the kernel takes them. {@code contains} is answered by the JDK's own method at run time, which
     * is why it is the witness there.
     */
    private static final Map<Kernel, Function<List<Object>, Object>> RUN_TIME = Map.of(
            Kernel.STRING_LENGTH, args -> Strings.length((String) args.get(0)),
            Kernel.STRING_CONTAINS, args -> ((String) args.get(1)).contains((String) args.get(0)),
            Kernel.STRING_MATCHES, args -> Strings.matches((String) args.get(1),
                    (String) args.get(0)));

    @Test
    void eachFoldAnswersWhatTheRunTimeAnswers() {
        for (Map.Entry<Kernel, Function<List<Object>, Object>> each : RUN_TIME.entrySet()) {
            for (List<Object> args : ARGUMENTS) {
                Optional<Object> folded = ConstantAlgebra.computed(each.getKey(), args);
                folded.ifPresent(answer -> assertEquals(each.getValue().apply(args), answer,
                        each.getKey() + " over " + shown(args)));
            }
        }
    }

    /** {@code String.length("𠮷")} is one, the case a count of units answers two for. */
    @Test
    void theLengthOfACharacterPastTheBasicPlaneIsOne() {
        assertEquals(Optional.of(1L), ConstantAlgebra.computed(Kernel.STRING_LENGTH,
                List.of(text(0x20BB7))));
    }

    /** The two text operations folded outside a kernel: {@code ++} and the order. */
    @Test
    void joiningAndOrderingFoldAsTheRunTimeDoes() {
        for (String a : TEXTS) {
            for (String b : TEXTS) {
                assertEquals(Optional.of(Strings.append(a, b)),
                        ConstantAlgebra.binary(BinOp.CONCAT, a, b), shown(List.of(a, b)));
                assertEquals(Strings.compare(a, b) < 0, ConstantAlgebra.stands(Rel.LT, a, b),
                        shown(List.of(a, b)));
            }
        }
    }

    /**
     * Every kernel a fold answers of text is one this holds to the run time.
     *
     * <p>Asked of every kernel there is, with text and numbers in the shapes a call takes, so a fold
     * added for any kernel is found whatever it is.
     */
    @Test
    void everyKernelAFoldAnswersIsOneThisHolds() {
        Set<String> answered = new TreeSet<>();
        for (Kernel kernel : Kernel.values()) {
            for (List<Object> args : ARGUMENTS) {
                if (ConstantAlgebra.computed(kernel, args).isPresent()) {
                    answered.add(kernel.name());
                }
            }
        }
        Set<String> held = new TreeSet<>();
        RUN_TIME.keySet().forEach(each -> held.add(each.name()));
        assertEquals(held, answered);
    }

    /** One, two and three arguments of text and of numbers, in every mix. */
    private static final List<List<Object>> ARGUMENTS = arguments();

    private static List<List<Object>> arguments() {
        List<Object> values = new ArrayList<>(TEXTS);
        values.addAll(List.of(0L, 1L, 2L));
        List<List<Object>> out = new ArrayList<>();
        for (Object a : values) {
            out.add(List.of(a));
            for (Object b : values) {
                out.add(List.of(a, b));
                out.add(List.of(a, b, "a"));
            }
        }
        return out;
    }

    private static String shown(List<?> args) {
        List<String> out = new ArrayList<>();
        for (Object each : args) {
            if (each instanceof String s) {
                StringBuilder one = new StringBuilder("\"");
                s.codePoints().forEach(cp -> one.append(cp < 0x80 ? String.valueOf((char) cp)
                        : String.format("U+%04X", cp)));
                out.add(one.append('"').toString());
            } else {
                out.add(String.valueOf(each));
            }
        }
        return out.toString();
    }
}
