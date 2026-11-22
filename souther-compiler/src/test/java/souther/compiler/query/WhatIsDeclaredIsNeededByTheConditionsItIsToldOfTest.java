package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.ACompiledModel;
import souther.compiler.partition.AComparisonRead;
import souther.compiler.types.ModelOccurrence;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The helpers named for some conditions are ones those conditions need: none can be left out, and
 * a condition nobody asked about adds none.
 *
 * <p>A case of {@code n} cases is read in {@code n + 1} ways, and an {@code if} in three, so what
 * each helper comes to is read off the model.
 */
class WhatIsDeclaredIsNeededByTheConditionsItIsToldOfTest {

    private static String match(String name, int cases) {
        return "data " + name + " = " + IntStream.rangeClosed(1, cases)
                .mapToObj(i -> name + i).collect(Collectors.joining(" | ")) + "\n"
                + "let of" + name + " (v: " + name + "): Int =\n    match v with\n"
                + IntStream.rangeClosed(1, cases)
                .mapToObj(i -> "        | " + name + i + " -> " + i + "\n")
                .collect(Collectors.joining());
    }

    private static List<AComparisonRead> read(String model) {
        Compilation compilation = Compilation.ofSource("module m\n" + model, "Main");
        compilation.measure(Adequacy.Asked.NOTHING);
        ACompiledModel.compiles(compilation);
        return compilation.db().ask(new Adequacy.ComparisonsRead("m", "paid")).value();
    }

    private static List<String> named(WhatToDeclare declare) {
        return declare.helpers().stream().map(each -> each.helper().name()).toList();
    }

    /** Three choices that come to 27 readings beside two that come to 400: the two are what is
     *  declared, however many choices the other helper holds. */
    @Test
    void theHelperNamedTakesOutTheMostReadingsAndNotTheMostChoices() {
        List<AComparisonRead> read = read("""
                let several (a: Int, b: Int, c: Int): Int =
                    (if a < 0 then 1 else 2) + (if b < 0 then 1 else 2) + (if c < 0 then 1 else 2)
                """ + match("K", 19) + """
                let two (k: K, p: K): Int = ofK(k) + ofK(p)
                behavior paid : (a: Int, b: Int, c: Int, k: K, p: K) -> Bool
                let paid (a, b, c, k, p) = several(a, b, c) + two(k, p) == 0
                """);

        assertEquals(List.of("two"), named(ConditionsReadThroughTooManyChoices.told(read)));
    }

    /** Helpers that come to 5, 6 and 225 readings: without the last, the first two are 30. Without
     *  the first two, the last is 225, which is as few as is asked of too, and is two helpers. */
    @Test
    void forOneConditionTheHelpersNamedAreTheFewest() {
        List<AComparisonRead> read = read(match("K", 4) + match("L", 5) + match("M", 14) + """
                let two (m: M, o: M): Int = ofM(m) + ofM(o)
                behavior paid : (k: K, l: L, m: M, o: M) -> Bool
                let paid (k, l, m, o) = ofK(k) + ofL(l) + two(m, o) == 0
                """);

        assertEquals(List.of("two"), named(ConditionsReadThroughTooManyChoices.told(read)));
    }

    /** One condition is brought down by either of two helpers and another by one of them alone:
     *  the one they share is what is declared. */
    @Test
    void aHelperAnotherConditionNeedsIsNotNamedBesideOneThatIsNotNeeded() {
        List<AComparisonRead> read = read(match("K", 29) + match("L", 29) + """
                behavior paid : (k: K, l: L, o: L) -> Bool
                let paid (k, l, o) = ofK(k) + ofL(l) == 0 || ofL(l) + ofL(o) == 1
                """);

        WhatToDeclare declare = ConditionsReadThroughTooManyChoices.told(read);

        assertEquals(2, declare.conditions());
        assertEquals(List.of("ofL"), named(declare));
        assertEquals(2, declare.helpers().getFirst().conditions());
    }

    /** Asked of one condition, nothing written in the other is named. */
    @Test
    void aConditionNotAskedOfNamesNothing() {
        List<AComparisonRead> read = read(match("K", 29) + match("L", 29) + """
                behavior paid : (k: K, p: K, l: L, o: L) -> Bool
                let paid (k, p, l, o) = ofK(k) + ofK(p) == 0 || ofL(l) + ofL(o) == 1
                """);
        assertEquals(2, ConditionsReadThroughTooManyChoices.told(read).helpers().size());
        List<ModelOccurrence> each = read.stream().filter(one -> one.through().size() == 2)
                .map(AComparisonRead::copy).toList();
        assertEquals(2, each.size());

        assertEquals(List.of("ofK"), named(WhatToDeclare.of(Set.of(each.get(0)), read)));
        assertEquals(List.of("ofL"), named(WhatToDeclare.of(Set.of(each.get(1)), read)));
    }

    /** A condition that comes to no more than is made in all, and to more than one way down makes,
     *  is told of nothing before the reading; once it stopped, it is told what to declare. */
    @Test
    void aConditionThatStoppedIsToldWhatToDeclareHoweverFewItsReadings() {
        List<AComparisonRead> read = read(match("K", 17) + """
                behavior paid : (k: K, p: K) -> Bool
                let paid (k, p) = ofK(k) + ofK(p) == 0
                """);
        Set<ModelOccurrence> stopped = read.stream().filter(one -> one.through().size() == 2)
                .map(AComparisonRead::copy).collect(Collectors.toSet());

        assertEquals(WhatToDeclare.NOTHING, ConditionsReadThroughTooManyChoices.told(read));
        assertEquals(List.of("ofK"), named(WhatToDeclare.of(stopped, read)));
    }
}
