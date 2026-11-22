package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.ACompiledModel;
import souther.compiler.partition.AComparisonRead;
import souther.compiler.partition.Allowances;
import souther.compiler.partition.CompositionBudget;
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
 * each helper comes to is read off the model. A condition is left with 32 readings at most, and is
 * told of before it is read past 64.
 */
class WhatIsDeclaredIsNeededByTheConditionsItIsToldOfTest {

    private static final Allowances HELD = Allowances.DECLARED
            .with(CompositionBudget.READINGS_OF_ONE_CONDITION, 32)
            .with(CompositionBudget.TOTAL_READINGS_OF_ONE_CONDITION, 64);

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

    private static WhatToDeclare toldAhead(List<AComparisonRead> read) {
        return HELD.over(() -> ConditionsReadThroughTooManyChoices.told(read));
    }

    private static WhatToDeclare toldOf(Set<ModelOccurrence> conditions,
                                        List<AComparisonRead> read) {
        return HELD.over(() -> WhatToDeclare.of(conditions, read));
    }

    private static List<String> named(WhatToDeclare declare) {
        return declare.helpers().stream().map(each -> each.helper().name()).toList();
    }

    private static List<ModelOccurrence> throughTwoChoices(List<AComparisonRead> read) {
        return read.stream().filter(one -> one.through().size() == 2)
                .map(AComparisonRead::copy).toList();
    }

    /** Three choices that come to 27 readings beside two that come to 36: the two are what is
     *  declared, however many choices the other helper holds. */
    @Test
    void theHelperNamedTakesOutTheMostReadingsAndNotTheMostChoices() {
        List<AComparisonRead> read = read("""
                let several (a: Int, b: Int, c: Int): Int =
                    (if a < 0 then 1 else 2) + (if b < 0 then 1 else 2) + (if c < 0 then 1 else 2)
                """ + match("K", 5) + """
                let two (k: K, p: K): Int = ofK(k) + ofK(p)
                behavior paid : (a: Int, b: Int, c: Int, k: K, p: K) -> Bool
                let paid (a, b, c, k, p) = several(a, b, c) + two(k, p) == 0
                """);

        assertEquals(List.of("two"), named(toldAhead(read)));
    }

    /** Helpers that come to 3, 4 and 25 readings: without the last, the first two are 12. Without
     *  the first two, the last is 25, which is as few as is asked of too, and is two helpers. */
    @Test
    void forOneConditionTheHelpersNamedAreTheFewest() {
        List<AComparisonRead> read = read(match("K", 2) + match("L", 3) + match("M", 4) + """
                let two (m: M, o: M): Int = ofM(m) + ofM(o)
                behavior paid : (k: K, l: L, m: M, o: M) -> Bool
                let paid (k, l, m, o) = ofK(k) + ofL(l) + two(m, o) == 0
                """);

        assertEquals(List.of("two"), named(toldAhead(read)));
    }

    /** One condition is brought down by either of two helpers and another by one of them alone:
     *  the one they share is what is declared. */
    @Test
    void aHelperAnotherConditionNeedsIsNotNamedBesideOneThatIsNotNeeded() {
        WhatToDeclare declare = toldAhead(read(match("K", 8) + match("L", 8) + """
                behavior paid : (k: K, l: L, o: L) -> Bool
                let paid (k, l, o) = ofK(k) + ofL(l) == 0 || ofL(l) + ofL(o) == 1
                """));

        assertEquals(2, declare.conditions());
        assertEquals(List.of("ofL"), named(declare));
        assertEquals(2, declare.helpers().getFirst().conditions());
    }

    /** Either condition is brought down by the helper the two share or by the greater one of its
     *  own: the one they share is what is declared, and not one for each. */
    @Test
    void aHelperSeveralConditionsShareIsNamedBeforeOneForEach() {
        WhatToDeclare declare = toldAhead(read(match("K", 2) + match("L", 4) + match("M", 4) + """
                let ofTwo (l: L, p: L): Int = ofL(l) + ofL(p)
                let ofOther (m: M, q: M): Int = ofM(m) + ofM(q)
                behavior paid : (k: K, l: L, p: L, m: M, q: M) -> Bool
                let paid (k, l, p, m, q) =
                    ofK(k) + ofTwo(l, p) == 0 || ofK(k) + ofOther(m, q) == 1
                """));

        assertEquals(2, declare.conditions());
        assertEquals(List.of("ofK"), named(declare));
    }

    /** Asked of one condition, nothing written in the other is named. */
    @Test
    void aConditionNotAskedOfNamesNothing() {
        List<AComparisonRead> read = read(match("K", 8) + match("L", 8) + """
                behavior paid : (k: K, p: K, l: L, o: L) -> Bool
                let paid (k, p, l, o) = ofK(k) + ofK(p) == 0 || ofL(l) + ofL(o) == 1
                """);
        assertEquals(2, toldAhead(read).helpers().size());
        List<ModelOccurrence> each = throughTwoChoices(read);
        assertEquals(2, each.size());

        assertEquals(List.of("ofK"), named(toldOf(Set.of(each.get(0)), read)));
        assertEquals(List.of("ofL"), named(toldOf(Set.of(each.get(1)), read)));
    }

    /** A condition that comes to no more than is made in all, and to more than one way down makes,
     *  is told of nothing before the reading; once it stopped, it is told what to declare. */
    @Test
    void aConditionThatStoppedIsToldWhatToDeclareHoweverFewItsReadings() {
        List<AComparisonRead> read = read(match("K", 6) + """
                behavior paid : (k: K, p: K) -> Bool
                let paid (k, p) = ofK(k) + ofK(p) == 0
                """);

        assertEquals(WhatToDeclare.NOTHING, toldAhead(read));
        assertEquals(List.of("ofK"), named(toldOf(Set.copyOf(throughTwoChoices(read)), read)));
    }
}
