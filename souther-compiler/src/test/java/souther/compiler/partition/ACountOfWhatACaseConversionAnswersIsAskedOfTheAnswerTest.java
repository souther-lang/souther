package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import net.unit8.notation199x.pattern.CodePoints;

import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Hir;
import souther.compiler.carrier.Membership;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.NewtypeInners;
import souther.compiler.check.ReadingPolicy;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.ScopedDeclarations;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeCardinality;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.RulesWithNoLine;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.observe.ObservedValue;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.regex.PatternPlan;
import souther.compiler.semantics.CaseMapping;
import souther.compiler.semantics.CodePointClass;
import souther.compiler.types.Type;
import souther.compiler.values.Allowance;
import souther.compiler.values.AsACompilationAllows;
import souther.runtime.Strings;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How many code points of a class what a case conversion answers holds is asked of the answer.
 *
 * <p>The answer is the full mapping and then NFC, so its code points are not the string's code
 * points one by one: a {@code J} followed by a combining caron is one code point that is none of
 * {@code [a-z]}, though the string holds a {@code J}. A count taken back to the classes the string's
 * own code points are in would be wrong at exactly such a string, so the term carries the
 * conversion and is read, and written for, through the run time's own.
 */
class ACountOfWhatACaseConversionAnswersIsAskedOfTheAnswerTest {

    private static final Symbols SYMBOLS = Symbols.none(DefaultStdlib.get());
    private static final RuleReadingSource RULES = RuleReadings.ofNoClauseFiled(SYMBOLS);
    private static final ReadingPolicy POLICY = new ReadingPolicy(64, 12,
            AsACompilationAllows.admittedValues(), AsACompilationAllows.whatARuleLeaves());
    private static final RuleReadingContext READING = RuleReadingContext.unshared(RULES, POLICY);
    private static final NewtypeInners INNERS = ScopedDeclarations.wrapsOf(SYMBOLS);
    private static final TermPath AT = TermPath.of("t");

    private static final CodePointClass LOWERCASE_LETTERS =
            CodePointClass.of(CodePoints.between('a', 'z'));
    private static final CodePointClass ASCII_ALPHANUMERIC =
            CodePointClass.of(CodePoints.between('0', '9').or(CodePoints.between('a', 'z')));

    private static NumericTerm.CodePointClassCount counting(CaseMapping through) {
        return NumericTerm.CodePointClassCount.of(AT, ASCII_ALPHANUMERIC, through, Type.STRING,
                INNERS);
    }

    private static TermOrders ordersOf(CaseMapping through) {
        return TermOrdersFixtures.at(counting(through), Type.STRING, SYMBOLS);
    }

    private static NumericTerm.Reading read(CaseMapping through, String text) {
        return ordersOf(through).read(new ObservedValue.Text(text));
    }

    /** The two ways of counting one place are two numbers of it. */
    @Test
    void theConversionIsPartOfWhichNumberItIs() {
        assertNotEquals(counting(CaseMapping.NONE), counting(CaseMapping.LOWERCASE));
        assertNotEquals(counting(CaseMapping.LOWERCASE), counting(CaseMapping.UPPERCASE));
        assertEquals(counting(CaseMapping.LOWERCASE), counting(CaseMapping.LOWERCASE));
    }

    /**
     * Counted in the answer: a capital is counted where the string is converted and not where it
     * is not, and a letter that composes with the mark after it into a code point of no class of
     * the letter is not counted although the string holds it.
     */
    @Test
    void theAnswerIsWhatIsCounted() {
        assertEquals(new NumericTerm.Reading.Number(Count.of(1)),
                read(CaseMapping.LOWERCASE, "A"));
        assertEquals(new NumericTerm.Reading.Number(Count.of(0)),
                read(CaseMapping.NONE, "A"));
        assertEquals(new NumericTerm.Reading.Number(Count.of(0)),
                read(CaseMapping.LOWERCASE, "!"));
        String composing = "J̌";
        assertEquals("ǰ", Strings.lowercase(composing).substring(0, 1),
                "the run time's answer is one code point, which no class of the letter holds");
        assertEquals(new NumericTerm.Reading.Number(Count.of(0)),
                read(CaseMapping.LOWERCASE, composing));
    }

    /**
     * A conversion of a conversion is counted as one: the outermost is the last applied, so the
     * lowercase of the uppercase of a sharp s is two letters, where either alone leaves none.
     */
    @Test
    void aConversionOfAConversionIsCountedInWhatTheLastOneAnswers() {
        CaseMapping lowercaseOfUppercase = new CaseMapping.Lowercase(CaseMapping.UPPERCASE);
        CaseMapping uppercaseOfLowercase = new CaseMapping.Uppercase(CaseMapping.LOWERCASE);
        assertNotEquals(lowercaseOfUppercase, uppercaseOfLowercase);
        assertEquals(new NumericTerm.Reading.Number(Count.of(2)),
                read(lowercaseOfUppercase, "ß"));
        assertEquals(new NumericTerm.Reading.Number(Count.of(0)), read(CaseMapping.LOWERCASE, "ß"));
        assertEquals(new NumericTerm.Reading.Number(Count.of(0)),
                read(uppercaseOfLowercase, "ß"));
        assertEquals("String.lowercase(String.uppercase(t))",
                lowercaseOfUppercase.writtenAround("t"));
        assertEquals(new CaseMapping.Lowercase(CaseMapping.UPPERCASE),
                CaseMapping.applying(
                        souther.compiler.types.ValueName.Stdlib.operation("String", "lowercase"),
                        CaseMapping.UPPERCASE));
    }

    /**
     * What is built for a count of the answer reads back as that count, through the conversion,
     * and a count of the string's own is not mistaken for it: the string built for nought of the
     * lowercase holds a capital it would be counted at as it stands.
     */
    @Test
    void everyStringBuiltForACountOfTheAnswerReadsBackAsItThroughTheConversion() {
        for (CaseMapping through : List.of(CaseMapping.LOWERCASE, CaseMapping.UPPERCASE)) {
            TermOrders orders = ordersOf(through);
            for (long each : new long[] {0, 1, 3}) {
                TermRealizations.Realization made = TermRealizations.at(Type.STRING, orders,
                        Count.of(each), NothingTheRulesSay.REGION, READING);
                if (through == CaseMapping.UPPERCASE) {
                    // No code point of [a-z0-9] is what an uppercase makes of a letter, so only
                    // the digits can be counted, and a count of none is the one that is offered.
                    assertTrue(each == 0 || made instanceof TermRealizations.Realization.Built,
                            made.toString());
                }
                if (made instanceof TermRealizations.Realization.Built built) {
                    for (FixtureTemplate value : built.values()) {
                        String offered = assertInstanceOf(Hir.StringLit.class, value.value())
                                .value();
                        assertEquals(new NumericTerm.Reading.Number(Count.of(each)),
                                orders.read(new ObservedValue.Text(offered)),
                                "built " + value.text() + " for " + each + " of " + through);
                    }
                }
            }
        }
    }

    /**
     * A rule on whether the answer of a conversion holds a letter or a digit divides the string in
     * two, and each side has a string that is on it by the run time's own answer: the oracle is
     * the conversion and a plain test of what it answered, and nothing of this compiler's.
     */
    @Test
    void aStringIsDividedByWhetherItsConversionHoldsAnAsciiLetterOrADigit() {
        // The conversions as the model writes them, the letters it keeps, and what the run time
        // makes of a string: the two ways of writing one conversion, and one of a conversion.
        record Case(String written, String keeps, Function<String, String> made) {}
        for (Case each : List.of(
                new Case("String.lowercase", "[a-z0-9]", Strings::lowercase),
                new Case("String.uppercase", "[A-Z0-9]", Strings::uppercase),
                new Case("String.uppercase |> String.lowercase", "[a-z0-9]",
                        text -> Strings.lowercase(Strings.uppercase(text))))) {
            for (String model : List.of(inline(each.written(), each.keeps()),
                    throughAHelper(each.written(), each.keeps()))) {
                List<List<String>> sides = representativesOfEachClass(model);
                String said = each.written() + " in " + model;
                assertEquals(2, sides.size(), said);
                for (List<String> side : sides) {
                    assertFalse(side.isEmpty(), "a string on every side of " + said);
                }
                Predicate<String> holds = text -> each.made().apply(text).codePoints()
                        .anyMatch(code -> each.keeps().equals("[a-z0-9]")
                                ? code >= '0' && code <= '9' || code >= 'a' && code <= 'z'
                                : code >= '0' && code <= '9' || code >= 'A' && code <= 'Z');
                assertTrue(sides.get(0).stream().noneMatch(holds), said + ": " + sides.get(0));
                assertTrue(sides.get(1).stream().allMatch(holds), said + ": " + sides.get(1));
            }
        }
    }

    /** The condition written in the guard itself. */
    private static String inline(String conversion, String letters) {
        return """
                module probe.conversion
                data Title = String
                    invariant String.length(value) >= 1 && String.length(value) <= 40
                data Ok
                data No
                behavior f : (title: Title) -> Ok | No
                let f (title) = {
                    guard String.length(title.value |> %s |> String.characters
                        |> List.map(c -> if String.matches("%s", c) then c else " ")
                        |> String.concat |> String.trim) >= 1 else No
                    Ok
                }
                """.formatted(conversion, letters);
    }

    /** The condition written as a helper the guard calls, which is how an author would. */
    private static String throughAHelper(String conversion, String letters) {
        return """
                module probe.conversion
                data Title = String
                    invariant String.length(value) >= 1 && String.length(value) <= 40
                data Ok
                data No
                let t (title: Title): String = title.value |> %s |> String.characters |> List.map(c -> if String.matches("%s", c) then c else " ") |> String.concat |> String.trim
                behavior f : (title: Title) -> Ok | No
                let f (title) = {
                    guard String.length(t(title)) >= 1 else No
                    Ok
                }
                """.formatted(conversion, letters);
    }

    /** The strings that stand for each class of the one position of {@code f}, in the order the
     *  classes are. */
    private static List<List<String>> representativesOfEachClass(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        GuardThresholds.Guards guards = ThresholdFixtures.guardsOf("f",
                checked.analysisBodies().get("f"), checked.behaviorBodies().get("f"),
                checked.plan(),
                compilation.db().ask(new Adequacy.Inputs(module)).value().get("f"), rules);
        RuleReadingContext ruleReading =
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES);
        InputDomain read = InputDomain.of(sigs.get("f"), ruleReading,
                TypeCardinality.Counts.workedOutIn(ruleReading), Membership.none());
        Quantities reading = read.quantities(rules);
        Partitions.Partitioning divided = ThresholdFixtures.withThresholds(
                Partitions.of("f", read.reading(rules), ReadAs.THE_COMPILATION_DOES), reading,
                guards.thresholds(), ruleReading, RulesWithNoLine.NONE, guards.singled(),
                Allowance.of(PatternPlan.Budget.OF_BEHAVIOR_DISTINCTIONS));
        List<List<String>> out = new ArrayList<>();
        for (Axis axis : divided.axes()) {
            for (PartitionClass each : axis.classes()) {
                out.add(Partitions.standingFor(each.representatives(), ruleReading, Set.of())
                        .values().stream().map(FixtureTemplate::text)
                        .map(written -> written.substring(written.indexOf('"') + 1,
                                written.lastIndexOf('"')))
                        .filter(text -> !text.isEmpty()).toList());
            }
        }
        return out;
    }

    /**
     * Every count is one some string answers only where a code point the class counts is left as it
     * is by the conversion, which is what a string of that many of it is written with: the lowercase
     * leaves a lowercase letter, and the uppercase leaves no code point of a class of lowercase
     * letters, which it makes into capitals.
     */
    @Test
    void everyCountIsWrittenOnlyWhereTheConversionLeavesACodePointOfTheClass() {
        assertTrue(TermRealizations.writesEveryCountOf(ASCII_ALPHANUMERIC, CaseMapping.NONE));
        assertTrue(TermRealizations.writesEveryCountOf(ASCII_ALPHANUMERIC,
                CaseMapping.LOWERCASE));
        assertFalse(TermRealizations.writesEveryCountOf(LOWERCASE_LETTERS,
                CaseMapping.UPPERCASE));
    }
}
