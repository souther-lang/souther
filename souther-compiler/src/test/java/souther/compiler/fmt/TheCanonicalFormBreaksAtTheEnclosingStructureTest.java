package souther.compiler.fmt;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The canonical width applies to every breakable construct, declarations included, and a construct
 * that does not fit breaks at its own separator rather than inside one of its members.
 *
 * <p>Each row of {@link #shapes} is one repeated or joined construct, written long enough not to
 * fit, against the multi-line form it is required to take. A construct with no row here is a
 * construct whose canonical form nothing pins.
 */
class TheCanonicalFormBreaksAtTheEnclosingStructureTest {

    private static final int WIDTH = 100;

    /**
     * @param source the construct on one line, over the width
     * @param brokenSource the same construct broken somewhere the canonical form does not break — a
     *     legal layout that is not this one, so that reaching {@code expected} from it says the
     *     layout carried no meaning rather than repeating that {@code expected} is a fixed point
     * @param expected the canonical form
     */
    record Shape(String name, String source, String brokenSource, String expected) {
        @Override
        public String toString() {
            return name;
        }
    }

    static Stream<Shape> shapes() {
        return Stream.of(
                new Shape("exposing",
                        """
                        module fmtprobe exposing ( AlphaType, BetaType, GammaType, DeltaType, EpsilonType, ZetaType, EtaType )
                        """,
                        """
                        module fmtprobe exposing (
                            AlphaType, BetaType, GammaType,
                            DeltaType, EpsilonType, ZetaType, EtaType )
                        """,
                        """
                        module fmtprobe exposing (
                            AlphaType,
                            BetaType,
                            GammaType,
                            DeltaType,
                            EpsilonType,
                            ZetaType,
                            EtaType
                        )
                        """),

                new Shape("import name list",
                        """
                        module fmtprobe exposing ( f )

                        import some.other.place ( alphaName, betaName, gammaName, deltaName, epsilonName, zetaName, etaName, thetaName )
                        """,
                        """
                        module fmtprobe exposing ( f )
                        import some.other.place ( alphaName, betaName,
                            gammaName, deltaName, epsilonName,
                            zetaName, etaName, thetaName )
                        """,
                        """
                        module fmtprobe exposing ( f )
                        import some.other.place (
                            alphaName,
                            betaName,
                            gammaName,
                            deltaName,
                            epsilonName,
                            zetaName,
                            etaName,
                            thetaName
                        )
                        """),

                new Shape("behavior parameter list",
                        """
                        module fmtprobe exposing ( settle )

                        behavior settleTheOutstandingBalance : (accountIdentifier: AccountId, requestedAmount: Amount, effectiveDate: Date) -> Receipt
                        """,
                        """
                        module fmtprobe exposing ( settle )

                        behavior settleTheOutstandingBalance : (accountIdentifier: AccountId,
                            requestedAmount: Amount, effectiveDate: Date) -> Receipt
                        """,
                        """
                        module fmtprobe exposing ( settle )

                        behavior settleTheOutstandingBalance : (
                            accountIdentifier: AccountId,
                            requestedAmount: Amount,
                            effectiveDate: Date
                        ) -> Receipt
                        """),

                new Shape("definition parameter list",
                        """
                        module fmtprobe exposing ( f )

                        let settleTheOutstandingBalance (accountIdentifier: AccountId, requestedAmount: Amount, effectiveDate: Date): Receipt = accountIdentifier
                        """,
                        """
                        module fmtprobe exposing ( f )

                        let settleTheOutstandingBalance (accountIdentifier: AccountId, requestedAmount: Amount,
                            effectiveDate: Date): Receipt = accountIdentifier
                        """,
                        """
                        module fmtprobe exposing ( f )

                        let settleTheOutstandingBalance (
                            accountIdentifier: AccountId,
                            requestedAmount: Amount,
                            effectiveDate: Date
                        ): Receipt = accountIdentifier
                        """),

                new Shape("return type union",
                        """
                        module fmtprobe exposing ( judge )

                        behavior judge : (code: Code) -> AcceptedOutcome | RefusedOutcome | DeferredOutcome | EscalatedOutcome
                        """,
                        """
                        module fmtprobe exposing ( judge )

                        behavior judge : (code: Code) -> AcceptedOutcome | RefusedOutcome |
                            DeferredOutcome | EscalatedOutcome
                        """,
                        """
                        module fmtprobe exposing ( judge )

                        behavior judge : (code: Code) -> AcceptedOutcome
                            | RefusedOutcome
                            | DeferredOutcome
                            | EscalatedOutcome
                        """),

                new Shape("sum cases",
                        """
                        module fmtprobe exposing ( Verdict )

                        data Verdict = AcceptedOutright | RefusedOutright | DeferredForReview | EscalatedToManager | WithdrawnByCustomer
                        """,
                        """
                        module fmtprobe exposing ( Verdict )

                        data Verdict = AcceptedOutright | RefusedOutright |
                            DeferredForReview | EscalatedToManager |
                            WithdrawnByCustomer
                        """,
                        """
                        module fmtprobe exposing ( Verdict )

                        data Verdict = AcceptedOutright
                            | RefusedOutright
                            | DeferredForReview
                            | EscalatedToManager
                            | WithdrawnByCustomer
                        """),

                new Shape("constructs clause",
                        """
                        module fmtprobe exposing ( b )

                        behavior b : (a: A) -> R
                            constructs FirstConstructed, SecondConstructed, ThirdConstructed, FourthConstructed, FifthConstructed, SixthConstructed
                        """,
                        """
                        module fmtprobe exposing ( b )

                        behavior b : (a: A) -> R
                            constructs FirstConstructed, SecondConstructed,
                                ThirdConstructed, FourthConstructed,
                                FifthConstructed, SixthConstructed
                        """,
                        """
                        module fmtprobe exposing ( b )

                        behavior b : (a: A) -> R
                            constructs FirstConstructed,
                                SecondConstructed,
                                ThirdConstructed,
                                FourthConstructed,
                                FifthConstructed,
                                SixthConstructed
                        """),

                new Shape("tuple expression",
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int = (aLongEnoughName, anotherLongEnoughName, yetAnotherLongName, andTheVeryLastOne, andOneFinalName, andReallyTheLast)
                        """,
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int = (aLongEnoughName,
                            anotherLongEnoughName, yetAnotherLongName, andTheVeryLastOne,
                            andOneFinalName, andReallyTheLast)
                        """,
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int =
                            (
                                aLongEnoughName,
                                anotherLongEnoughName,
                                yetAnotherLongName,
                                andTheVeryLastOne,
                                andOneFinalName,
                                andReallyTheLast
                            )
                        """),

                new Shape("operator chain",
                        """
                        module fmtprobe exposing ( f )

                        let lateNightMinutes (s: Int, e: Int): Int = overlapLength(s, e, 0, lateNightMorningEnd) + overlapLength(s, e, lateNightEveningStart, minutesInADay)
                        """,
                        """
                        module fmtprobe exposing ( f )

                        let lateNightMinutes (s: Int, e: Int): Int = overlapLength(s, e, 0, lateNightMorningEnd) +
                            overlapLength(s, e, lateNightEveningStart, minutesInADay)
                        """,
                        """
                        module fmtprobe exposing ( f )

                        let lateNightMinutes (s: Int, e: Int): Int =
                            overlapLength(s, e, 0, lateNightMorningEnd)
                                + overlapLength(s, e, lateNightEveningStart, minutesInADay)
                        """),

                new Shape("example row",
                        """
                        module fmtprobe exposing ( judge )

                        example judge
                            | "an amount that sits exactly on the line is accepted rather than refused" : (Code("c-1"), Amount(100)) -> Accepted
                        """,
                        // what the formatter used to write, which is where #431 started
                        """
                        module fmtprobe exposing ( judge )

                        example judge
                            | "an amount that sits exactly on the line is accepted rather than refused" : (Code(
                                "c-1"
                            ), Amount(100)) -> Accepted
                        """,
                        """
                        module fmtprobe exposing ( judge )

                        example judge
                            | "an amount that sits exactly on the line is accepted rather than refused"
                                : (Code("c-1"), Amount(100))
                                -> Accepted
                        """),

                new Shape("match case",
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int = match a with | Zero -> aVeryLongFunctionName(withSomeArgument, andAnotherOne, andYetAnotherOne, andFinalOne)
                        """,
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int = match a with
                            | Zero -> aVeryLongFunctionName(withSomeArgument,
                                andAnotherOne, andYetAnotherOne, andFinalOne)
                        """,
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int =
                            match a with
                                | Zero
                                    -> aVeryLongFunctionName(withSomeArgument, andAnotherOne, andYetAnotherOne, andFinalOne)
                        """),

                new Shape("lambda in an expression",
                        """
                        module fmtprobe exposing ( f )

                        let f (xs: Int): Int = consume((firstVeryLongParameter, secondVeryLongParameter, thirdVeryLongParameter) -> firstVeryLongParameter)
                        """,
                        """
                        module fmtprobe exposing ( f )

                        let f (xs: Int): Int = consume((firstVeryLongParameter,
                            secondVeryLongParameter, thirdVeryLongParameter) -> firstVeryLongParameter)
                        """,
                        """
                        module fmtprobe exposing ( f )

                        let f (xs: Int): Int =
                            consume(
                                (
                                    firstVeryLongParameter,
                                    secondVeryLongParameter,
                                    thirdVeryLongParameter
                                ) -> firstVeryLongParameter
                            )
                        """),

                new Shape("intrinsic body",
                        """
                        module fmtprobe exposing ( f )

                        let truncatingRemainder (dividend: Int, divisor: Int): Int | DivisionByZero = intrinsic "int.truncatingRemainder"
                        """,
                        """
                        module fmtprobe exposing ( f )

                        let truncatingRemainder (dividend: Int,
                            divisor: Int): Int | DivisionByZero = intrinsic "int.truncatingRemainder"
                        """,
                        """
                        module fmtprobe exposing ( f )

                        let truncatingRemainder (dividend: Int, divisor: Int): Int | DivisionByZero =
                            intrinsic "int.truncatingRemainder"
                        """),

                new Shape("call arguments",
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int = aFunctionWithAName(aLongEnoughName, anotherLongEnoughName, yetAnotherLongName, andTheVeryLastOne)
                        """,
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int = aFunctionWithAName(aLongEnoughName, anotherLongEnoughName,
                            yetAnotherLongName, andTheVeryLastOne)
                        """,
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int =
                            aFunctionWithAName(
                                aLongEnoughName,
                                anotherLongEnoughName,
                                yetAnotherLongName,
                                andTheVeryLastOne
                            )
                        """),

                new Shape("record literal",
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int = Receipt { firstField = aLongEnoughName, secondField = anotherLongEnoughName, thirdField = yetAnotherName }
                        """,
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int = Receipt { firstField = aLongEnoughName,
                            secondField = anotherLongEnoughName, thirdField = yetAnotherName }
                        """,
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int =
                            Receipt {
                                firstField = aLongEnoughName,
                                secondField = anotherLongEnoughName,
                                thirdField = yetAnotherName
                            }
                        """),

                new Shape("list literal",
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int = [aLongEnoughName, anotherLongEnoughName, yetAnotherLongName, andTheVeryLastOne, andOneFinalName, andReallyTheLast]
                        """,
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int = [aLongEnoughName, anotherLongEnoughName,
                            yetAnotherLongName, andTheVeryLastOne,
                            andOneFinalName, andReallyTheLast]
                        """,
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int =
                            [
                                aLongEnoughName,
                                anotherLongEnoughName,
                                yetAnotherLongName,
                                andTheVeryLastOne,
                                andOneFinalName,
                                andReallyTheLast
                            ]
                        """));
    }

    /** Each source is written on one line, and that line has to be over the width — a fixture that
     * fits proves nothing about breaking, and would pass whatever the formatter did. */
    @ParameterizedTest(name = "{0}")
    @MethodSource("shapes")
    void theFixtureDoesNotFitOnOneLine(Shape shape) {
        int longest = 0;
        for (String line : shape.source().split("\n", -1)) {
            longest = Math.max(longest, line.length());
        }
        assertTrue(longest > WIDTH, shape.name() + " fits in " + longest + " columns");
    }

    /** The canonical multi-line form of each construct. */
    @ParameterizedTest(name = "{0}")
    @MethodSource("shapes")
    void canonicalMultilineShape(Shape shape) {
        assertEquals(shape.expected(), Formatter.format(shape.source()));
    }

    /** Every construct here has a break that resolves the overflow, so no line is left over the
     * width. This is not a general property of the formatter — a long pattern, an indivisible token
     * and a deep enough indent all leave a line over — it is a property of these fixtures, and it is
     * the one an unbreakable declaration fails. */
    @ParameterizedTest(name = "{0}")
    @MethodSource("shapes")
    void everyLineFitsTheWidth(Shape shape) {
        for (String line : Formatter.format(shape.source()).split("\n", -1)) {
            assertTrue(line.length() <= WIDTH,
                    "line of " + line.length() + " columns: " + line);
        }
    }

    /** Formatting the canonical form gives it back. */
    @ParameterizedTest(name = "{0}")
    @MethodSource("shapes")
    void theCanonicalFormIsAFixedPoint(Shape shape) {
        assertEquals(shape.expected(), Formatter.format(shape.expected()));
    }

    /** A source broken somewhere else legal reaches the same canonical form, so where the author put
     * the newlines carried nothing the tree does not have. The broken form is not the canonical one,
     * or this would only be asking again whether the canonical form is a fixed point. */
    @ParameterizedTest(name = "{0}")
    @MethodSource("shapes")
    void aDifferentLegalLayoutReachesTheSameCanonicalForm(Shape shape) {
        assertTrue(!shape.brokenSource().equals(shape.expected()),
                shape.name() + ": the broken source is the canonical form, so this asks nothing");
        assertEquals(shape.expected(), Formatter.format(shape.brokenSource()));
    }

    /**
     * @param membersOnTheirOwnLine each member against how many lines have to hold exactly it —
     *     a count, because one member left intact says nothing about the others
     */
    record Nesting(String name, String source, Map<String, Integer> membersOnTheirOwnLine) {
        @Override
        public String toString() {
            return name;
        }
    }

    private static Map<String, Integer> members(String a, int na, String b, int nb) {
        Map<String, Integer> out = new LinkedHashMap<>();
        out.put(a, na);
        out.put(b, nb);
        return out;
    }

    static Stream<Nesting> nestings() {
        return Stream.of(
                new Nesting("a call inside a call",
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int = outerFunction(innerFunction(aaa, bbb, ccc), innerFunction(aaa, bbb, ccc), innerFunction(aaa, bbb, ccc))
                        """,
                        members("innerFunction(aaa, bbb, ccc),", 2,
                                "innerFunction(aaa, bbb, ccc)", 1)),

                new Nesting("a call inside a tuple",
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int = (innerFunction(aaa, bbb, ccc), innerFunction(aaa, bbb, ccc), innerFunction(aaa, bbb, ccc), innerFunction(aaa, bbb, ccc))
                        """,
                        members("innerFunction(aaa, bbb, ccc),", 3,
                                "innerFunction(aaa, bbb, ccc)", 1)),

                new Nesting("a call inside an operator chain",
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int = innerFunction(aaa, bbb, ccc) + innerFunction(aaa, bbb, ccc) + innerFunction(aaa, bbb, ccc) + innerFunction(aaa, bbb, ccc)
                        """,
                        members("innerFunction(aaa, bbb, ccc)", 1,
                                "+ innerFunction(aaa, bbb, ccc)", 3)),

                new Nesting("a call inside an example row",
                        """
                        module fmtprobe exposing ( judge )

                        example judge
                            | "an amount that sits exactly on the line is accepted rather than refused" : (Code("c-1"), Amount(100)) -> Accepted
                        """,
                        members(": (Code(\"c-1\"), Amount(100))", 1,
                                "-> Accepted", 1)));
    }

    /**
     * The regression #431 leaves behind: every member that fits on a line of its own is written on
     * one, because the structure enclosing it took the break. The formatter used to descend past the
     * enclosing structure — which had no break to take — and split the first member that crossed the
     * width, so a row's three parts stopped being visible and calls written to look alike stopped
     * looking alike. Counted rather than found, since splitting one of three members leaves the
     * other two to be found.
     */
    @ParameterizedTest(name = "{0}")
    @MethodSource("nestings")
    void everyMemberStaysWholeWhenTheStructureAroundItCanBreak(Nesting nesting) {
        String formatted = Formatter.format(nesting.source());
        List<String> lines = List.of(formatted.split("\n", -1));
        for (Map.Entry<String, Integer> member : nesting.membersOnTheirOwnLine().entrySet()) {
            long held = lines.stream().filter(l -> l.strip().equals(member.getKey())).count();
            assertEquals(member.getValue().longValue(), held,
                    "lines holding `" + member.getKey() + "` and nothing else, in:\n" + formatted);
        }
    }
}
