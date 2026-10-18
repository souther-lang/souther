package souther.compiler;

import souther.compiler.diag.SourceRendering;
import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.GeneratedRows;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value its declarations hold to a class is offered a member of the class, wherever in a row it
 * is chosen.
 *
 * <p>Every place a value is chosen at, and not only the one a line is drawn on. The rest of a row —
 * a field the body never reads, a parameter it never reads, a position a row has to pass on the
 * way to the line — is chosen out of what the rules leave it as much as the position the line is
 * on, and a value chosen there off where it stops alone is the start of its order: nought, or the
 * first of January. Of the class only by luck, and where it is not, every row built around it is
 * refused and the line is reported as one nothing could write a row at.
 */
class AValueHeldToAClassIsOfferedAMemberOfItTest {

    private static String offered(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return GeneratedRows.of(
                Adequacy.offeredFor(compilation.db(), OfferingRequest.overTheModule("m")),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()), compilation.db())
                .text();
    }

    /** A field the body never reads, held to a remainder and to a day of the month. */
    @Test
    void aFieldTheBodyDoesNotReadIsOfferedAMemberOfItsClass() {
        String remainder = offered("""
                module m

                data P = { pay: Int, n: Int }
                    invariant Int.floorMod(pay, 7) == 3

                behavior late : (p: P) -> Bool

                let late (p) = p.n > 15
                """);
        assertTrue(remainder.contains("(P { pay = 3, n = 16 })"), remainder);

        String day = offered("""
                module m

                data P = { pay: Date, n: Int }
                    invariant Date.day(pay) == 2

                behavior late : (p: P) -> Bool

                let late (p) = p.n > 15
                """);
        assertTrue(day.contains("(P { pay = Date(\"2000-01-02\"), n = 16 })"), day);
    }

    /** A parameter the body never reads, whose own rules hold it to a class. */
    @Test
    void aParameterTheBodyDoesNotReadIsOfferedAMemberOfItsClass() {
        String offered = offered("""
                module m

                data T = Int
                    invariant Int.floorMod(value, 7) == 3

                behavior late : (t: T, n: Int) -> Bool

                let late (t, n) = n > 15
                """);
        assertTrue(offered.contains("(T(3), 16)"), offered);
    }

    /**
     * A position a row passes on the way to the line, and the position the line is on.
     *
     * <p>The row at the line on {@code n} has to have come past {@code pay > 2024-05-15} first, and
     * the first date past that a value held to the first of each month can be is the first of June.
     * And the rows on either side of the line on the date itself are the first of a month on each
     * side.
     */
    @Test
    void aPositionOnTheWayAndOneALineIsOnAreOfferedMembers() {
        String onTheWay = offered("""
                module m

                data P = { pay: Date, n: Int }
                    invariant Date.day(pay) == 1 && Int.floorMod(n, 10) == 0

                behavior late : (p: P) -> Bool

                let late (p) = p.pay > Date("2024-05-15") && p.n > 15
                """);
        assertTrue(onTheWay.contains("(P { pay = Date(\"2024-06-01\"), n = 20 })"), onTheWay);

        String itself = offered("""
                module m

                data V = Date
                    invariant Date.day(value) == 1

                behavior f : (v: V) -> Bool

                let f (v) = v.value > Date("2024-05-10")
                """);
        assertTrue(itself.contains("(V(Date(\"2024-05-01\")))"), itself);
        assertTrue(itself.contains("(V(Date(\"2024-06-01\")))"), itself);
    }

    /**
     * A value held to a class and related to another, so that where it may stand turns on where
     * the other was put: every row offered has it at the first of a month, on both sides of the
     * line the relation draws.
     */
    @Test
    void aValueRelatedToAnotherIsOfferedAMemberOnEverySide() {
        String offered = offered("""
                module m

                data Month = Date
                    invariant Date.day(value) == 1

                behavior soon : (m: Month, d: Date, n: Int) -> Bool

                let soon (m, d, n) = Date.daysBetween(m.value, d) + n > 3
                """);
        List<String> months = new ArrayList<>();
        Matcher found = Pattern.compile("Month\\(Date\\(\"([0-9-]+)\"\\)\\)").matcher(offered);
        while (found.find()) {
            months.add(found.group(1));
        }
        assertTrue(months.size() >= 2, "a row on each side of the line:\n" + offered);
        assertTrue(months.stream().allMatch(each -> each.endsWith("-01")), offered);
    }
}
