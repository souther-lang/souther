package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.PointRole;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Rules that divide a position in one place are read as one division, however they were written.
 *
 * <p>Three ways two rules can say one thing, and the measures have to agree with all three. Two of
 * them are about the arithmetic: {@code n > 10} and {@code 2 * n > 20} are the same line said at two
 * scales, and {@code n + 1 > 11} is the same line with the constant on the other side. The third is
 * about the carrier: {@code n <= 4} and {@code n < 5} are two comparisons and one division of the
 * whole numbers, because nothing lies between four and five for them to disagree over.
 *
 * <p>The fourth thing they have to agree about is where they do not agree. A third is no decimal
 * this language writes, so {@code 3 * d <= 1} is not {@code d <= 0.333...} and the rows it asks for
 * are not the rows that one would ask for.
 */
class OneDivisionReadsAlikeHoweverItIsWrittenTest {

    /** What the report says about the one position, as the classes and the four points of each
     *  border. */
    private static List<String> readingOf(String type, String guard) {
        Compilation compilation = Compilation.ofSource("""
                module example.same

                data Yes = { n: %s }
                data No = { n: %s }

                behavior f : (n: %s) -> Yes | No
                    constructs Yes, No

                let f (n) = {
                    guard %s else No { n = n }
                    Yes { n = n }
                }

                example f
                    | (%s) -> Yes { n = %s }
                """.formatted(type, type, type, guard,
                        type.equals("Decimal") ? "0.1m" : "1",
                        type.equals("Decimal") ? "0.1m" : "1"), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, PartitionEvidence> all = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value();
        assertNotNull(all, "the model under test compiles: " + guard);
        PartitionEvidence evidence = all.get("f");
        List<String> read = new ArrayList<>();
        // How many classes and not what they are called. A class keeps the number the rule that
        // drew it was written with — an author who wrote `< 240` is shown 240 and not 239 — so two
        // spellings of one division name the same two classes differently. What has to agree is the
        // division: how many there are, and what each of the border's four points asks for.
        evidence.axes().forEach(axis -> read.add("classes " + axis.classes().size()));
        for (BorderAssessment border : evidence.boundaries()) {
            for (PointRole role : PointRole.values()) {
                read.add(role + " " + border.operator(role) + " " + border.against(role));
            }
        }
        return read;
    }

    /** That every one of {@code guards} is read the same way, named by the first of them. */
    private static void allAlike(String type, String... guards) {
        List<String> first = readingOf(type, guards[0]);
        for (String guard : guards) {
            assertEquals(first, readingOf(type, guard),
                    "`" + guard + "` divides the position where `" + guards[0] + "` does");
        }
    }

    /**
     * One line at four scales and with the constant on either side.
     *
     * <p>A form and any positive multiple of it order the rows the same way, and where the constant
     * sits is a fact about the writing. All four part the whole numbers between ten and eleven.
     */
    @Test
    void aLineIsOneLineAtEveryScaleTheRuleCouldBeWrittenAt() {
        allAlike("Int", "n > 10", "2 * n > 20", "3 * n > 30", "n + 1 > 11");
    }

    /**
     * And two operators that leave nothing between them are one line.
     *
     * <p>Nothing lies between four and five on the whole numbers, so {@code <= 4} and {@code < 5}
     * keep and give away the same values. A reading that told them apart by the number each carried
     * left a class between them holding nothing.
     */
    @Test
    void twoOperatorsWithNothingBetweenThemAreOneLine() {
        allAlike("Int", "n <= 4", "n < 5", "2 * n <= 9", "2 * n <= 8");
    }

    /**
     * And a line at a place the carrier names no value at is not moved to one it does.
     *
     * <p>{@code 3 * d} takes every third of a finite decimal and no whole number of thirds. The rule
     * cuts at a third, which is not {@code 0.333...} and not {@code 0.334}: divided out and rounded,
     * the report would ask for rows either side of a line the model does not draw.
     */
    @Test
    void aLineAtAPlaceTheCarrierNamesNoValueAtIsNotMovedToOneItDoes() {
        List<String> exact = readingOf("Decimal", "3m * n <= 1m");

        assertEquals(List.of(), exact.stream().filter(each -> each.contains("0.33")).toList(),
                "no third is written out: " + exact);
    }
}
