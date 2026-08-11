package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.Main;
import souther.compiler.ast.Ast;
import souther.compiler.check.Resolve;
import souther.compiler.check.Symbols;
import souther.compiler.frontend.CstFrontend;
import souther.compiler.types.Type;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A sum every case of which is a record has values, and every reader that asks for one is told so.
 *
 * <p>{@code Values} and {@code Compose} are two ways of arriving at a representative and not two
 * answers about whether there is one. A reader that took the first and dropped the second reported
 * a position as having no value in the same report where another reader wrote one — which is issue
 * #651, and which is one function's answer read in five places.
 */
class ACaseComposedForOneReaderIsComposedForEveryReaderTest {

    private static final String MODULE = """
            module demo

            data Yen = Int invariant value >= 0
            data Ok = { n: Int }

            data Boxed = { x: Int }
            data Labelled = { s: String }
            data EveryCaseARecord = Boxed | Labelled

            data Wrapped = EveryCaseARecord

            behavior recordCases : (bill: Yen, v: EveryCaseARecord) -> Ok
                constructs Ok
            let recordCases (bill, v) = Ok { n = bill.value }

            example recordCases | (Yen(5), Boxed { x = 1 }) -> Ok { n = 5 }
            """;

    private final Symbols symbols = Symbols.of(resolved());

    private static Ast.Module resolved() {
        Ast.Module parsed = CstFrontend.parse(MODULE);
        return Resolve.module(parsed, Symbols.of(parsed));
    }

    private Type named(String name) {
        return Type.ref(symbols.own(name));
    }

    private Type sum() {
        return named("EveryCaseARecord");
    }

    // --- the position a row is not about ---------------------------------------------------------

    /** The boundary strategy fills every other position, and one that is a sum is one of them. */
    @Test
    void aBoundaryRowIsOfferedWhereACompanionPositionIsASumOfRecords() throws Exception {
        String report = generated();

        List<String> rows = report.lines().filter(line -> line.startsWith("//     | ")).toList();
        assertTrue(rows.stream().anyMatch(line -> line.contains("bill = 0")),
                () -> "the row at the boundary is offered: " + rows);
    }

    /** And the sentence that says otherwise is not printed beside the row that disproves it. */
    @Test
    void nothingSaysThePositionHasNoValue() throws Exception {
        String report = generated();

        assertFalse(report.contains("no value can be written there"),
                () -> "a case was composed two lines above:\n" + report);
    }

    // --- the same question, asked by the other readers --------------------------------------------

    /** What an optional holds is what stands for its element, composed or not. */
    @Test
    void theSomeOfAnOptionalSumOfRecordsIsGeneratable() {
        PartitionClass some = PartitionClasses.of(new Type.OptionOf(sum()), symbols).stream()
                .filter(each -> each.id().equals("Some")).findFirst().orElseThrow();

        assertTrue(some.generatable(),
                () -> "`Some` stands for a value that composes: " + some.representatives());
    }

    /** A collection whose rules ask it to hold one is built from what stands for its element. */
    @Test
    void aCollectionRequiredToHoldOneOfASumOfRecordsIsBuilt() {
        List<FixtureTemplate> held =
                Witnesses.holding(new Type.ListOf(sum()), 1, symbols, Set.of());

        assertFalse(held.isEmpty(), "a list of one is built from a case of the sum");
    }

    /** Two of them, which is the reading that asks what the type divides into rather than what
     *  stands for it. */
    @Test
    void aSetOfTwoIsBuiltFromTwoCasesOfASumOfRecords() {
        List<FixtureTemplate> held =
                Witnesses.holding(new Type.SetOf(sum()), 2, symbols, Set.of());

        assertFalse(held.isEmpty(), "the two cases are two distinct values");
    }

    /** A name round the sum is a name round what stands for it. */
    @Test
    void aNewtypeOverASumOfRecordsHasARepresentative() {
        List<FixtureTemplate> stands = Partitions.representativesOf(named("Wrapped"), symbols);

        assertTrue(stands.stream().anyMatch(each -> each.text().startsWith("Wrapped(")),
                () -> "written under the name the position wears: " + stands);
    }

    // --- what a class says it is, once ------------------------------------------------------------

    /** Every class of the sum offers a representative: none of them is a class nothing produces a
     *  value for. */
    @Test
    void everyCaseOfTheSumStandsForSomething() {
        for (PartitionClass each : PartitionClasses.of(sum(), symbols)) {
            assertFalse(Partitions.representativesOf(named(each.id()), symbols).isEmpty(),
                    () -> "a record case stands for a value: " + each.id());
        }
    }

    /**
     * A recipe of no values is not a recipe.
     *
     * <p>Held as one, a class offering nothing and saying nothing about why was a class the search
     * met and had no reading for, and what it wrote down was read as the position having no value.
     * A class that cannot produce one says so and says why, which is {@link
     * RepresentativeSource.Ungeneratable}; there is nothing left for an empty list to mean.
     */
    @Test
    void aRecipeOfNoValuesCannotBeWritten() {
        assertThrows(IllegalArgumentException.class, () -> RepresentativeSource.of(List.of()));
    }

    private static String generated() throws Exception {
        Path file = Files.createTempDirectory("souther-651").resolve("model.sou");
        Files.writeString(file, MODULE);
        PrintStream was = System.out;
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        try {
            Main.main(new String[] {"examples", file.toString(), "--generate", "--boundaries"});
        } finally {
            System.setOut(was);
        }
        return out.toString(StandardCharsets.UTF_8);
    }
}
