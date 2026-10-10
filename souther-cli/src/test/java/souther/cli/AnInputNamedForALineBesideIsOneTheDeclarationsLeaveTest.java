package souther.cli;

import org.junit.jupiter.api.Test;
import souther.test.Nightly;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * The input a sentence about the line beside a border names is one the declared types leave a
 * value at.
 *
 * <p>The input is worked out by stepping along the line, and a step is arithmetic: over a sum of
 * amounts that cannot be negative it can land on a negative one, which no row can be written at.
 * The model is a month's taxable amount, whose line crosses a cap on one of the amounts, and whose
 * rows meet every point of every line it draws.
 *
 * <p>Asked once a night. Seven positions and fifteen rows make a search that takes minutes, and
 * the model cannot be made smaller: the sentence only appears once every point of every line has a
 * row, and the step only lands below zero where a cap on one position sits in the sum. A
 * defect here is as well found by the morning as by the change that caused it.
 */
@Nightly
class AnInputNamedForALineBesideIsOneTheDeclarationsLeaveTest {

    private static final String MODEL = """
            module m

            data Yen = Int
                invariant value >= 0

            data Pay =
                { baseSalary: Yen
                , scheduledAllowances: Yen
                , commutingAllowance: Yen
                , excludedAllowances: Yen
                , variableAllowances: Yen
                }

            let total (r: Pay): Yen =
                r.baseSalary + r.scheduledAllowances + r.commutingAllowance
                    + r.excludedAllowances + r.variableAllowances

            let ceiling = Yen(150000)

            let exempt (r: Pay): Yen =
                if r.commutingAllowance > ceiling then ceiling else r.commutingAllowance

            data Excess

            behavior taxable : (pay: Pay, uplift: Yen, premium: Yen) -> Yen | Excess
                constructs Yen

            let taxable (pay, uplift, premium) = {
                let gross = total(pay) + uplift
                let subtracted = exempt(pay) + premium
                guard gross >= subtracted else Excess
                Yen(gross.value - subtracted.value)
            }

            example taxable
              | (Pay { baseSalary = Yen(260000), scheduledAllowances = Yen(20000), commutingAllowance = Yen(15000), excludedAllowances = Yen(5000), variableAllowances = Yen(0) }, Yen(22750), Yen(43965)) -> Yen(263785)
              | (Pay { baseSalary = Yen(0), scheduledAllowances = Yen(0), commutingAllowance = Yen(150001), excludedAllowances = Yen(0), variableAllowances = Yen(0) }, Yen(0), Yen(3)) -> Excess
              | (Pay { baseSalary = Yen(260001), scheduledAllowances = Yen(20000), commutingAllowance = Yen(0), excludedAllowances = Yen(4999), variableAllowances = Yen(0) }, Yen(0), Yen(285000)) -> Yen(0)
              | (Pay { baseSalary = Yen(260000), scheduledAllowances = Yen(20000), commutingAllowance = Yen(150000), excludedAllowances = Yen(5000), variableAllowances = Yen(0) }, Yen(0), Yen(0)) -> Yen(285000)
              | (Pay { baseSalary = Yen(260000), scheduledAllowances = Yen(20000), commutingAllowance = Yen(150001), excludedAllowances = Yen(5000), variableAllowances = Yen(0) }, Yen(0), Yen(0)) -> Yen(285001)
              | (Pay { baseSalary = Yen(260000), scheduledAllowances = Yen(20000), commutingAllowance = Yen(200000), excludedAllowances = Yen(5000), variableAllowances = Yen(0) }, Yen(0), Yen(0)) -> Yen(335000)
              | (Pay { baseSalary = Yen(260000), scheduledAllowances = Yen(20000), commutingAllowance = Yen(15000), excludedAllowances = Yen(5000), variableAllowances = Yen(0) }, Yen(0), Yen(285000)) -> Yen(0)
              | (Pay { baseSalary = Yen(260000), scheduledAllowances = Yen(20000), commutingAllowance = Yen(15000), excludedAllowances = Yen(5000), variableAllowances = Yen(0) }, Yen(0), Yen(285001)) -> Excess
              | (Pay { baseSalary = Yen(0), scheduledAllowances = Yen(0), commutingAllowance = Yen(150001), excludedAllowances = Yen(0), variableAllowances = Yen(0) }, Yen(0), Yen(1)) -> Yen(0)
              | (Pay { baseSalary = Yen(0), scheduledAllowances = Yen(0), commutingAllowance = Yen(150001), excludedAllowances = Yen(0), variableAllowances = Yen(0) }, Yen(0), Yen(2)) -> Excess
              | (Pay { baseSalary = Yen(0), scheduledAllowances = Yen(0), commutingAllowance = Yen(0), excludedAllowances = Yen(0), variableAllowances = Yen(0) }, Yen(0), Yen(2)) -> Excess
              | (Pay { baseSalary = Yen(10000), scheduledAllowances = Yen(0), commutingAllowance = Yen(150001), excludedAllowances = Yen(0), variableAllowances = Yen(0) }, Yen(0), Yen(10001)) -> Yen(0)
              | (Pay { baseSalary = Yen(259999), scheduledAllowances = Yen(20000), commutingAllowance = Yen(0), excludedAllowances = Yen(5001), variableAllowances = Yen(0) }, Yen(0), Yen(285000)) -> Yen(0)
              | (Pay { baseSalary = Yen(100000), scheduledAllowances = Yen(30000), commutingAllowance = Yen(0), excludedAllowances = Yen(7000), variableAllowances = Yen(3000) }, Yen(0), Yen(140000)) -> Yen(0)
              | (Pay { baseSalary = Yen(20000), scheduledAllowances = Yen(3000), commutingAllowance = Yen(150001), excludedAllowances = Yen(1000), variableAllowances = Yen(500) }, Yen(700), Yen(25201)) -> Yen(0)
            """;

    @Test
    void noInputATypeRefusesIsNamedOrOffered() {
        String report = run(MODEL);

        List<String> sentences = findings(report);
        assertFalse(sentences.isEmpty(),
                () -> "the rows leave lines standing beside the ones this model draws:\n" + report);
        for (String sentence : sentences) {
            assertFalse(sentence.contains("= -"),
                    () -> "an amount that cannot be negative is named as one: " + sentence);
        }
        for (String line : report.split("\n")) {
            String said = line.strip();
            if (said.startsWith("| (") && said.endsWith("-> <?>")) {
                assertFalse(said.substring(0, said.indexOf("->")).contains("-"),
                        () -> "a row is offered at an input a type refuses: " + said);
            }
        }
    }

    private static List<String> findings(String report) {
        List<String> said = new ArrayList<>();
        for (String line : report.split("\n")) {
            if (line.contains("no row tells")) {
                said.add(line.strip());
            }
        }
        return said;
    }

    private static String run(String source) {
        try {
            Path file = Files.createTempDirectory("souther-declared").resolve("m.sou");
            Files.writeString(file, source);
            PrintStream out = System.out;
            PrintStream err = System.err;
            ByteArrayOutputStream said = new ByteArrayOutputStream();
            System.setOut(new PrintStream(said, true, StandardCharsets.UTF_8));
            System.setErr(new PrintStream(said, true, StandardCharsets.UTF_8));
            try {
                Main.dispatch(new String[] {"examples", "--generate", file.toString()});
            } finally {
                System.setOut(out);
                System.setErr(err);
            }
            return said.toString(StandardCharsets.UTF_8);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }
}
