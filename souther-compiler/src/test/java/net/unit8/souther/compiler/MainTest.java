package net.unit8.souther.compiler;

import net.unit8.souther.compiler.fmt.Formatter;
import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/** The CLI compiles a multi-file project, resolving imports across the given source files. */
class MainTest {

    @Test
    void compilesAMultiModuleProjectResolvingImports() throws Exception {
        Path dir = Files.createTempDirectory("souther-cli");
        Path a = dir.resolve("a.sou");
        Path b = dir.resolve("b.sou");
        Files.writeString(a, """
                module a exposing ( 従業員ID )

                import String ( length )

                data 従業員ID = String
                    invariant length(value) > 0
                """);
        Files.writeString(b, """
                module b

                import a ( 従業員ID )

                data Trip = { who: 従業員ID }
                """);
        Path out = Files.createTempDirectory("souther-cli-out");

        Main.compileToDir(List.of(a, b), out);

        assertTrue(Files.exists(out.resolve("a/従業員ID.class")), "module a's class is written");
        assertTrue(Files.exists(out.resolve("b/Trip.class")), "module b's class, which imports a, is written");
    }

    @Test
    void fmtPrintsCanonicalFormToStdout() throws Exception {
        Path f = Files.createTempDirectory("souther-fmt").resolve("m.sou");
        String messy = "module m\ndata X = { a: Int }\n";
        Files.writeString(f, messy);

        PrintStream original = System.out;
        ByteArrayOutputStream captured = new ByteArrayOutputStream();
        System.setOut(new PrintStream(captured, true, StandardCharsets.UTF_8));
        try {
            Main.main(new String[]{"fmt", f.toString()});
        } finally {
            System.setOut(original);
        }
        assertEquals(Formatter.format(messy), captured.toString(StandardCharsets.UTF_8));
    }

    @Test
    void fmtWriteRewritesTheFileInPlace() throws Exception {
        Path f = Files.createTempDirectory("souther-fmt").resolve("m.sou");
        String messy = "module m\ndata X = { a: Int }\n";
        Files.writeString(f, messy);

        Main.main(new String[]{"fmt", "-w", f.toString()});

        assertEquals(Formatter.format(messy), Files.readString(f));
    }
}
