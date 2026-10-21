package souther.cli;

import souther.cli.CliProcess.Ran;
import souther.compiler.fmt.Formatter;
import org.junit.jupiter.api.Test;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;

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

        assertEquals(Formatter.format(messy), CliInProcess.printed("fmt", f.toString()));
    }

    @Test
    void docPrintsASpecificationSectionByItsAnchor() throws Exception {
        String printed = CliInProcess.printed("doc", "purpose");
        assertTrue(printed.contains("JVM-targeted language"), "the purpose section is printed");
    }

    @Test
    void apiListsTheStdlibSurface() throws Exception {
        String printed = CliInProcess.printed("api", "Option");
        assertTrue(printed.lines().anyMatch(l -> l.startsWith("Option.map(")),
                "the Option module's surface is printed");
    }

    @Test
    void japiPrintsAJarsPublicApi() throws Exception {
        Path scratch = Files.createTempDirectory("souther-japi");
        Ran ran = CliInProcess.run(scratch, scratch, Map.of(),
                Map.of("java.class.path", System.getProperty("java.class.path")), "",
                "japi", "net.unit8.raoh.Issues");
        assertEquals(0, ran.code(), ran.err());
        assertTrue(ran.out().contains("record net.unit8.raoh.Issues"),
                "raoh's Issues is answered from the test classpath");
    }

    @Test
    void mcpServesTheProtocolOnStdinAndLeavesAtItsEnd() throws Exception {
        Path scratch = Files.createTempDirectory("souther-mcp");
        Ran ran = CliInProcess.run(scratch, scratch, Map.of(), Map.of(),
                "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"tools/list\"}\n", "mcp");
        assertEquals(0, ran.code(), ran.err());
        assertTrue(ran.out().contains("\"doc_search\""),
                "the server answered on stdout and returned at end of input");
    }

    @Test
    void fmtWriteRewritesTheFileInPlace() throws Exception {
        Path f = Files.createTempDirectory("souther-fmt").resolve("m.sou");
        String messy = "module m\ndata X = { a: Int }\n";
        Files.writeString(f, messy);

        assertEquals(0, CliInProcess.run("fmt", "-w", f.toString()).code());

        assertEquals(Formatter.format(messy), Files.readString(f));
    }
}
