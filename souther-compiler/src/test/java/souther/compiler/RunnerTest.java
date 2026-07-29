package souther.compiler;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.nio.file.Files;
import java.nio.file.Path;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@code souther run} drives a compiled behavior end to end: the runner decodes the input through
 * the derived decoders, applies the behavior, and encodes the output back to JSON.
 */
class RunnerTest {

    @TempDir
    Path dir;

    private Path write(String fileName, String source) throws Exception {
        Path file = dir.resolve(fileName);
        Files.writeString(file, source);
        return file;
    }

    @Test
    void drivesAHeaderlessHelloWorldByName() throws Exception {
        Path file = write("hello.sou", """
                behavior greet : (name: String) -> String
                let greet (name) = "Hello, " ++ name
                """);
        assertEquals("\"Hello, world\"", Runner.run(file, "greet", "\"world\""));
    }

    @Test
    void selectsTheSoleRunnableBehaviorWhenNoneNamed() throws Exception {
        Path file = write("hello.sou", """
                behavior greet : (name: String) -> String
                let greet (name) = "Hi, " ++ name
                """);
        assertEquals("\"Hi, Souther\"", Runner.run(file, null, "\"Souther\""));
    }

    @Test
    void decodesSeveralInputsFromAJsonArrayPositionally() throws Exception {
        Path file = write("pair.sou", """
                data A = Int
                data B = Int
                data Pair = {
                    left: Int
                    , right: Int
                }
                behavior mkPair : (a: A, b: B) -> Pair constructs Pair
                let mkPair (a, b) = Pair { left = a.value, right = b.value }
                """);
        assertEquals("{\"left\":3,\"right\":7}", Runner.run(file, "mkPair", "[3, 7]"));
    }

    @Test
    void encodesTheRuntimeCaseOfASumOutput() throws Exception {
        Path file = write("classify.sou", """
                data Adult = { name: String }
                data Minor = { age: Int }
                behavior classify : (age: Int) -> Adult | Minor constructs Adult, Minor
                let classify (age) = {
                    guard age >= 18 else Minor { age = age }
                    Adult { name = "adult" }
                }
                """);
        assertEquals("{\"name\":\"adult\"}", Runner.run(file, "classify", "20"));
        assertEquals("{\"age\":10}", Runner.run(file, "classify", "10"));
    }

    @Test
    void reportsADecodeFailureWithItsPathAndMessage() throws Exception {
        Path file = write("pair.sou", """
                data A = Int
                data B = Int
                data Pair = { left: Int, right: Int }
                behavior mkPair : (a: A, b: B) -> Pair constructs Pair
                let mkPair (a, b) = Pair { left = a.value, right = b.value }
                """);
        Runner.RunException e = assertThrows(Runner.RunException.class,
                () -> Runner.run(file, "mkPair", "[\"x\", 7]"));
        assertEquals(1, e.exitCode);
        assertTrue(e.getMessage().contains("could not be decoded"), e.getMessage());
    }

    @Test
    void refusesAnInjectedBehaviorThatHasNoImplementation() throws Exception {
        Path file = write("clock.sou", """
                behavior now : () -> String
                """);
        Runner.RunException e = assertThrows(Runner.RunException.class,
                () -> Runner.run(file, "now", null));
        assertTrue(e.getMessage().contains("no implementation"), e.getMessage());
    }

    @Test
    void refusesABehaviorThatNeedsInjectedDependencies() throws Exception {
        Path file = write("stamp.sou", """
                data Stamped = { at: String }
                behavior now : () -> String
                behavior stamp : (x: String) -> Stamped
                    depends on now
                    constructs Stamped
                let stamp (x, now) = Stamped { at = now() }
                """);
        Runner.RunException e = assertThrows(Runner.RunException.class,
                () -> Runner.run(file, "stamp", "\"x\""));
        assertTrue(e.getMessage().contains("depends on injected dependencies"), e.getMessage());
    }

    @Test
    void drivesASingleStageInLanguagePipeline() throws Exception {
        Path file = write("flow.sou", """
                data In = { v: Int }
                data Out = { v: Int }
                behavior stage : (i: In) -> Out constructs Out
                let stage (i) = Out { v = i.v }
                behavior flow = stage
                """);
        assertEquals("{\"v\":1}", Runner.run(file, "flow", "{\"v\": 1}"));
    }

    @Test
    void drivesAMultiStageInLanguagePipeline() throws Exception {
        Path file = write("flow.sou", """
                data In = { v: Int }
                data Mid = { v: Int }
                data Out = { v: Int }
                behavior first : (i: In) -> Mid constructs Mid
                let first (i) = Mid { v = i.v }
                behavior second : (m: Mid) -> Out constructs Out
                let second (m) = Out { v = m.v }
                behavior flow = first >-> second
                """);
        assertEquals("{\"v\":42}", Runner.run(file, "flow", "{\"v\": 42}"));
    }

    @Test
    void refusesAPipelineWhoseStageNeedsInjectedDependencies() throws Exception {
        Path file = write("flow.sou", """
                data In = { v: Int }
                data Out = { at: String }
                behavior now : () -> String
                behavior stamp : (i: In) -> Out
                    depends on now
                    constructs Out
                let stamp (i, now) = Out { at = now() }
                behavior flow = stamp
                """);
        Runner.RunException e = assertThrows(Runner.RunException.class,
                () -> Runner.run(file, "flow", "{\"v\": 1}"));
        assertTrue(e.getMessage().contains("depends on injected dependencies"), e.getMessage());
        assertTrue(e.getMessage().contains("stamp"), e.getMessage());
    }

    @Test
    void refusesToPickAmongSeveralRunnableBehaviors() throws Exception {
        Path file = write("two.sou", """
                behavior a : (s: String) -> String
                let a (s) = s
                behavior b : (s: String) -> String
                let b (s) = s
                """);
        Runner.RunException e = assertThrows(Runner.RunException.class,
                () -> Runner.run(file, null, "\"x\""));
        assertEquals(2, e.exitCode);
        assertTrue(e.getMessage().contains("--behavior"), e.getMessage());
    }

    @Test
    void decodesAListOfDataAsAnInput() throws Exception {
        Path file = write("tally.sou", """
                data Item = { name: String, price: Int }
                data Out = { n: Int }
                behavior tally : (items: List<Item>) -> Out constructs Out
                let tally (items) = Out { n = List.fold((a, x) -> a + x.price, 0, items) }
                """);
        assertEquals("{\"n\":350}",
                Runner.run(file, "tally", "[{\"name\":\"a\",\"price\":100},{\"name\":\"b\",\"price\":250}]"));
    }

    @Test
    void decodesACollectionAmongSeveralInputs() throws Exception {
        Path file = write("total.sou", """
                data Out = { n: Int }
                behavior total : (prices: List<Int>, extra: Int) -> Out constructs Out
                let total (prices, extra) = Out { n = List.fold((a, x) -> a + x, extra, prices) }
                """);
        assertEquals("{\"n\":16}", Runner.run(file, "total", "[[1, 2, 3], 10]"));
    }

    @Test
    void decodesASetAndAMapAsInputs() throws Exception {
        Path file = write("counts.sou", """
                data Out = { n: Int }
                behavior counts : (tags: Set<String>, prices: Map<String, Int>) -> Out constructs Out
                let counts (tags, prices) = Out { n = Set.size(tags) + Map.size(prices) }
                """);
        assertEquals("{\"n\":5}",
                Runner.run(file, "counts", "[[\"a\", \"b\", \"a\"], {\"x\": 1, \"y\": 2, \"z\": 3}]"));
    }

    @Test
    void encodesACollectionOutput() throws Exception {
        Path file = write("names.sou", """
                data Item = { name: String, price: Int }
                data Cart = { items: List<Item> }
                behavior names : (c: Cart) -> List<String>
                let names (c) = List.map(.name, c.items)
                """);
        assertEquals("[\"a\",\"b\"]",
                Runner.run(file, "names",
                        "{\"items\":[{\"name\":\"a\",\"price\":1},{\"name\":\"b\",\"price\":2}]}"));
    }

    /** A type `run` still cannot drive is named the way the source writes it, not in the checker's
     * own spelling, and in the reader's language — the runner is as much a user surface as the
     * compiler's diagnostics. */
    @Test
    void namesAnUndecodableInputTypeInSurfaceSyntax() throws Exception {
        Path file = write("keyed.sou", """
                data UserId = String
                data Out = { n: Int }
                behavior f : (byUser: Map<UserId, Int>) -> Out constructs Out
                let f (byUser) = Out { n = Map.size(byUser) }
                """);
        Runner.RunException e = assertThrows(Runner.RunException.class,
                () -> Runner.run(file, "f", "{\"u1\": 1}"));
        assertTrue(e.getMessage().contains("Map<UserId, Int>"), e.getMessage());
        assertFalse(e.getMessage().contains("MapOf"), e.getMessage());
    }

    /** A run failure is read in the language the command line selected, as a compile error is. The
     * exception's own message stays English — that is what a Java caller sees. */
    @Test
    void aRunFailureIsRenderedInTheSelectedLocale() throws Exception {
        Path file = write("keyed.sou", """
                data UserId = String
                data Out = { n: Int }
                behavior f : (byUser: Map<UserId, Int>) -> Out constructs Out
                let f (byUser) = Out { n = Map.size(byUser) }
                """);
        Runner.RunException e = assertThrows(Runner.RunException.class,
                () -> Runner.run(file, "f", "{\"u1\": 1}"));

        assertTrue(e.localized(java.util.Locale.JAPANESE).contains("デコードできません"),
                e.localized(java.util.Locale.JAPANESE));
        assertTrue(e.localized(java.util.Locale.JAPANESE).contains("Map<UserId, Int>"),
                e.localized(java.util.Locale.JAPANESE));
        assertTrue(e.localized(java.util.Locale.ENGLISH).contains("cannot decode yet"),
                e.localized(java.util.Locale.ENGLISH));
    }

    /** The decoder's own issue text is part of the message the reader sees, so it is resolved in the
     * same language rather than left in the decoder's default English. */
    @Test
    void aDecodeFailureResolvesItsIssueTextInTheSelectedLocale() throws Exception {
        Path file = write("tally.sou", """
                data Item = { name: String, price: Int }
                data Out = { n: Int }
                behavior tally : (items: List<Item>) -> Out constructs Out
                let tally (items) = Out { n = List.fold((a, x) -> a + x.price, 0, items) }
                """);
        Runner.RunException e = assertThrows(Runner.RunException.class,
                () -> Runner.run(file, "tally", "[{\"name\":\"a\"}]"));

        assertTrue(e.localized(java.util.Locale.JAPANESE).contains("必須です"),
                e.localized(java.util.Locale.JAPANESE));
        assertTrue(e.localized(java.util.Locale.JAPANESE).contains("/0/price"),
                e.localized(java.util.Locale.JAPANESE));
        assertTrue(e.getMessage().contains("is required"), e.getMessage());
    }

    /** Input of the wrong shape is a user error, not a crash: the decoder throws where it cannot even
     * read the value, and `run` reports that as the decode failure it is. */
    @Test
    void inputOfTheWrongShapeIsReportedRatherThanThrown() throws Exception {
        Path file = write("cart.sou", """
                data Item = { name: String, price: Int }
                data Cart = { items: List<Item> }
                data Out = { n: Int }
                behavior tally : (c: Cart) -> Out constructs Out
                let tally (c) = Out { n = List.length(c.items) }
                """);
        Runner.RunException e = assertThrows(Runner.RunException.class,
                () -> Runner.run(file, "tally", "[1, 2]"));
        assertEquals(1, e.exitCode);
        assertTrue(e.getMessage().contains("input #1"), e.getMessage());
    }

    /** A usage error ends with the usage line, in the same language. */
    @Test
    void aUsageFailureCarriesTheUsageLineInTheSelectedLocale() throws Exception {
        Path file = write("two.sou", """
                behavior a : (s: String) -> String
                let a (s) = s
                behavior b : (s: String) -> String
                let b (s) = s
                """);
        Runner.RunException e = assertThrows(Runner.RunException.class,
                () -> Runner.run(file, null, "\"x\""));
        assertEquals(2, e.exitCode);
        assertTrue(e.localized(java.util.Locale.JAPANESE).contains("使い方: souther run"),
                e.localized(java.util.Locale.JAPANESE));
        assertTrue(e.localized(java.util.Locale.ENGLISH).contains("usage: souther run"),
                e.localized(java.util.Locale.ENGLISH));
    }

    @Test
    void namesAHeaderlessModuleAfterTheFile() throws Exception {
        Path file = write("greeter.sou", """
                behavior id : (s: String) -> String
                let id (s) = s
                """);
        // The generated class lands in the file-stem package; driving it confirms the name resolves.
        assertEquals("\"ok\"", Runner.run(file, "id", "\"ok\""));
    }
}
