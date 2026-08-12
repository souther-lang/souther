package souther.cli;

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
    void encodesAUnionOutputThroughTheUnionItDeclared() throws Exception {
        Path file = write("classify.sou", """
                data Adult = { name: String }
                data Minor = { age: Int }
                behavior classify : (age: Int) -> Adult | Minor constructs Adult, Minor
                let classify (age) = {
                    guard age >= 18 else Minor { age = age }
                    Adult { name = "adult" }
                }
                """);
        assertEquals("{\"name\":\"adult\",\"type\":\"Adult\"}", Runner.run(file, "classify", "20"));
        assertEquals("{\"age\":10,\"type\":\"Minor\"}", Runner.run(file, "classify", "10"));
    }

    @Test
    void encodesANamedSumOutputThroughTheSumItDeclared() throws Exception {
        // The case's own encoder writes no discriminator — only the sum's does, and the sum is what
        // the behavior declared. Taking the encoder off the runtime case would answer a value the
        // same sum's decoder then refuses.
        Path file = write("answer.sou", """
                data Hit = { score: Int }
                data Miss = { reason: String }
                data Answer = Hit | Miss
                behavior ask : (n: Int) -> Answer constructs Hit, Miss
                let ask (n) = if n > 0 then Hit { score = n } else Miss { reason = "no" }
                """);
        assertEquals("{\"score\":5,\"type\":\"Hit\"}", Runner.run(file, "ask", "5"));
    }

    @Test
    void encodesASumInsideACollectionThroughItsElementType() throws Exception {
        Path file = write("many.sou", """
                data Hit = { score: Int }
                data Miss = { reason: String }
                data Answer = Hit | Miss
                behavior many : (n: Int) -> List<Answer> constructs Hit, Miss
                let many (n) = [ Hit { score = n }, Miss { reason = "no" } ]
                """);
        assertEquals("[{\"score\":5,\"type\":\"Hit\"},{\"reason\":\"no\",\"type\":\"Miss\"}]",
                Runner.run(file, "many", "5"));
    }

    @Test
    void encodesAPrimitiveMemberOfAUnionUnderValue() throws Exception {
        Path file = write("len.sou", """
                data NotFound
                behavior lengthOf : (key: String) -> Int | NotFound
                    constructs NotFound
                let lengthOf (key) = {
                    guard String.length(key) > 0 else NotFound
                    String.length(key)
                }
                """);
        assertEquals("{\"type\":\"Int\",\"value\":4}", Runner.run(file, "lengthOf", "\"abcd\""));
        assertEquals("{\"type\":\"NotFound\"}", Runner.run(file, "lengthOf", "\"\""));
    }

    @Test
    void encodesAnOutcomeCarryingNothingAsItsCaseName() throws Exception {
        Path file = write("decide.sou", """
                data Approved
                data Rejected
                behavior decide : (n: Int) -> Approved | Rejected
                    constructs Approved, Rejected
                let decide (n) = if n > 0 then Approved else Rejected
                """);
        assertEquals("\"Approved\"", Runner.run(file, "decide", "1"));
        assertEquals("\"Rejected\"", Runner.run(file, "decide", "0"));
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
    void refusesABehaviorTheModuleDoesNotExpose() throws Exception {
        Path file = write("visible.sou", """
                module visible exposing ( shown )

                behavior shown : (s: String) -> String
                let shown (s) = s

                behavior hidden : (s: String) -> String
                let hidden (s) = s
                """);
        Runner.RunException e = assertThrows(Runner.RunException.class,
                () -> Runner.run(file, "hidden", "\"x\""));
        assertTrue(e.getMessage().contains("not exposed"), e.getMessage());
        assertFalse(e.getMessage().contains("souther.compiler")
                || e.getMessage().contains("souther.cli"), e.getMessage());
    }

    @Test
    void refusesTheSoleRunnableBehaviorWhenTheModuleDoesNotExposeIt() throws Exception {
        Path file = write("visible.sou", """
                module visible exposing ( Note )

                data Note = { body: String }

                behavior hidden : (n: Note) -> Note
                let hidden (n) = n
                """);
        Runner.RunException e = assertThrows(Runner.RunException.class,
                () -> Runner.run(file, null, "{\"body\":\"b\"}"));
        assertTrue(e.getMessage().contains("exposes"), e.getMessage());
        assertFalse(e.getMessage().contains("souther.compiler")
                || e.getMessage().contains("souther.cli"), e.getMessage());
    }

    @Test
    void picksTheExposedBehaviorOverARunnableOneTheModuleKeepsToItself() throws Exception {
        Path file = write("visible.sou", """
                module visible exposing ( shown )

                behavior shown : (s: String) -> String
                let shown (s) = "shown " ++ s

                behavior hidden : (s: String) -> String
                let hidden (s) = "hidden " ++ s
                """);
        assertEquals("\"shown x\"", Runner.run(file, null, "\"x\""));
    }

    @Test
    void offersOnlyExposedBehaviorsToPickAmong() throws Exception {
        Path file = write("visible.sou", """
                module visible exposing ( a, b )

                behavior a : (s: String) -> String
                let a (s) = s

                behavior b : (s: String) -> String
                let b (s) = s

                behavior hidden : (s: String) -> String
                let hidden (s) = s
                """);
        Runner.RunException e = assertThrows(Runner.RunException.class,
                () -> Runner.run(file, null, "\"x\""));
        assertTrue(e.getMessage().contains("a, b"), e.getMessage());
        assertFalse(e.getMessage().contains("hidden"), e.getMessage());
    }

    @Test
    void refusesAPipelineTheModuleDoesNotExpose() throws Exception {
        Path file = write("visible.sou", """
                module visible exposing ( shown )

                data In = { v: Int }
                data Out = { v: Int }

                behavior shown : (s: String) -> String
                let shown (s) = s

                behavior stage : (i: In) -> Out constructs Out
                let stage (i) = Out { v = i.v }

                behavior flow = stage
                """);
        Runner.RunException e = assertThrows(Runner.RunException.class,
                () -> Runner.run(file, "flow", "{\"v\": 1}"));
        assertTrue(e.getMessage().contains("not exposed"), e.getMessage());
    }

    /** The behavior is refused where it is chosen, so its hidden input type is never asked for a
     *  decoder — which would have failed for the same reason and said so as a missing decoder. */
    @Test
    void refusesAHiddenBehaviorBeforeAskingItsInputTypeForADecoder() throws Exception {
        Path file = write("visible.sou", """
                module visible exposing ( other )

                data Note = { body: String }

                behavior hidden : (n: Note) -> Note
                let hidden (n) = n

                behavior other : (s: String) -> String
                let other (s) = s
                """);
        Runner.RunException e = assertThrows(Runner.RunException.class,
                () -> Runner.run(file, "hidden", "{\"body\":\"b\"}"));
        assertTrue(e.getMessage().contains("not exposed"), e.getMessage());
        assertFalse(e.getMessage().contains("decoder"), e.getMessage());
    }

    /** The list every refusal ends with holds what `run` can run, which is narrower than what is
     *  runnable. Calling it the runnable ones would deny that `hidden` — a `let`, nothing injected —
     *  is runnable at all, when what it is not is exposed. */
    @Test
    void doesNotCallTheBehaviorsItOffersTheRunnableOnes() throws Exception {
        Path file = write("visible.sou", """
                module visible exposing ( Note )

                data Note = { body: String }

                behavior hidden : (n: Note) -> Note
                let hidden (n) = n
                """);
        Runner.RunException e = assertThrows(Runner.RunException.class,
                () -> Runner.run(file, "typo", "{\"body\":\"b\"}"));
        assertTrue(e.getMessage().contains("no behavior named `typo`"), e.getMessage());
        assertFalse(e.getMessage().contains("Runnable"), e.getMessage());
    }

    @Test
    void drivesABehaviorTheModuleExposesAlongsideItsType() throws Exception {
        Path file = write("visible.sou", """
                module visible exposing ( shown, Note )

                data Note = { body: String }

                behavior shown : (n: Note) -> Note
                let shown (n) = n
                """);
        assertEquals("{\"body\":\"b\"}", Runner.run(file, "shown", "{\"body\":\"b\"}"));
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

    /**
     * A parameter type reaches {@code run} already judged. What may cross is the checker's question,
     * and every kind it admits is one the runner composes a decoder for, so {@code run.decode
     * .unsupported} has no input left to refuse — each row here is refused before a decoder is asked
     * for at all.
     */
    @Test
    void aParameterTypeTheRunnerCannotDecodeIsRefusedBeforeItIsAsked() throws Exception {
        assertInputRefused("(Int, Int)", "a tuple", "E1311");
        assertInputRefused("Int?", "an optional", "E1402");
        assertInputRefused("A | B", "an anonymous union", "E1312");
        assertInputRefused("Map<Int, Int>", "a map an object cannot be keyed by", "E1314");

        Path file = write("indrives.sou", """
                data UserId = String
                data Out = { n: Int }
                behavior f : (byUser: Map<UserId, Int>) -> Out constructs Out
                let f (byUser) = Out { n = Map.size(byUser) }
                """);
        assertEquals("{\"n\":1}", Runner.run(file, "f", "{\"u1\": 1}"));
    }

    /**
     * The same of an output type, which is a separate claim and asked separately: the encoder is
     * composed from the behavior's return type, and what may be returned is a shorter list than what
     * may be taken — an anonymous union is a parameter the checker refuses and an output it admits.
     */
    @Test
    void anOutputTypeTheRunnerCannotEncodeIsRefusedBeforeItIsAsked() throws Exception {
        assertOutputRefused("(Int, Int)", "(1, 2)", "a tuple", "E1311");
        assertOutputRefused("Int?", "1", "an optional", "E1402");
        assertOutputRefused("Map<Int, Int>", "Map.fromList([ (1, 2) ])",
                "a map an object cannot be keyed by", "E1314");

        Path file = write("outdrives.sou", """
                data UserId = String
                data A = { a: Int }
                data B = { b: Int }
                behavior f : (n: Int) -> Map<UserId, Int> constructs UserId
                let f (n) = Map.fromList([ (UserId("u1"), n) ])
                behavior g : (n: Int) -> A | B constructs A
                let g (n) = A { a = n }
                """);
        assertEquals("{\"u1\":1}", Runner.run(file, "f", "1"));
        // the union's own encoder writes the case, so the answer carries the discriminator
        assertEquals("{\"a\":1,\"type\":\"A\"}", Runner.run(file, "g", "1"));
    }

    /** That a parameter of this type never reaches the runner's decoder: the compile refuses it,
     *  naming the code that owns the rule. */
    private void assertInputRefused(String type, String what, String code) throws Exception {
        Path file = write("inref" + Math.abs(type.hashCode()) + ".sou", """
                data A = { a: Int }
                data B = { b: Int }
                data Out = { n: Int }
                behavior f : (v: %s) -> Out constructs Out
                let f (v) = Out { n = 1 }
                """.formatted(type));
        RuntimeException e = assertThrows(RuntimeException.class,
                () -> Runner.run(file, "f", "1"), what + " is refused before run decodes");
        assertTrue(e.getMessage().contains(code), what + ": " + e.getMessage());
    }

    /** That an output of this type never reaches the runner's encoder. */
    private void assertOutputRefused(String type, String body, String what, String code)
            throws Exception {
        Path file = write("outref" + Math.abs(type.hashCode()) + ".sou", """
                data A = { a: Int }
                data B = { b: Int }
                behavior f : (n: Int) -> %s
                let f (n) = %s
                """.formatted(type, body));
        RuntimeException e = assertThrows(RuntimeException.class,
                () -> Runner.run(file, "f", "1"), what + " is refused before run encodes");
        assertTrue(e.getMessage().contains(code), what + ": " + e.getMessage());
    }

    /** A run failure is read in the language the command line selected, as a compile error is. The
     * exception's own message stays English — that is what a Java caller sees. */
    @Test
    void aRunFailureIsRenderedInTheSelectedLocale() throws Exception {
        Path file = write("injected.sou", """
                data Out = { n: Int }
                behavior f : (n: Int) -> Out constructs Out
                behavior g : (n: Int) -> Out constructs Out
                let g (n) = Out { n = n }
                """);
        Runner.RunException e = assertThrows(Runner.RunException.class,
                () -> Runner.run(file, "f", "1"));

        assertTrue(e.localized(java.util.Locale.JAPANESE).contains("実装がありません"),
                e.localized(java.util.Locale.JAPANESE));
        assertTrue(e.localized(java.util.Locale.JAPANESE).contains("`f`"),
                e.localized(java.util.Locale.JAPANESE));
        assertTrue(e.localized(java.util.Locale.ENGLISH).contains("has no implementation"),
                e.localized(java.util.Locale.ENGLISH));
        assertEquals(e.getMessage(), e.localized(java.util.Locale.ENGLISH));
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

    /** {@code --input} with nothing in it is input of the wrong shape, which is a refusal the reader
     * can act on rather than a null the runner then walks into. */
    @Test
    void anEmptyInputIsReportedRatherThanThrown() throws Exception {
        Path file = write("pair.sou", """
                data Pair = { left: Int, right: Int }
                behavior mkPair : (a: Int, b: Int) -> Pair constructs Pair
                let mkPair (a, b) = Pair { left = a, right = b }
                """);
        Runner.RunException e = assertThrows(Runner.RunException.class,
                () -> Runner.run(file, "mkPair", "   "));
        assertEquals(1, e.exitCode);
        assertTrue(e.getMessage().contains("must be a JSON array"), e.getMessage());
    }

    // --- depth at the boundary ------------------------------------------------------------------

    /** {@code levels} levels of {@code {"n": 1, "kids": [ ... ]}}, the shape self-referential data
     * arrives in. Each level spends two levels of JSON: the object and the list. */
    private static String nestedTree(int levels) {
        return "{\"n\":1,\"kids\":[".repeat(levels) + "]}".repeat(levels);
    }

    /** A JSON array of {@code count} numbers — flat input, whatever the behavior builds from it. */
    private static String counting(int count) {
        StringBuilder json = new StringBuilder("[");
        for (int i = 0; i < count; i++) {
            json.append(i == 0 ? "" : ",").append(i);
        }
        return json.append("]").toString();
    }

    /**
     * Input deeper than the boundary reads is a decode failure like any other: it names the path it
     * gave up at, and counts the nesting in JSON rather than in the parser's words.
     */
    @Test
    void anInputDeeperThanTheBoundaryReadsNamesThePathItGaveUpAt() throws Exception {
        Path file = write("tree.sou", """
                data Node = { n: Int, kids: List<Node> }
                data Out = { n: Int }
                behavior top : (t: Node) -> Out constructs Out
                let top (t) = Out { n = t.n }
                """);
        assertEquals("{\"n\":1}", Runner.run(file, "top", nestedTree(250)));

        Runner.RunException e = assertThrows(Runner.RunException.class,
                () -> Runner.run(file, "top", nestedTree(251)));
        assertEquals(1, e.exitCode);
        assertTrue(e.getMessage().contains("/kids/0/kids"), e.getMessage());
        assertTrue(e.getMessage().contains("past 500 levels"), e.getMessage());
        assertFalse(e.getMessage().contains("StreamReadConstraints"), e.getMessage());
        assertTrue(e.localized(java.util.Locale.JAPANESE).contains("深さ"),
                e.localized(java.util.Locale.JAPANESE));
    }

    /**
     * Depth is one of the limits the reader holds, not the only one: a number too long and a name
     * too long are refused by the same exception type at a depth of nothing. Each keeps the wording
     * it had rather than being told it nests too deeply.
     */
    @Test
    void aLimitOtherThanDepthIsNotReportedAsDepth() throws Exception {
        Path file = write("tree.sou", """
                data Node = { n: Int, kids: List<Node> }
                data Out = { n: Int }
                behavior top : (t: Node) -> Out constructs Out
                let top (t) = Out { n = t.n }
                """);
        // A number longer than StreamReadConstraints.getMaxNumberLength(), written at the 500th
        // level — the deepest a value the reader accepts the nesting of can stand, and one level
        // short of where a refusal for depth stands. Reading the exception's text instead of the
        // context's depth, or reading the depth as `at the limit` rather than `past it`, calls this
        // one too deeply nested.
        String longNumber = "[".repeat(500) + "1".repeat(1001) + "]".repeat(500);
        Runner.RunException tooLongANumber = assertThrows(Runner.RunException.class,
                () -> Runner.run(file, "top", longNumber));
        assertTrue(tooLongANumber.getMessage().contains("is not valid JSON"),
                tooLongANumber.getMessage());
        assertFalse(tooLongANumber.getMessage().contains("nests deeper"),
                tooLongANumber.getMessage());

        // longer than StreamReadConstraints.getMaxNameLength()
        String longName = "{\"" + "n".repeat(50001) + "\":1}";
        Runner.RunException tooLongAName = assertThrows(Runner.RunException.class,
                () -> Runner.run(file, "top", longName));
        assertTrue(tooLongAName.getMessage().contains("is not valid JSON"),
                tooLongAName.getMessage());
        assertFalse(tooLongAName.getMessage().contains("nests deeper"), tooLongAName.getMessage());
    }

    /**
     * Output deeper than the boundary writes is reported the same way. A behavior can build a value
     * deeper than anything it was handed, so this is reachable from input the boundary accepted.
     */
    @Test
    void anOutputDeeperThanTheBoundaryWritesNamesThePathItGaveUpAt() throws Exception {
        Path file = write("nest.sou", """
                data Node = { kids: List<Node> }
                behavior nest : (xs: List<Int>) -> Node constructs Node
                let nest (xs) = List.fold((acc, x) -> Node { kids = [acc] }, Node { kids = [] }, xs)
                """);
        assertEquals("{\"kids\":[{\"kids\":[]}]}", Runner.run(file, "nest", "[1]"));

        Runner.RunException e = assertThrows(Runner.RunException.class,
                () -> Runner.run(file, "nest", counting(600)));
        assertEquals(1, e.exitCode);
        assertTrue(e.getMessage().contains("/kids/0/kids"), e.getMessage());
        assertFalse(e.getMessage().contains("StreamWriteConstraints"), e.getMessage());
        assertFalse(e.getMessage().contains("java.util"), e.getMessage());
        assertTrue(e.localized(java.util.Locale.JAPANESE).contains("深さ"),
                e.localized(java.util.Locale.JAPANESE));
    }

    // --- one input, written bare or wrapped in an array -----------------------------------------

    private static final String ONE_STRING = """
            behavior echo : (name: String) -> String
            let echo (name) = name
            """;

    private static final String ONE_LIST = """
            behavior echo : (xs: List<Int>) -> List<Int>
            let echo (xs) = xs
            """;

    private static final String ONE_NESTED_LIST = """
            behavior echo : (xs: List<List<Int>>) -> List<List<Int>>
            let echo (xs) = xs
            """;

    private static final String ONE_RECORD = """
            data Note = { body: String, tag: String? }
            behavior echo : (n: Note) -> Note
            let echo (n) = n
            """;

    /** The wrapper diagnosis, in both the language a Java caller reads and the one the CLI selects. */
    private void assertNamesTheOuterArray(Runner.RunException e) {
        assertEquals(1, e.exitCode);
        assertTrue(e.getMessage().contains("remove the outer array"), e.getMessage());
        assertFalse(e.getMessage().contains("could not be decoded"), e.getMessage());
        assertTrue(e.localized(java.util.Locale.JAPANESE).contains("外側の配列"),
                e.localized(java.util.Locale.JAPANESE));
    }

    @Test
    void readsASinglePrimitiveInputWrittenBare() throws Exception {
        assertEquals("\"world\"", Runner.run(write("one.sou", ONE_STRING), "echo", "\"world\""));
    }

    @Test
    void namesTheOuterArrayWhenASinglePrimitiveInputIsWrappedInOne() throws Exception {
        Path file = write("one.sou", ONE_STRING);
        assertNamesTheOuterArray(assertThrows(Runner.RunException.class,
                () -> Runner.run(file, "echo", "[\"world\"]")));
    }

    /**
     * A collection input is written as its own array, so an array is not a wrapper by itself. What
     * makes the wrapper case decidable is that the whole input fails to decode and its sole element
     * succeeds — which is why the value is tried as it stands first.
     */
    @Test
    void readsAListInputWrittenAsItsOwnArray() throws Exception {
        assertEquals("[1,2,3]", Runner.run(write("one.sou", ONE_LIST), "echo", "[1,2,3]"));
    }

    @Test
    void namesTheOuterArrayWhenAListInputIsWrappedInOne() throws Exception {
        Path file = write("one.sou", ONE_LIST);
        assertNamesTheOuterArray(assertThrows(Runner.RunException.class,
                () -> Runner.run(file, "echo", "[[1,2,3]]")));
    }

    /** The same text is the input itself when the parameter is a list of lists. */
    @Test
    void readsANestedListInputWrittenAsItself() throws Exception {
        assertEquals("[[1,2,3]]",
                Runner.run(write("one.sou", ONE_NESTED_LIST), "echo", "[[1,2,3]]"));
    }

    @Test
    void readsASingleRecordInputWrittenBare() throws Exception {
        assertEquals("{\"body\":\"b\"}",
                Runner.run(write("one.sou", ONE_RECORD), "echo", "{\"body\":\"b\"}"));
    }

    @Test
    void namesTheOuterArrayWhenASingleRecordInputIsWrappedInOne() throws Exception {
        Path file = write("one.sou", ONE_RECORD);
        assertNamesTheOuterArray(assertThrows(Runner.RunException.class,
                () -> Runner.run(file, "echo", "[{\"body\":\"b\"}]")));
    }

    /**
     * The element has to decode for the wrapper to be the mistake. When it does not, the input is
     * wrong for some other reason and the decoder's own report is what says so.
     */
    @Test
    void keepsTheDecodeFailureWhenTheSoleElementDoesNotDecodeEither() throws Exception {
        Path file = write("one.sou", ONE_RECORD);
        Runner.RunException e = assertThrows(Runner.RunException.class,
                () -> Runner.run(file, "echo", "[{\"unknown\":1}]"));
        assertEquals(1, e.exitCode);
        assertTrue(e.getMessage().contains("could not be decoded"), e.getMessage());
        assertFalse(e.getMessage().contains("remove the outer array"), e.getMessage());
    }

    /** Two inputs still take an array, and the arity failures they get keep saying what they said. */
    @Test
    void keepsTheArityFailuresOfABehaviorThatTakesSeveralInputs() throws Exception {
        Path file = write("pair.sou", """
                data Pair = { left: Int, right: Int }
                behavior mkPair : (a: Int, b: Int) -> Pair constructs Pair
                let mkPair (a, b) = Pair { left = a, right = b }
                """);
        Runner.RunException notArray = assertThrows(Runner.RunException.class,
                () -> Runner.run(file, "mkPair", "3"));
        assertTrue(notArray.getMessage().contains("must be a JSON array"), notArray.getMessage());

        Runner.RunException count = assertThrows(Runner.RunException.class,
                () -> Runner.run(file, "mkPair", "[3]"));
        assertTrue(count.getMessage().contains("but --input has 1"), count.getMessage());
    }

    /**
     * Deeper still, the encoder runs out of stack before the writer ever counts a level. That is not
     * a {@code RuntimeException}, so left alone it reaches the caller as a stack trace.
     */
    @Test
    void anOutputTooDeepToEncodeIsReportedRatherThanThrown() throws Exception {
        Path file = write("nest.sou", """
                data Node = { kids: List<Node> }
                behavior nest : (xs: List<Int>) -> Node constructs Node
                let nest (xs) = List.fold((acc, x) -> Node { kids = [acc] }, Node { kids = [] }, xs)
                """);
        Runner.RunException e = assertThrows(Runner.RunException.class,
                () -> Runner.run(file, "nest", counting(20000)));
        assertEquals(1, e.exitCode);
        assertTrue(e.getMessage().contains("encode"), e.getMessage());
        assertTrue(e.localized(java.util.Locale.JAPANESE).contains("エンコード"),
                e.localized(java.util.Locale.JAPANESE));
    }
}
