package souther.compiler.doc;

import org.junit.jupiter.api.Test;
import souther.compiler.Prelude;
import souther.compiler.types.Type;

import java.io.IOException;
import java.io.InputStream;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.NavigableMap;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A call the specification writes in its prose or in an example is what a reader copies. The
 * checker resolves that call against a signature the standard library declares, so a call the
 * document writes one way and the library declares another is the document teaching code that does
 * not compile.
 *
 * <p>The calls are read out of the specification's own text and the signatures come from the
 * resolver {@code souther api} prints. Neither side is written for the other: what is checked is
 * that the side a reader reads and the side the compiler enforces do not say different things.
 *
 * <p>It refutes rather than verifies, and the name says so. Deciding that a call is right needs the
 * types of every argument, which is the checker's job over a program and not this scan's over a
 * document. What it decides is the argument count, whether the name is published, and — for an
 * argument whose being a function or not is settled by how it is written — whether it stands at a
 * parameter declared to take one. An argument neither settles is left alone, so
 * {@code List.map(xs, ys)} passes here and is caught only by the compiler (E1804).
 */
class NoStandardLibraryCallTheSpecificationWritesContradictsItsSignatureTest {

    /** A qualified standard-library call, wherever the specification writes one. */
    private static final Pattern CALL =
            Pattern.compile("(?<![\\w.])([A-Z][A-Za-z0-9]*)\\.([a-z][A-Za-z0-9]*)\\(");

    /**
     * A function declared beside the call, so a bare name written as an argument is known to be one.
     * A behavior counts: its name handed over is the behavior, and passing one to {@code List.map}
     * and calling it by name reach the same place (<<blocks>>, specification.adoc:1818).
     */
    private static final Pattern DECLARED_FUNCTION = Pattern.compile(
            "(?m)^\\s*(?:partial\\s+)?let\\s+([a-z][A-Za-z0-9]*)\\s*\\("
                    + "|^\\s*behavior\\s+([a-z][A-Za-z0-9]*)\\s*:");

    /** The delimiter of a block AsciiDoc takes as it stands. A listing is one region a name is
     *  declared over; outside one, a paragraph is. */
    private static final Pattern BLOCK_DELIMITER = Pattern.compile("^([-.+/])\\1{3,}$");

    /** An argument written as an ellipsis rather than as a value — the call is quoted, not made. */
    private static final Pattern ELIDED = Pattern.compile("\\.\\.\\.|…");

    /** A bare name, qualified or not, with nothing applied to it. */
    private static final Pattern NAME = Pattern.compile("[A-Za-z][A-Za-z0-9]*(\\.[A-Za-z][A-Za-z0-9]*)?");

    /** A getter block: {@code .field} desugars to {@code (x) -> x.field}. */
    private static final Pattern GETTER = Pattern.compile("\\.[a-z][A-Za-z0-9]*");

    /** What is not a function whatever it holds: a literal, a list literal, or a construction. */
    private static final Pattern NOT_A_FUNCTION = Pattern.compile(
            "-?\\d[\\d_]*(\\.\\d+)?m?|\"[^\"]*\"|true|false|\\[.*]|[A-Z][A-Za-z0-9]*\\s*\\{.*}");

    /**
     * A call the specification writes in order to say that it is refused. The document is right
     * about each of these and the checker is right to resolve them otherwise; what is checked here
     * is the calls a reader is meant to copy.
     */
    private static final Set<String> WRITTEN_TO_BE_REFUSED = Set.of(
            // "`Decimal.divide(dividend, divisor)` without scale and mode cannot be written"
            "Decimal.divide(dividend, divisor)",
            // "a *value* and not a function — written `Map.empty`, never `Map.empty()`"
            "Map.empty()",
            "Set.empty()");

    @Test
    void theSpecificationCallsTheStandardLibraryTheWayTheLibraryDeclaresItself() {
        assertEquals(Set.of(), disagreements(text()),
                "the specification writes these calls, and the checker resolves them otherwise");
    }

    @Test
    void aCallIsFoundAtAllSoTheScanIsNotLookingAtAnEmptyDocument() {
        assertFalse(callsIn(text()).isEmpty(),
                "found no standard-library call at all — the scan missed the document");
    }

    /**
     * The two lines this check was written for. Both pass a function where {@code List.all} declares
     * the list: the first writes it as a block, the second by the name the same listing declares it
     * under.
     */
    @Test
    void aFunctionPassedWhereTheSignatureDeclaresTheCollectionIsCaught() {
        Set<String> found = disagreements("""
                [,text]
                ----
                let isValid (r: PreApprovalReason) = ...

                List.all(reasons, r -> isValid(r))
                List.all(reasons, isValid)
                ----
                """);

        assertEquals(2, found.size(), found.toString());
        assertTrue(found.stream().allMatch(f -> f.contains("List.all") && f.contains("argument 2")),
                found.toString());
        assertEquals(Set.of(), disagreements("""
                [,text]
                ----
                let isValid (r: PreApprovalReason) = ...

                List.all(r -> isValid(r), reasons)
                List.all(isValid, reasons)
                ----
                """), "and the same two lines written the other way round are what the signature declares");
    }

    /**
     * The other half of the same disagreement. An argument order is wrong in both directions at
     * once, and the collection is the half a reader is likelier to write as something that could
     * not be a function whatever it holds.
     */
    @Test
    void somethingThatIsNotAFunctionPassedWhereTheSignatureDeclaresOneIsCaught() {
        assertEquals(1, disagreements("`+List.map([1, 2], xs)+`").size());
        assertEquals(1, disagreements("`+List.fold(0, step, xs)+`").size());
        assertEquals(1, disagreements("`+List.filter(\"a\", xs)+`").size());
    }

    /**
     * A behavior's name is a function value: the specification says so at {@code <<blocks>>} and the
     * compiler accepts it, so the scan must not read one as a disagreement.
     */
    @Test
    void aBehaviorNameStandsWhereTheSignatureDeclaresAFunction() {
        assertEquals(Set.of(), disagreements("""
                [,text]
                ----
                behavior norm : (s: String) -> String

                List.map(norm, xs)
                ----
                """));
        assertEquals(1, disagreements("""
                [,text]
                ----
                behavior norm : (s: String) -> String

                List.map(xs, norm)
                ----
                """).size());
    }

    /**
     * A name is a function over the listing that declares it and nowhere else. Reading declarations
     * from the whole document would have one listing's {@code let n (x)} make another listing's
     * {@code n} a function, which is a coarser scope than the language's own.
     */
    @Test
    void aFunctionDeclaredInOneListingDoesNotNameAnotherListingsValue() {
        assertEquals(Set.of(), disagreements("""
                [,text]
                ----
                let n (x: Int) = x + 1
                ----

                [,text]
                ----
                let n = 3

                List.get(n, xs)
                ----
                """));
    }

    @Test
    void aCallPassingTooFewOrTooManyArgumentsIsCaught() {
        assertEquals(1, disagreements("`+List.map(xs)+`").size());
        assertEquals(1, disagreements("`+List.map(f, xs, more)+`").size());
        assertEquals(Set.of(), disagreements("`+List.map(f, xs)+`"));
    }

    /** A pipe supplies the last argument, so the call is written with one fewer. */
    @Test
    void aPipedCallIsReadWithTheArgumentThePipeSupplies() {
        assertEquals(Set.of(), disagreements("`+xs |> List.map(.value)+`"));
        assertEquals(1, disagreements("`+xs |> List.map(f, xs)+`").size());
    }

    @Test
    void aNameTheLibraryDoesNotPublishIsCaught() {
        assertEquals(1, disagreements("`+List.mapish(f, xs)+`").size());
    }

    /** {@code Map.empty} declares no parameter list, so applying it is refused (E1803). */
    @Test
    void aLibraryValueWrittenWithAnArgumentListIsCaught() {
        assertEquals(1, disagreements("`+Map.empty(k)+`").size());
    }

    /** An ellipsis stands for arguments rather than being one, so the count says nothing. */
    @Test
    void aCallQuotedWithAnEllipsisIsNotCountedAgainstItsArity() {
        assertEquals(Set.of(), disagreements("`+String.length(...)+`"));
    }

    /** Every way the specification contradicts a resolved signature, one line each. */
    private static Set<String> disagreements(String adoc) {
        NavigableMap<Integer, Set<String>> declared = declarationsByRegion(adoc);
        Map<String, ApiCommand.Signature> surface = ApiCommand.surface();
        Set<String> found = new TreeSet<>();
        for (Call call : callsIn(adoc)) {
            if (WRITTEN_TO_BE_REFUSED.contains(call.written())) {
                continue;
            }
            ApiCommand.Signature signature = surface.get(call.name());
            if (signature == null) {
                found.add(call.where() + call.name() + " names nothing the standard library publishes");
                continue;
            }
            if (Prelude.isEmptyCollectionValue(call.name())) {
                found.add(call.where() + call.name() + " is a value and takes no argument list");
                continue;
            }
            int declares = signature.paramNames().size();
            int written = call.args().size() + (call.piped() ? 1 : 0);
            if (written != declares && call.args().stream().noneMatch(a -> ELIDED.matcher(a).find())) {
                found.add(call.where() + call.name() + " is written with " + written
                        + " argument(s) and declares " + declares);
            }
            Set<String> here = declared.floorEntry(call.at()).getValue();
            for (int i = 0; i < call.args().size() && i < declares; i++) {
                boolean takesAFunction = signature.paramTypes().get(i) instanceof Type.FnOf;
                String at = " as argument " + (i + 1) + ", where it declares "
                        + signature.paramNames().get(i) + ": " + Type.show(signature.paramTypes().get(i));
                switch (kindOf(call.args().get(i), here, surface)) {
                    case FUNCTION -> {
                        if (!takesAFunction) {
                            found.add(call.where() + call.name() + " is passed a function" + at);
                        }
                    }
                    case NOT_A_FUNCTION -> {
                        if (takesAFunction) {
                            found.add(call.where() + call.name()
                                    + " is passed something that is not a function" + at);
                        }
                    }
                    case UNDECIDED -> { }
                }
            }
        }
        return found;
    }

    /** What an argument is, where how it is written settles it. */
    private enum Kind { FUNCTION, NOT_A_FUNCTION, UNDECIDED }

    /**
     * An anonymous block, a getter block and a name declared as a function are functions; a literal,
     * a list literal, a construction and a library name declaring no parameter list are not. A name
     * nothing here declares settles nothing either way.
     */
    private static Kind kindOf(String argument, Set<String> declaredHere,
                               Map<String, ApiCommand.Signature> surface) {
        String written = argument.strip();
        if (arrowAt(written) >= 0 || GETTER.matcher(written).matches()) {
            return Kind.FUNCTION;
        }
        if (NOT_A_FUNCTION.matcher(written).matches()) {
            return Kind.NOT_A_FUNCTION;
        }
        if (NAME.matcher(written).matches()) {
            if (declaredHere.contains(written)) {
                return Kind.FUNCTION;
            }
            ApiCommand.Signature published = surface.get(written);
            if (published != null) {
                return published.paramNames().isEmpty() ? Kind.NOT_A_FUNCTION : Kind.FUNCTION;
            }
        }
        return Kind.UNDECIDED;
    }

    /** One call as the document writes it, with the arguments split as the parser would. */
    private record Call(String name, List<String> args, boolean piped, int at, int line) {
        String where() {
            return "specification.adoc:" + line + ": ";
        }

        String written() {
            return name + "(" + String.join(", ", args) + ")";
        }
    }

    private static List<Call> callsIn(String adoc) {
        List<Call> calls = new ArrayList<>();
        Matcher m = CALL.matcher(adoc);
        while (m.find()) {
            if (!Prelude.isQualifier(m.group(1))) {
                continue;
            }
            int open = m.end() - 1;
            int close = closing(adoc, open);
            if (close < 0) {
                continue;
            }
            calls.add(new Call(m.group(1) + "." + m.group(2),
                    argumentsOf(adoc.substring(open + 1, close)),
                    piped(adoc, m.start()),
                    m.start(),
                    lineOf(adoc, m.start())));
        }
        return calls;
    }

    /**
     * The {@code )} that closes the argument list, or -1 where the paragraph ends first — an
     * unbalanced {@code (} is prose about a call rather than a call, and reading on would take a
     * {@code )} from somewhere else in the document.
     */
    private static int closing(String text, int open) {
        int depth = 0;
        for (int i = open; i < text.length(); i++) {
            char c = text.charAt(i);
            if (c == '"') {
                i = endOfString(text, i);
            } else if (c == '(') {
                depth++;
            } else if (c == ')' && --depth == 0) {
                return i;
            } else if (c == '\n' && i + 1 < text.length() && text.charAt(i + 1) == '\n') {
                return -1;
            }
        }
        return -1;
    }

    private static List<String> argumentsOf(String inside) {
        if (inside.isBlank()) {
            return List.of();
        }
        List<String> args = new ArrayList<>();
        int depth = 0;
        int start = 0;
        for (int i = 0; i < inside.length(); i++) {
            char c = inside.charAt(i);
            if (c == '"') {
                i = endOfString(inside, i);
            } else if (c == '(' || c == '[' || c == '{') {
                depth++;
            } else if (c == ')' || c == ']' || c == '}') {
                depth--;
            } else if (c == ',' && depth == 0) {
                args.add(inside.substring(start, i).strip());
                start = i + 1;
            }
        }
        args.add(inside.substring(start).strip());
        return args;
    }

    /** The index of a top-level {@code ->}, which makes what is written an anonymous block. */
    private static int arrowAt(String written) {
        int depth = 0;
        for (int i = 0; i < written.length() - 1; i++) {
            char c = written.charAt(i);
            if (c == '"') {
                i = endOfString(written, i);
            } else if (c == '(' || c == '[' || c == '{') {
                depth++;
            } else if (c == ')' || c == ']' || c == '}') {
                depth--;
            } else if (c == '-' && written.charAt(i + 1) == '>' && depth == 0) {
                return i;
            }
        }
        return -1;
    }

    private static int endOfString(String text, int quote) {
        for (int i = quote + 1; i < text.length(); i++) {
            if (text.charAt(i) == '\\') {
                i++;
            } else if (text.charAt(i) == '"') {
                return i;
            }
        }
        return text.length();
    }

    /** Whether the call stands on the right of a {@code |>}, which supplies its last argument. */
    private static boolean piped(String text, int callStart) {
        int i = callStart - 1;
        while (i >= 0 && (text.charAt(i) == ' ' || text.charAt(i) == '\t' || text.charAt(i) == '\n')) {
            i--;
        }
        return i >= 1 && text.charAt(i) == '>' && text.charAt(i - 1) == '|';
    }

    /**
     * The functions declared in each region of the document, keyed by where the region starts. A
     * listing block is one region and a paragraph outside one is another, so a name is a function
     * where it was declared rather than everywhere the document goes on to write it.
     */
    private static NavigableMap<Integer, Set<String>> declarationsByRegion(String adoc) {
        NavigableMap<Integer, Set<String>> byStart = new TreeMap<>();
        boolean listing = false;
        int start = 0;
        int at = 0;
        for (String line : adoc.split("\n", -1)) {
            String delimiter = line.strip();
            boolean boundary = BLOCK_DELIMITER.matcher(delimiter).matches();
            if (boundary) {
                listing = !listing;
            }
            if (boundary || (!listing && delimiter.isEmpty())) {
                byStart.put(start, declaredFunctionsIn(adoc.substring(start, at)));
                start = at;
            }
            at += line.length() + 1;
        }
        byStart.put(start, declaredFunctionsIn(adoc.substring(Math.min(start, adoc.length()))));
        return byStart;
    }

    private static Set<String> declaredFunctionsIn(String region) {
        Set<String> declared = new TreeSet<>();
        Matcher m = DECLARED_FUNCTION.matcher(region);
        while (m.find()) {
            declared.add(m.group(1) != null ? m.group(1) : m.group(2));
        }
        return declared;
    }

    private static int lineOf(String text, int at) {
        int line = 1;
        for (int i = 0; i < at; i++) {
            if (text.charAt(i) == '\n') {
                line++;
            }
        }
        return line;
    }

    private static String text() {
        try (InputStream in = SpecDocument.class.getResourceAsStream("/META-INF/souther/specification.adoc")) {
            assertNotNull(in, "the specification travels in the jar");
            return new String(in.readAllBytes(), StandardCharsets.UTF_8);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }
}
