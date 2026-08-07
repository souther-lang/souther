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
import java.util.Set;
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
 * resolver `souther api` prints. Neither side is written for the other: what is checked is that the
 * side a reader reads and the side the compiler enforces say the same thing.
 */
class EveryStandardLibraryCallTheSpecificationWritesAgreesWithItsSignatureTest {

    /** A qualified standard-library call, wherever the specification writes one. */
    private static final Pattern CALL =
            Pattern.compile("(?<![\\w.])([A-Z][A-Za-z0-9]*)\\.([a-z][A-Za-z0-9]*)\\(");

    /** A function the specification declares, so a bare name it writes elsewhere is known to be one. */
    private static final Pattern DECLARED_FUNCTION = Pattern.compile(
            "(?m)^\\s*(?:partial\\s+)?let\\s+([a-z][A-Za-z0-9]*)\\s*\\("
                    + "|^\\s*behavior\\s+([a-z][A-Za-z0-9]*)\\s*:");

    /** An argument written as an ellipsis rather than as a value — the call is quoted, not made. */
    private static final Pattern ELIDED = Pattern.compile("\\.\\.\\.|…");

    /** A bare name, qualified or not, with nothing applied to it. */
    private static final Pattern NAME = Pattern.compile("[A-Za-z][A-Za-z0-9]*(\\.[A-Za-z][A-Za-z0-9]*)?");

    /** A getter block: {@code .field} desugars to {@code (x) -> x.field}. */
    private static final Pattern GETTER = Pattern.compile("\\.[a-z][A-Za-z0-9]*");

    /**
     * A call the specification writes in order to say that it is refused. The document is right
     * about each of these and the checker is right to resolve them otherwise; what is checked here
     * is the calls a reader is meant to copy.
     */
    private static final Set<String> WRITTEN_TO_BE_REFUSED = Set.of(
            "Decimal.divide(dividend, divisor)");

    @Test
    void theSpecificationCallsTheStandardLibraryTheWayTheLibraryDeclaresItself() {
        assertEquals(Set.of(), disagreements(text()),
                "the specification writes these calls, and the checker resolves them otherwise");
    }

    @Test
    void aCallIsFoundAtAllSoTheScanIsNotLookingAtAnEmptyDocument() {
        assertFalse(callsIn(text()).isEmpty(), "found no standard-library call at all — the scan missed the document");
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
        assertTrue(found.stream().allMatch(f -> f.contains("List.all") && f.contains("argument 2")), found.toString());
        assertEquals(Set.of(), disagreements("""
                [,text]
                ----
                let isValid (r: PreApprovalReason) = ...

                List.all(r -> isValid(r), reasons)
                List.all(isValid, reasons)
                ----
                """), "and the same two lines written the other way round are what the signature declares");
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

    /** An ellipsis stands for arguments rather than being one, so the count says nothing. */
    @Test
    void aCallQuotedWithAnEllipsisIsNotCountedAgainstItsArity() {
        assertEquals(Set.of(), disagreements("`+String.length(...)+`"));
    }

    /** Every way the specification disagrees with a resolved signature, one line each. */
    private static Set<String> disagreements(String adoc) {
        Set<String> declaredHere = declaredFunctionsIn(adoc);
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
            int declared = signature.paramNames().size();
            int written = call.args().size() + (call.piped() ? 1 : 0);
            if (written != declared && call.args().stream().noneMatch(a -> ELIDED.matcher(a).find())) {
                found.add(call.where() + call.name() + " is written with " + written
                        + " argument(s) and declares " + declared);
            }
            for (int i = 0; i < call.args().size() && i < declared; i++) {
                if (isFunction(call.args().get(i), declaredHere, surface)
                        && !(signature.paramTypes().get(i) instanceof Type.FnOf)) {
                    found.add(call.where() + call.name() + " is passed a function as argument " + (i + 1)
                            + ", where it declares " + signature.paramNames().get(i) + ": "
                            + Type.show(signature.paramTypes().get(i)));
                }
            }
        }
        return found;
    }

    /**
     * Whether the argument is a function on its face: an anonymous block, a getter block, or a name
     * declared as a function — by the standard library, or by the document that writes the call.
     * A name nothing here declares says nothing either way, so it is left alone. A library name
     * declaring no parameter is a value rather than a function — {@code Map.empty}, which is written
     * without an argument list for that reason.
     */
    private static boolean isFunction(String argument, Set<String> declaredHere,
                                      Map<String, ApiCommand.Signature> surface) {
        String written = argument.strip();
        if (arrowAt(written) >= 0 || GETTER.matcher(written).matches()) {
            return true;
        }
        if (!NAME.matcher(written).matches()) {
            return false;
        }
        ApiCommand.Signature published = surface.get(written);
        return declaredHere.contains(written) || (published != null && !published.paramNames().isEmpty());
    }

    /** One call as the document writes it, with the arguments split as the parser would. */
    private record Call(String name, List<String> args, boolean piped, int line) {
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

    private static Set<String> declaredFunctionsIn(String adoc) {
        Set<String> declared = new TreeSet<>();
        Matcher m = DECLARED_FUNCTION.matcher(adoc);
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
