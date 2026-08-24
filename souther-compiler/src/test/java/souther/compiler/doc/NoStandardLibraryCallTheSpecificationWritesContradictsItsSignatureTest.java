package souther.compiler.doc;

import org.junit.jupiter.api.Test;
import souther.compiler.Reserved;
import souther.compiler.check.Prelude;
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
 * argument whose being a function or not is settled by how it is written, at a call site where no
 * other binding of that name is in the way — whether it stands at a parameter declared to take one.
 * Anything else is left alone, so {@code List.map(xs, ys)} passes here and is caught only by the
 * compiler (E1804).
 */
class NoStandardLibraryCallTheSpecificationWritesContradictsItsSignatureTest {

    /** A qualified standard-library call, wherever the specification writes one. */
    private static final Pattern CALL =
            Pattern.compile("(?<![\\w.])([A-Z][A-Za-z0-9]*)\\.([a-z][A-Za-z0-9]*)\\(");

    /**
     * A function declared beside the call, so a bare name written as an argument is known to be one.
     * A behavior counts: its name handed over is the behavior, and passing one to {@code List.map}
     * and calling it by name reach the same place (specification.adoc:1818).
     */
    private static final Pattern DECLARED_FUNCTION = Pattern.compile(
            "(?m)^\\s*(?:partial\\s+)?let\\s+([a-z][A-Za-z0-9]*)\\s*\\("
                    + "|^\\s*behavior\\s+([a-z][A-Za-z0-9]*)\\s*:");

    /** A parameter list — a helper's, or an anonymous block's. Its binders stand for values. */
    private static final Pattern PARAMETERS = Pattern.compile(
            "(?:let\\s+[a-z][A-Za-z0-9]*\\s*)?\\(([^()]*)\\)\\s*(?:->|=|:)");

    /** A block taking one parameter without parentheses: {@code r -> …}. */
    private static final Pattern BARE_PARAMETER = Pattern.compile("(?<![\\w.])([a-z][A-Za-z0-9]*)\\s*->");

    /** A {@code let} binding a value rather than declaring a function. */
    private static final Pattern VALUE_BINDING =
            Pattern.compile("(?m)^\\s*let\\s+([a-z][A-Za-z0-9]*)\\s*(?::[^=(]*)?=");

    /** The delimiter of a block AsciiDoc takes as it stands. A listing is one region a name is
     *  declared over; outside one, a paragraph is. */
    private static final Pattern BLOCK_DELIMITER = Pattern.compile("^([-.+/])\\1{3,}$");

    /** The anchor attribute a section carries, which is how a finding says where it is without
     *  naming a line number every edit above it would move. */
    private static final Pattern ANCHOR = Pattern.compile("^\\[#([A-Za-z0-9_-]+)]$");

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
     * The calls the specification writes in order to say that they are refused, each with the
     * contradiction it is written to carry. Expected rather than skipped: a negative example that
     * stops contradicting the library — because the library came to accept it — is as much a
     * document out of step as a positive one that starts. A second occurrence of the same spelling
     * under another anchor is an extra entry and fails too.
     */
    private static final List<String> WRITTEN_TO_BE_REFUSED = List.of(
            // "`Decimal.divide(dividend, divisor)` without scale and mode cannot be written"
            "stdlib-decimal: Decimal.divide(dividend, divisor) is written with 2 argument(s) and declares 4",
            // "a *value* and not a function — written `Map.empty`, never `Map.empty()`"
            "stdlib-map: Map.empty() is a value and takes no argument list",
            // "so it is a *value* and not a function — written `Set.empty`, never `Set.empty()`"
            "stdlib-set: Set.empty() is a value and takes no argument list");

    @Test
    void theOnlyCallsContradictingTheLibraryAreTheOnesWrittenToBeRefused() {
        List<Finding> found = findings(text());

        assertEquals(WRITTEN_TO_BE_REFUSED, keysOf(found), "the specification writes these calls, "
                + "and the checker resolves them otherwise: " + found);
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
        List<String> found = disagreements("""
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
        assertEquals(List.of(), disagreements("""
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
        assertEquals(List.of(), disagreements("""
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
        assertEquals(List.of(), disagreements("""
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

    /**
     * Nor does a name a binding in the same listing has taken over. The scan does not resolve names,
     * so where one spelling stands for a function in one place and a parameter in another it settles
     * nothing and says nothing — a shadowing is harmless in the language and must be here too.
     */
    @Test
    void aParameterShadowingAFunctionOfTheSameListingSettlesNothing() {
        assertEquals(List.of(), disagreements("""
                [,text]
                ----
                let index (x: Int) = x + 1

                let nth (index: Int, xs: List<String>) =
                    List.get(index, xs)
                ----
                """));
    }

    /** A block's own parameter is a binding like any other. */
    @Test
    void aBlockParameterShadowingAFunctionOfTheSameListingSettlesNothing() {
        assertEquals(List.of(), disagreements("""
                [,text]
                ----
                let p (x: Int) = x > 0

                List.map(p -> List.get(p, xs), ys)
                ----
                """));
    }

    @Test
    void aCallPassingTooFewOrTooManyArgumentsIsCaught() {
        assertEquals(1, disagreements("`+List.map(xs)+`").size());
        assertEquals(1, disagreements("`+List.map(f, xs, more)+`").size());
        assertEquals(List.of(), disagreements("`+List.map(f, xs)+`"));
    }

    /** A pipe supplies the last argument, so the call is written with one fewer. */
    @Test
    void aPipedCallIsReadWithTheArgumentThePipeSupplies() {
        assertEquals(List.of(), disagreements("`+xs |> List.map(.value)+`"));
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
        assertEquals(List.of(), disagreements("`+String.length(...)+`"));
    }

    /**
     * One way the specification contradicts a resolved signature. Identified by the anchor it stands
     * under rather than by its line, which every edit above it moves.
     */
    private record Finding(String anchor, String written, String says, int line) {
        String key() {
            return anchor + ": " + written + " " + says;
        }

        @Override
        public String toString() {
            return "specification.adoc:" + line + " [" + anchor + "] " + written + " " + says;
        }
    }

    private static List<String> keysOf(List<Finding> found) {
        return found.stream().map(Finding::key).sorted().toList();
    }

    private static List<String> disagreements(String adoc) {
        return keysOf(findings(adoc));
    }

    private static List<Finding> findings(String adoc) {
        NavigableMap<Integer, Declared> declared = declarationsByRegion(adoc);
        NavigableMap<Integer, String> anchors = anchorsByOffset(adoc);
        Map<String, ApiCommand.Signature> surface = ApiCommand.surface();
        List<Finding> found = new ArrayList<>();
        for (Call call : callsIn(adoc)) {
            String anchor = anchors.floorEntry(call.at()) == null ? ""
                    : anchors.floorEntry(call.at()).getValue();
            ApiCommand.Signature signature = surface.get(call.name());
            if (signature == null) {
                found.add(call.saying(anchor, "names nothing the standard library publishes"));
                continue;
            }
            if (Prelude.isEmptyCollectionValue(call.name())) {
                found.add(call.saying(anchor, "is a value and takes no argument list"));
                continue;
            }
            int declares = signature.paramNames().size();
            int written = call.args().size() + (call.piped() ? 1 : 0);
            if (written != declares && call.args().stream().noneMatch(a -> ELIDED.matcher(a).find())) {
                found.add(call.saying(anchor, "is written with " + written
                        + " argument(s) and declares " + declares));
            }
            Declared here = declared.floorEntry(call.at()).getValue();
            for (int i = 0; i < call.args().size() && i < declares; i++) {
                boolean takesAFunction = signature.paramTypes().get(i) instanceof Type.FnOf;
                String at = " as argument " + (i + 1) + ", where it declares "
                        + signature.paramNames().get(i) + ": " + Type.show(signature.paramTypes().get(i));
                switch (kindOf(call.args().get(i), here, surface)) {
                    case FUNCTION -> {
                        if (!takesAFunction) {
                            found.add(call.saying(anchor, "is passed a function" + at));
                        }
                    }
                    case NOT_A_FUNCTION -> {
                        if (takesAFunction) {
                            found.add(call.saying(anchor, "is passed something that is not a function" + at));
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
     * nothing here declares — or one a binding of the same region has also taken — settles nothing.
     */
    private static Kind kindOf(String argument, Declared here, Map<String, ApiCommand.Signature> surface) {
        String written = argument.strip();
        if (arrowAt(written) >= 0 || GETTER.matcher(written).matches()) {
            return Kind.FUNCTION;
        }
        if (NOT_A_FUNCTION.matcher(written).matches()) {
            return Kind.NOT_A_FUNCTION;
        }
        if (NAME.matcher(written).matches()) {
            if (here.functions().contains(written)) {
                return here.bindings().contains(written) ? Kind.UNDECIDED : Kind.FUNCTION;
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
        String written() {
            return name + "(" + String.join(", ", args) + ")";
        }

        Finding saying(String anchor, String says) {
            return new Finding(anchor, written(), says, line);
        }
    }

    private static List<Call> callsIn(String adoc) {
        List<Call> calls = new ArrayList<>();
        Matcher m = CALL.matcher(adoc);
        while (m.find()) {
            if (!Reserved.isQualifier(m.group(1))) {
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

    /** What a region of the document declares: the names it declares as functions, and the names it
     *  also binds as something else, which leaves a bare occurrence of one undecided. */
    private record Declared(Set<String> functions, Set<String> bindings) {}

    /**
     * What each region of the document declares, keyed by where the region starts. A listing block
     * is one region and a paragraph outside one is another, so a name is a function where it was
     * declared rather than everywhere the document goes on to write it.
     */
    private static NavigableMap<Integer, Declared> declarationsByRegion(String adoc) {
        NavigableMap<Integer, Declared> byStart = new TreeMap<>();
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
                byStart.put(start, declaredIn(adoc.substring(start, at)));
                start = at;
            }
            at += line.length() + 1;
        }
        byStart.put(start, declaredIn(adoc.substring(Math.min(start, adoc.length()))));
        return byStart;
    }

    private static Declared declaredIn(String region) {
        Set<String> functions = new TreeSet<>();
        Matcher m = DECLARED_FUNCTION.matcher(region);
        while (m.find()) {
            functions.add(m.group(1) != null ? m.group(1) : m.group(2));
        }
        Set<String> bindings = new TreeSet<>();
        Matcher params = PARAMETERS.matcher(region);
        while (params.find()) {
            for (String parameter : params.group(1).split(",")) {
                String binder = parameter.strip().split("[:\\s]", 2)[0];
                if (!binder.isEmpty()) {
                    bindings.add(binder);
                }
            }
        }
        Matcher bare = BARE_PARAMETER.matcher(region);
        while (bare.find()) {
            bindings.add(bare.group(1));
        }
        Matcher value = VALUE_BINDING.matcher(region);
        while (value.find()) {
            bindings.add(value.group(1));
        }
        return new Declared(functions, bindings);
    }

    /** The section anchor in force at each offset, so a finding says where it is by name. */
    private static NavigableMap<Integer, String> anchorsByOffset(String adoc) {
        NavigableMap<Integer, String> byOffset = new TreeMap<>();
        int at = 0;
        for (String line : adoc.split("\n", -1)) {
            Matcher m = ANCHOR.matcher(line.strip());
            if (m.matches()) {
                byOffset.put(at, m.group(1));
            }
            at += line.length() + 1;
        }
        return byOffset;
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
