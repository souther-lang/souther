package souther.compiler.fmt;

import souther.compiler.diag.msg.MessageKeys;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import souther.compiler.ast.Ast;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.SourcePos;
import souther.compiler.frontend.CstFrontend;

import java.lang.reflect.RecordComponent;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the canonical form of a source is allowed to change: how it is written, and nothing the
 * compiler reads. The formatter's other tests ask that its output is what was expected, that it
 * reparses, and that formatting it again writes the same thing. Those measure that it is closed
 * under its own syntax. None of them measures that it is a meaning-preserving transformation, and
 * that is the property a formatter has to have — a source that compiles and a canonical form that
 * does not are not two spellings of one program.
 *
 * <p>The contract is stated against the AST, since that is what the rest of the compiler reads:
 *
 * <pre>{@code
 * frontend(source) = frontend(format(source))
 * }</pre>
 *
 * <p>This is not token preservation and does not imply it. A trailing comma the canonical form drops
 * and a first-arm {@code |} it writes are code tokens the source and its canonical form disagree on,
 * and both sides of this equation are the same — the grammar gives those tokens nothing to leave
 * behind. Whether a {@code fmt --check} deviation witness needs the token property as well is a
 * separate question; this one is the formatter's own correctness and is not up for a decision.
 *
 * <p>It lives here rather than beside the formatter because the formatter cannot state it: it reads
 * a CST and writes text, and the frontend that turns the one into an AST is in this module. So the
 * two implementations of any rule about which spellings are one definition — the frontend's and the
 * formatter's — can only be held against each other from this side.
 *
 * <p>A position is where a node was written and not what it means, so positions are what this
 * comparison drops. Everything else a node carries is compared, names and modifiers and structure
 * included.
 */
@Tag("population")
class TheCanonicalFormMeansWhatTheSourceMeantTest {

    /** The sources the layout rules are swept over: the bundled standard library, and the written
     * ones that build every node kind. What holds over the language has to hold over these first. */
    static Stream<String> corpus() {
        return WhatGoesBetweenTwoTokensOnALineTest.corpus().stream();
    }

    @ParameterizedTest
    @MethodSource("corpus")
    void aCanonicalFormMeansWhatItsSourceMeant(String source) {
        assertEquals(meaning(source), meaning(Formatter.format(source)),
                "the canonical form is a different module:\n" + Formatter.format(source));
    }

    /**
     * And so does the canonical form of each source the code-token rewrites are pinned with. Those
     * rewrites drop and add tokens, and this says what that costs: nothing, because a trailing comma
     * and a first-arm {@code |} are not read by anything downstream.
     */
    @ParameterizedTest
    @MethodSource("souther.compiler.fmt.ACanonicalFormCanRewriteCodeTokensTest#rewrites")
    void andSoDoesOneWhoseCodeTokensChanged(ACanonicalFormCanRewriteCodeTokensTest.Rewrite rewrite) {
        assertEquals(meaning(rewrite.source()), meaning(rewrite.canonical()),
                "these are written differently and are meant to be one module");
    }

    /**
     * A definition that writes a function type is a value of that type, and its lambda stays on the
     * right of {@code =}: writing the parameters on the left would leave the written type describing
     * something the definition is not. That one is the specification's, not the canonical form's —
     * the two spellings are two definitions, so there is nothing here to choose between.
     */
    @Test
    void aDefinitionThatWritesAFunctionTypeKeepsItsLambda() {
        String source = """
                module m

                let f: (Int) -> Int = (x) -> x
                """;
        assertEquals(source, Formatter.format(source));
    }

    /**
     * And a definition that writes no type is written with its parameters on the left. Which of the
     * two spellings a definition has is what the specification settles; which one the canonical form
     * writes is settled here, and this is the whole of it.
     */
    @Test
    void andOneThatWritesNoTypeIsWrittenWithItsParametersOnTheLeft() {
        String source = """
                module m

                let f = (x) -> x
                """;
        assertEquals("""
                module m

                let f (x) = x
                """, Formatter.format(source));
    }

    /** The comparison has to be able to tell two modules apart, or every row above holds vacuously. */
    @Test
    void andTwoModulesThatDifferAreNotOneModule() {
        assertNotEquals(meaning("module m\n\nlet f (x: Int): Int = x\n"),
                meaning("module m\n\nlet f (x: Int): Int = 1\n"));
        assertNotEquals(meaning("module m\n\nlet f: (Int) -> Int = (x) -> x\n"),
                meaning("module m\n\nlet f (x) = x\n"));
    }

    /**
     * The module a source builds, written out with its positions dropped — or, for a source the
     * frontend refuses, what it refused it for. Some of the corpus is written to build a node kind
     * rather than to be a module a model could write, and a refusal is as much what a source means
     * as a module is: the canonical form of one is expected to be refused for the same thing.
     */
    private static String meaning(String source) {
        Ast.Module module;
        try {
            module = CstFrontend.parse(source);
        } catch (CompileException e) {
            return "refused " + e.diagnostic().code() + " " + MessageKeys.of(e.diagnostic().said());
        }
        StringBuilder out = new StringBuilder();
        write(module, out);
        return out.toString();
    }

    private static void write(Object value, StringBuilder out) {
        switch (value) {
            case null -> out.append("absent");
            // where a node was written, which is not what it means
            case SourcePos ignored -> out.append("somewhere");
            // an Optional prints what it holds, and what it holds may be a node
            case Optional<?> held -> write(held.orElse(null), out);
            case List<?> items -> {
                out.append('[');
                for (int i = 0; i < items.size(); i++) {
                    if (i > 0) {
                        out.append(", ");
                    }
                    write(items.get(i), out);
                }
                out.append(']');
            }
            // a map's iteration order is its own business, so it is compared by its entries
            case Map<?, ?> entries -> {
                Map<String, String> written = new TreeMap<>();
                entries.forEach((k, v) -> {
                    StringBuilder key = new StringBuilder();
                    StringBuilder held = new StringBuilder();
                    write(k, key);
                    write(v, held);
                    written.put(key.toString(), held.toString());
                });
                out.append(written);
            }
            case Record node -> {
                out.append(node.getClass().getSimpleName()).append('(');
                RecordComponent[] components = node.getClass().getRecordComponents();
                for (int i = 0; i < components.length; i++) {
                    if (i > 0) {
                        out.append(", ");
                    }
                    out.append(components[i].getName()).append('=');
                    write(componentOf(node, components[i]), out);
                }
                out.append(')');
            }
            default -> out.append(value);
        }
    }

    private static Object componentOf(Record node, RecordComponent component) {
        try {
            component.getAccessor().setAccessible(true);
            return component.getAccessor().invoke(node);
        } catch (ReflectiveOperationException e) {
            throw new AssertionError("a component of " + node.getClass() + " could not be read", e);
        }
    }

    /**
     * Everything the walk reaches is a record, a list, a map, or one of the leaf types whose
     * {@code toString} is its value. A node holding anything else is written out as whatever its
     * class says, and a class that says the same thing for two different values would make every
     * comparison above hold without asking anything.
     */
    @Test
    void andEveryPartOfAModuleIsWrittenAsItsValue() {
        List<String> opaque = new ArrayList<>();
        Set<String> reached = new TreeSet<>();
        for (String source : WhatGoesBetweenTwoTokensOnALineTest.corpus()) {
            Ast.Module module;
            try {
                module = CstFrontend.parse(source);
            } catch (CompileException e) {
                continue;   // a source written to build a node kind, which the frontend refuses
            }
            opaqueParts(module, opaque, reached);
        }
        assertEquals(List.of(), opaque, "written as whatever their class says");
        // and the walk above went somewhere, or it holds by having reached nothing
        assertTrue(reached.containsAll(List.of("Module", "FnDef")), "what it reached is " + reached);
    }

    private static boolean isLeaf(Object value) {
        return value == null || value instanceof SourcePos || value instanceof String
                || value instanceof Enum<?> || value instanceof Number
                || value instanceof Boolean || value instanceof Character;
    }

    private static void opaqueParts(Object value, List<String> out, Set<String> reached) {
        if (isLeaf(value)) {
            return;
        }
        switch (value) {
            case Optional<?> held -> opaqueParts(held.orElse(null), out, reached);
            case List<?> items -> items.forEach(item -> opaqueParts(item, out, reached));
            case Map<?, ?> entries -> entries.forEach((k, v) -> {
                opaqueParts(k, out, reached);
                opaqueParts(v, out, reached);
            });
            case Record node -> {
                reached.add(node.getClass().getSimpleName());
                for (RecordComponent c : node.getClass().getRecordComponents()) {
                    opaqueParts(componentOf(node, c), out, reached);
                }
            }
            default -> out.add(value.getClass().getName());
        }
    }
}
