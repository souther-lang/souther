package souther.compiler.frontend;

import souther.compiler.ast.Ast;
import souther.test.RepositoryLayout;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a definition is read as does not turn on what was written beside it.
 *
 * <p>Every number the builder hands out is an identity or a name, and both are carried from here to
 * the end: a coverage obligation is the construct it was numbered as, a rule is the block it was
 * numbered as, and a binder a lowering minted is the name it was given. Counted over the file, each
 * of those is a function of everything written before it there — so declaring a helper renumbers
 * every construct after it, an importer that cannot name the helper is handed a declaration that
 * says something new, and the work of a whole module runs again for an edit nothing about it can
 * see.
 *
 * <p>So the property is about pairs of sources rather than about any one of them. Write the same
 * model twice, once with a definition ahead of it that numbers something and once with the same
 * definition numbering one thing more, and every definition the two share must be read the same
 * way. The two probes are one line each, so nothing after them moves and no position has to be
 * passed over to compare what is left.
 *
 * <p>Asked of every model this repository carries. The counters are one shape and there are several
 * of them; a test naming the constructs it thought of would answer about those and leave the next
 * one to be found by an author.
 */
class WhatIsWrittenBesideADefinitionDoesNotNumberItTest {

    /** A definition that numbers nothing beyond itself. */
    private static final String NUMBERS_NOTHING = "let aProbeThatNumbersNothing = 0";

    /** The same definition with one construct more in it — a comparison, which takes a number. */
    private static final String NUMBERS_ONE_MORE = "let aProbeThatNumbersNothing = 0 + 0";

    /** What the probe is filed under among what a module declares. */
    private static final String THE_PROBE = "let aProbeThatNumbersNothing";

    @Test
    void aDefinitionIsReadTheSameWhateverIsWrittenBeforeIt() {
        List<String> corpus = everySourceTheRepositoryCarries();
        assertFalse(corpus.isEmpty(), "a property over no source would hold for any reason");

        List<String> moved = new ArrayList<>();
        int compared = 0;
        for (String source : corpus) {
            Ast.Module numbersNothing = parsed(withAProbe(source, NUMBERS_NOTHING));
            Ast.Module numbersOneMore = parsed(withAProbe(source, NUMBERS_ONE_MORE));
            if (numbersNothing == null || numbersOneMore == null) {
                continue;   // not a source this asks about: the parser refused it
            }
            Map<String, Object> before = whatItDeclares(numbersNothing);
            Map<String, Object> after = whatItDeclares(numbersOneMore);
            for (Map.Entry<String, Object> each : before.entrySet()) {
                Object beside = after.get(each.getKey());
                // The probe is what differs between the two, and is the one definition this asks
                // nothing about.
                if (beside == null || each.getKey().equals(THE_PROBE)) {
                    continue;
                }
                compared++;
                if (!each.getValue().equals(beside)) {
                    moved.add(numbersNothing.name() + " " + each.getKey());
                }
            }
        }

        assertTrue(compared > 0, "nothing was compared, so nothing was held");
        assertEquals(List.of(), moved,
                "these are read differently for a definition written before them that numbers one"
                        + " thing more, so what they were numbered as is a count over the file"
                        + " rather than within what wrote them");
    }

    /**
     * The control: the two probes really do differ by a number the builder hands out.
     *
     * <p>Without it the property above would hold for a pair of sources that were the same source,
     * and would go on holding after the counters went back to counting the file.
     */
    @Test
    void andTheTwoProbesAreToldApartByWhatTheyNumber() {
        Ast.Module numbersNothing = parsed(withAProbe("module probe exposing ( )\n",
                NUMBERS_NOTHING));
        Ast.Module numbersOneMore = parsed(withAProbe("module probe exposing ( )\n",
                NUMBERS_ONE_MORE));

        assertNotEquals(whatItDeclares(numbersNothing).get(THE_PROBE),
                whatItDeclares(numbersOneMore).get(THE_PROBE),
                "the probe that numbers one more is the same definition either way");
    }

    /** {@code source} with {@code probe} written as its first definition — after the header, so that
     *  the header is still the first line and one line is added either way. */
    private static String withAProbe(String source, String probe) {
        int firstLine = source.indexOf('\n');
        if (firstLine < 0) {
            return source + "\n" + probe + "\n";
        }
        return source.substring(0, firstLine + 1) + probe + "\n" + source.substring(firstLine + 1);
    }

    /** The module, or null where the parser refused the source. */
    private static Ast.Module parsed(String source) {
        try {
            return CstFrontend.parse(source, null);
        } catch (RuntimeException refused) {
            return null;
        }
    }

    /** What the module declares, by what it is written as and called — everything but the probe. */
    private static Map<String, Object> whatItDeclares(Ast.Module module) {
        Map<String, Object> declared = new LinkedHashMap<>();
        for (Ast.Def def : module.defs()) {
            declared.put("data " + def.name(), def);
        }
        for (Ast.BehaviorDef behavior : module.behaviors()) {
            declared.put("behavior " + behavior.written().canonical(), behavior);
        }
        for (Ast.FnDef fn : module.fns()) {
            declared.put("let " + fn.written().canonical(), fn);
        }
        for (Ast.Example example : module.examples()) {
            declared.put("example " + example.target(), example);
        }
        for (Ast.Fake fake : module.fakes()) {
            declared.put("fake " + fake.target().name(), fake);
        }
        return declared;
    }

    /** Every {@code .sou} file the repository carries: the corpora, the models written to be worked
     *  with, and the library the language ships. */
    private static List<String> everySourceTheRepositoryCarries() {
        Path root = RepositoryLayout.ofWorkingDirectory().root();
        List<String> sources = new ArrayList<>();
        try (Stream<Path> walk = Files.walk(root)) {
            for (Path each : walk.filter(Files::isRegularFile)
                    .filter(it -> it.getFileName().toString().endsWith(".sou"))
                    .filter(it -> !it.toString().contains("/target/"))
                    .sorted().toList()) {
                sources.add(Files.readString(each));
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        return sources;
    }
}
