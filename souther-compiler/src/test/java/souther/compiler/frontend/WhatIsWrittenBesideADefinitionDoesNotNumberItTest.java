package souther.compiler.frontend;

import souther.compiler.ast.Ast;
import souther.compiler.diag.SourcePos;
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

    /**
     * The sources this asks nothing of, and why: they declare nothing, so there is nothing for a
     * definition written ahead of them to number.
     *
     * <p>Written down rather than passed over. A source dropped where it is met leaves the property
     * holding over whatever was left and says nothing about which sources those were, which is the
     * shape of an answer that shrinks without anybody noticing.
     */
    private static final List<String> DECLARES_NOTHING =
            List.of("souther-compiler/src/main/resources/souther/instant.sou");

    @Test
    void aDefinitionIsReadTheSameWhateverIsWrittenBeforeIt() {
        Map<String, String> corpus = everySourceTheRepositoryCarries();
        assertFalse(corpus.isEmpty(), "a property over no source would hold for any reason");

        List<String> moved = new ArrayList<>();
        List<String> refused = new ArrayList<>();
        List<String> declaringNothing = new ArrayList<>();
        int compared = 0;
        for (Map.Entry<String, String> each : corpus.entrySet()) {
            String source = each.getValue();
            Ast.Module written = parsed(source);
            if (written == null || whereItsDefinitionsBegin(written).isEmpty()) {
                // A source that declares nothing has nothing for a definition written ahead of it
                // to number, and one the parser refuses as it stands is not this property's to ask
                // about. Both are said below rather than passed over here.
                declaringNothing.add(each.getKey());
                continue;
            }
            Ast.Module numbersNothing = parsed(withAProbe(written, source, NUMBERS_NOTHING));
            Ast.Module numbersOneMore = parsed(withAProbe(written, source, NUMBERS_ONE_MORE));
            if (numbersNothing == null || numbersOneMore == null) {
                // Said rather than passed over. A source dropped here leaves the property holding
                // over whatever was left, and nothing would say which sources that was.
                refused.add(each.getKey());
                continue;
            }
            Map<String, Object> before = whatItDeclares(numbersNothing);
            Map<String, Object> after = whatItDeclares(numbersOneMore);
            for (Map.Entry<String, Object> declared : before.entrySet()) {
                Object beside = after.get(declared.getKey());
                // The probe is what differs between the two, and is the one definition this asks
                // nothing about.
                if (beside == null || declared.getKey().equals(THE_PROBE)) {
                    continue;
                }
                compared++;
                if (!declared.getValue().equals(beside)) {
                    moved.add(numbersNothing.name() + " " + declared.getKey());
                }
            }
        }

        assertEquals(List.of(), refused,
                "these are sources this repository carries and the property was not asked of them,"
                        + " so what it holds is about the rest. A source that cannot be read with a"
                        + " definition written ahead of it belongs here with the reason");
        assertEquals(DECLARES_NOTHING, declaringNothing,
                "a source this asks nothing of is named here with the reason. One that has left the"
                        + " list has definitions now and is asked about; one that has joined it"
                        + " stopped declaring anything, and either is a thing to know");
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
        String declaringOne = "module probe exposing ( )\n\nlet beside = 1\n";
        Ast.Module written = parsed(declaringOne);
        Ast.Module numbersNothing =
                parsed(withAProbe(written, declaringOne, NUMBERS_NOTHING));
        Ast.Module numbersOneMore =
                parsed(withAProbe(written, declaringOne, NUMBERS_ONE_MORE));

        assertNotEquals(whatItDeclares(numbersNothing).get(THE_PROBE),
                whatItDeclares(numbersOneMore).get(THE_PROBE),
                "the probe that numbers one more is the same definition either way");
    }

    /**
     * {@code source} with {@code probe} written as its first definition.
     *
     * <p>Placed where the source says its definitions begin and not at a line counted from the top:
     * a file may open with anything the grammar lets it open with — a comment, a header written over
     * several lines, imports — and a probe written into the middle of that is a source the parser
     * refuses. Where it goes is read off the parse, and one line is added either way, so nothing
     * moves between the two.
     *
     * <p>Null where the source declares nothing, there being no definition for one written ahead of
     * it to number.
     */
    private static String withAProbe(Ast.Module written, String source, String probe) {
        int firstDefinition = Integer.MAX_VALUE;
        for (SourcePos pos : whereItsDefinitionsBegin(written)) {
            firstDefinition = Math.min(firstDefinition, pos.line());
        }
        if (firstDefinition == Integer.MAX_VALUE) {
            return null;
        }
        List<String> lines = new ArrayList<>(List.of(source.split("\n", -1)));
        lines.add(firstDefinition - 1, probe);
        return String.join("\n", lines);
    }

    /** Where each thing the module declares is written. */
    private static List<SourcePos> whereItsDefinitionsBegin(Ast.Module module) {
        List<SourcePos> begins = new ArrayList<>();
        module.defs().forEach(it -> begins.add(it.pos()));
        module.behaviors().forEach(it -> begins.add(it.pos()));
        module.fns().forEach(it -> begins.add(it.pos()));
        module.examples().forEach(it -> begins.add(it.pos()));
        module.fakes().forEach(it -> begins.add(it.pos()));
        return begins;
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

    /** Every {@code .sou} file the repository carries, by where it is written: the corpora, the
     *  models written to be worked with, and the library the language ships. */
    private static Map<String, String> everySourceTheRepositoryCarries() {
        Path root = RepositoryLayout.ofWorkingDirectory().root();
        Map<String, String> sources = new LinkedHashMap<>();
        try (Stream<Path> walk = Files.walk(root)) {
            for (Path each : walk.filter(Files::isRegularFile)
                    .filter(it -> it.getFileName().toString().endsWith(".sou"))
                    .filter(it -> !it.toString().contains("/target/"))
                    .sorted().toList()) {
                sources.put(root.relativize(each).toString(), Files.readString(each));
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        return sources;
    }
}
