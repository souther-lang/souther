package souther.compiler.cst;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Each {@link TopLevelForm} is recognised by the words it lists and read by the routine that reads
 * that form, and here the two are held to one source apiece.
 *
 * <p>The catalog is what the parser dispatches on, so asking whether the parser accepts what the
 * catalog lists would be asking the catalog about itself. What can still go wrong is a form whose
 * words and whose routine are not about the same construct: an entry added with a starter nothing
 * reads falls through to recovery, and one whose words match a construct the routine does not read
 * produces the wrong node. A source per form catches both, and a form added with no source here
 * fails for want of one.
 *
 * <p>The sources and the node kinds are written out rather than derived. Deriving either from the
 * catalog would make the agreement hold by construction, which is a check that cannot fail.
 */
class ATopLevelFormIsParsedByTheEntryThatListsItTest {

    /** One source per form, each holding that form and nothing else that could stand for it. */
    private static final Map<TopLevelForm, String> WITNESSES = witnesses();

    /** The node each form's routine builds. */
    private static final Map<TopLevelForm, SyntaxKind> PRODUCES = produces();

    private static Map<TopLevelForm, String> witnesses() {
        Map<TopLevelForm, String> sources = new LinkedHashMap<>();
        sources.put(TopLevelForm.MODULE_HEADER, "module m\n");
        sources.put(TopLevelForm.EXAMPLES_FILE_HEADER, "examples for m\n");
        sources.put(TopLevelForm.IMPORT, "import up ( a )\n");
        sources.put(TopLevelForm.DATA, "data A = { v: Int }\n");
        sources.put(TopLevelForm.BEHAVIOR, "behavior f : (x: Int) -> Int\n");
        sources.put(TopLevelForm.FN, "let f (x) = x\n");
        sources.put(TopLevelForm.EXAMPLE, "example f\n    | (1) -> 1\n");
        sources.put(TopLevelForm.FAKE, "fake f\n    | _ -> 1\n");
        return sources;
    }

    private static Map<TopLevelForm, SyntaxKind> produces() {
        Map<TopLevelForm, SyntaxKind> kinds = new LinkedHashMap<>();
        kinds.put(TopLevelForm.MODULE_HEADER, SyntaxKind.MODULE_HEADER);
        kinds.put(TopLevelForm.EXAMPLES_FILE_HEADER, SyntaxKind.EXAMPLES_FILE_HEADER);
        kinds.put(TopLevelForm.IMPORT, SyntaxKind.IMPORT_DECL);
        kinds.put(TopLevelForm.DATA, SyntaxKind.DATA_DEF);
        kinds.put(TopLevelForm.BEHAVIOR, SyntaxKind.BEHAVIOR_DEF);
        kinds.put(TopLevelForm.FN, SyntaxKind.FN_DEF);
        kinds.put(TopLevelForm.EXAMPLE, SyntaxKind.EXAMPLE_DEF);
        kinds.put(TopLevelForm.FAKE, SyntaxKind.FAKE_DEF);
        return kinds;
    }

    @Test
    void everyFormHasASourceHere() {
        List<TopLevelForm> unwitnessed = new ArrayList<>();
        for (TopLevelForm form : TopLevelForm.values()) {
            if (!WITNESSES.containsKey(form) || !PRODUCES.containsKey(form)) {
                unwitnessed.add(form);
            }
        }
        assertEquals(List.of(), unwitnessed, "a form nothing here is written for");
    }

    /** The words a form lists reach that form and no other. */
    @Test
    void aSourceStartsWithTheFormThatListsIt() {
        List<String> wrong = new ArrayList<>();
        WITNESSES.forEach((form, source) -> {
            Optional<TopLevelForm> found = TopLevelForm.at(lookahead(source));
            if (found.isEmpty() || found.get() != form) {
                wrong.add(source.lines().findFirst().orElse("") + " reached " + found);
            }
        });
        assertEquals(List.of(), wrong, "a source does not reach the form that lists its words");
    }

    /** And the routine that reads the form builds the node the form is about. */
    @Test
    void aSourceIsReadIntoTheNodeItsFormIsAbout() {
        List<String> wrong = new ArrayList<>();
        WITNESSES.forEach((form, source) -> {
            CstParser.Result parsed = CstParser.parse(source);
            List<SyntaxKind> children = parsed.root().childNodes().stream()
                    .map(SyntaxNode::kind).toList();
            if (!parsed.errors().isEmpty()) {
                wrong.add(form + " does not parse: " + parsed.errors());
            } else if (!children.contains(PRODUCES.get(form))) {
                wrong.add(form + " was read as " + children);
            }
        });
        assertEquals(List.of(), wrong, "a form's words and its routine are about different things");
    }

    /**
     * A modifier in front of {@code let} is still the same form.
     *
     * <p>The words a form is recognised by are not all of what may stand in front of it, and the
     * modifiers are the one place that is so. Read the other way, a bare {@code private} opens
     * nothing, so an identifier spelled that way at the top level is not half a definition.
     */
    @Test
    void aModifierInFrontOfLetOpensTheSameForm() {
        assertEquals(Optional.of(TopLevelForm.FN), TopLevelForm.at(lookahead("private let f (x) = x")));
        assertEquals(Optional.of(TopLevelForm.FN), TopLevelForm.at(lookahead("partial let f (x) = x")));
        assertEquals(Optional.of(TopLevelForm.FN),
                TopLevelForm.at(lookahead("private partial let f (x) = x")));
        assertEquals(Optional.empty(), TopLevelForm.at(lookahead("private f (x) = x")));
        assertEquals(Optional.empty(), TopLevelForm.at(lookahead("partial")));
    }

    /** The meaningful tokens of {@code source}, as a reader ahead of them. */
    private static TopLevelForm.Lookahead lookahead(String source) {
        List<GreenToken> tokens = CstLexer.lex(source).tokens().stream()
                .filter(token -> !token.kind().isTrivia()).toList();
        return new TopLevelForm.Lookahead() {
            @Override
            public SyntaxKind kindAt(int i) {
                return i < tokens.size() ? tokens.get(i).kind() : SyntaxKind.EOF;
            }

            @Override
            public String textAt(int i) {
                return i < tokens.size() ? tokens.get(i).text() : "";
            }
        };
    }
}
