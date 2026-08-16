package souther.compiler.cst;

import java.util.List;
import java.util.Optional;

/**
 * What may be written at the top level of a file, and the words each of those is opened with.
 *
 * <p>A fact about the language and not about any one reader of it. The parser dispatches on this, a
 * recovery works out from it where a parse may pick itself up again, and an editor offering to write
 * a declaration asks it what there is to offer. Those three asked the same question of three lists
 * of words before, and the one that was written for the editor could only ever have been a fourth.
 *
 * <p>The words are not the reserved keywords. {@code example}, {@code fake} and the {@code for} of
 * an {@code examples for} header are ordinary identifiers everywhere else, and a reader that took
 * {@link CstLexer#keywords()} for the set of things a declaration may start with would be short by
 * two whole forms of definition. Nor is a keyword enough to name one: a {@code let} may have
 * modifiers written in front of it, and it is the same form with or without them.
 *
 * <p>Nothing here says how a form is read past its first words. Which routine reads which form is
 * the parser's, where the grammar is.
 */
public enum TopLevelForm {

    MODULE_HEADER(Region.FILE_HEADER, Word.of(SyntaxKind.MODULE_KW)),
    EXAMPLES_FILE_HEADER(Region.FILE_HEADER, Word.of("examples"), Word.of("for")),
    IMPORT(Region.PRELUDE, Word.of(SyntaxKind.IMPORT_KW)),
    DATA(Region.BODY, Word.of(SyntaxKind.DATA_KW)),
    BEHAVIOR(Region.BODY, Word.of(SyntaxKind.BEHAVIOR_KW)),
    FN(Region.BODY, List.of(Word.of("private"), Word.of("partial")), Word.of(SyntaxKind.LET_KW)),
    EXAMPLE(Region.BODY, Word.of("example")),
    FAKE(Region.BODY, Word.of("fake"));

    /**
     * Where in a file a form may open something.
     *
     * <p>A file is read as a header, then the imports, then everything else, and this says which of
     * those three a form belongs to. It is what the parse reads in order and what an editor asks
     * about a cursor: a {@code module} line is not something to offer halfway down a file.
     */
    public enum Region { FILE_HEADER, PRELUDE, BODY }

    /** A reader of the meaningful tokens ahead of a point, counted from it. */
    public interface Lookahead {

        /** The kind of the {@code i}th meaningful token from here, or {@link SyntaxKind#EOF}. */
        SyntaxKind kindAt(int i);

        /** Its exact text. */
        String textAt(int i);
    }

    /**
     * One word a form is opened with, however the lexer happens to treat it.
     *
     * <p>A reserved word is matched by its kind and spells itself through {@link
     * SyntaxKind#fixedSpelling()}; a contextual one lexes as an identifier and is matched by its
     * text. Either way the spelling is held once, so what recognises a form and what an editor shows
     * for it cannot come apart.
     */
    public record Word(SyntaxKind kind, String spelling) {

        public static Word of(SyntaxKind kind) {
            return new Word(kind, kind.fixedSpelling().orElseThrow(
                    () -> new IllegalArgumentException(kind + " does not spell itself")));
        }

        /** A contextual word: an ordinary identifier that opens a form only where it stands. */
        public static Word of(String contextual) {
            return new Word(SyntaxKind.IDENT, contextual);
        }

        private boolean matchesAt(Lookahead ahead, int i) {
            return ahead.kindAt(i) == kind
                    && (kind != SyntaxKind.IDENT || spelling.equals(ahead.textAt(i)));
        }
    }

    private final Region region;
    private final List<Word> modifiers;
    private final List<Word> words;

    TopLevelForm(Region region, Word... words) {
        this(region, List.of(), words);
    }

    TopLevelForm(Region region, List<Word> modifiers, Word... words) {
        this.region = region;
        this.modifiers = modifiers;
        this.words = List.of(words);
    }

    public Region region() {
        return region;
    }

    /**
     * How this form is written, for a reader being offered it.
     *
     * <p>The words it is recognised by, so the two cannot disagree. The modifiers are left out: they
     * may be written in front of a form but they do not open one, and a reader offered
     * {@code private let} would be shown a choice the language does not make for them.
     */
    public String starter() {
        return String.join(" ", words.stream().map(Word::spelling).toList());
    }

    /** The same, as the tokens they are — for a reader writing the form out rather than showing it. */
    public List<Word> words() {
        return words;
    }

    /**
     * Whether the tokens ahead open this form, past any modifiers written in front of it.
     *
     * <p>The first word, and not all of them. What opens a form and what it is written with are the
     * same everywhere but one: an {@code examples for} header is two words, and a file whose first
     * line is {@code examples m} has opened one and left a word out. Reading it as opening nothing
     * takes the line away from the routine that would say which word is missing, and takes the
     * header off the file with it — so what is read here is enough to say which form it is, and
     * saying what is wrong with the rest of it belongs to whatever reads the form.
     *
     * <p>Enough because the opening words differ: no two forms begin with the same one.
     */
    public boolean startsAt(Lookahead ahead) {
        int i = 0;
        for (Word modifier : modifiers) {
            if (modifier.matchesAt(ahead, i)) {
                i++;
            }
        }
        return words.getFirst().matchesAt(ahead, i);
    }

    /** The form the tokens ahead open, or empty where they open none. */
    public static Optional<TopLevelForm> at(Lookahead ahead) {
        for (TopLevelForm form : values()) {
            if (form.startsAt(ahead)) {
                return Optional.of(form);
            }
        }
        return Optional.empty();
    }
}
