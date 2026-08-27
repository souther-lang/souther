package souther.lsp.analysis;

import souther.compiler.cst.CstParser;
import souther.compiler.cst.LineIndex;
import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.source.SourceId;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

/**
 * The document being typed in, made whole enough to be resolved, without any of it being answered
 * from an earlier one.
 *
 * <p>What an editor asks about a position is asked while the position is mid-edit. {@code
 * request.plannedCost.} is where a field list is wanted and is not a document that parses — the
 * parser reads {@code .} as a field access only with a name after it — and a document that does not
 * parse is held out of the compile, so the compiler has nothing to say about it exactly where it is
 * being asked. That is not a gap in what the compiler knows. It is the current source not reaching
 * the compiler at all.
 *
 * <p>So the current source is made to reach it. Not the last one that did: a receiver edited from
 * {@code customer.address.} to {@code customer.amount.} would be answered with the fields of
 * {@code Address}, which is a wrong answer wearing the shape of a right one, and worse than no
 * answer. What is compiled here is always what the buffer says now.
 *
 * <p><b>Insertion only, at or after the cursor.</b> Nothing is deleted and nothing replaced, so
 * every offset before the first inserted character is the offset it was, and an extent that ends
 * there covers the characters it covered. What may be read off a probe is exactly that far: an
 * extent ending at or before the insertion. Not "an extent that does not overlap the insertion" —
 * a name put in front of the next line changes how the next line reads without touching it, and
 * overlap does not tell the two apart.
 *
 * <p>Which is enough for what asks. A field list wants the type of what is left of the {@code .},
 * and that ends before it. A signature help wants the callee and which argument is being written:
 * the callee's name ends before the {@code (}, and the argument's number is counted in the source as
 * the author left it — the call's own extent, which would take in a bracket that was put there, is
 * not read.
 *
 * <p>Its own compile, kept beside the workspace's rather than written into it. Two reasons, and each
 * on its own is enough. The workspace's compile publishes diagnostics, and a marker made by a
 * bracket nobody typed is a marker about nothing. And it is incremental: answers stand until
 * something they read changes, so a store fed the real text and the repaired one by turns re-answers
 * the edited module every time it is asked — which is the module every one of these questions is
 * about.
 */
final class SemanticProbe {

    /**
     * The name put in where one is missing.
     *
     * <p>Letters only: a leading {@code _} does not begin a name in this language. It is spelled so
     * as not to be something an author wrote, and nothing rests on that — a module that happened to
     * declare it would resolve the inserted name to it, and the inserted name is inside the
     * insertion, which nothing may read.
     */
    private static final String SENTINEL = "souLspProbe";

    /** A repair, and where it starts. Everything before {@code firstInserted} is the source
     *  unaltered, which is what makes an extent ending there readable. */
    record Repair(String text, int firstInserted) {}

    /**
     * A probe that answered: the compile the repaired source is in, and how far into it may be read.
     *
     * <p>{@code firstInserted} is a place rather than an offset because what is compared against it
     * is an extent, and an extent is two places.
     */
    record Reading(Compilation compilation, String uri, String repaired, SourcePos firstInserted) {

        /**
         * Whether what is written over {@code extent} is the author's rather than the probe's.
         *
         * <p>Ends at or before the insertion, in the file the insertion is in. An extent in another
         * file is the author's too — nothing was inserted there — and one with no extent at all is
         * nothing that can be shown.
         */
        boolean mayBeRead(Region extent) {
            if (extent == null) {
                return false;
            }
            if (!extent.end().isInTheSameTextAs(firstInserted)) {
                return true;
            }
            return extent.end().line() != firstInserted.line()
                    ? extent.end().line() < firstInserted.line()
                    : extent.end().column() <= firstInserted.column();
        }
    }

    private Compilation compile;
    private ModulePath compiledAgainst;

    /**
     * What {@code text} would be with what the cursor is in the middle of finished off, or null
     * where it is not in the middle of anything this knows how to finish.
     *
     * <p>Every candidate is tried against the parser and the first that parses is the repair, so a
     * probe exists only where the source it compiles is a source. Which candidate it was is not
     * recorded: what a reader needs is where the insertion begins, and two repairs that begin in the
     * same place are the same promise about what may be read.
     */
    static Repair repair(String text, int cursor) {
        if (text == null || cursor < 0 || cursor > text.length() || parses(text)) {
            return null;
        }
        Repair afterADot = cursor > 0 && text.charAt(cursor - 1) == '.'
                ? new Repair(text.substring(0, cursor) + SENTINEL + text.substring(cursor), cursor)
                : null;
        if (afterADot != null && parses(afterADot.text())) {
            return afterADot;
        }
        // A call whose closing bracket has not been typed yet. Appended at the end rather than at
        // the cursor: an argument may still be being written after it, and what is wanted is that
        // the call closes somewhere, not that it closes here.
        Repair closed = new Repair(text + ")", text.length());
        return parses(closed.text()) ? closed : null;
    }

    /**
     * The current source of {@code uri}, repaired and compiled, or null where there was nothing to
     * repair or no repair that parses.
     *
     * <p>{@code joining} and {@code broken} are the workspace as the analyzer already sorted it — the
     * documents that can join a compile and the modules of those that cannot. Sorted once and handed
     * over, because which of the two a document is is a question with one answer, and a second
     * reading of it here would be a second answer free to differ.
     */
    Reading of(Map<String, String> joining, Set<String> broken, ModulePath path, String uri,
               String text, int cursor) {
        Repair repair = repair(text, cursor);
        if (repair == null) {
            return null;
        }
        Map<String, String> sources = new LinkedHashMap<>(joining);
        sources.put(uri, repair.text());
        if (compile == null || !path.equals(compiledAgainst)) {
            compile = Compilation.ofDocuments(sources, broken, path);
            compiledAgainst = path;
        } else {
            compile.update(sources, broken);
        }
        // In the document it was inserted into, and said so: a place that names no text is in the
        // same text as nothing, and every extent would compare as being somewhere else — which
        // reads as "the author wrote this" about all of them.
        return new Reading(compile, uri, repair.text(),
                new LineIndex(text, new SourceId(uri)).posOf(repair.firstInserted()));
    }

    /** Forgets the compile it was keeping. What a probe holds is a second store of every answer the
     *  workspace's holds, and a workspace nobody is typing in has no use for one. */
    void forget() {
        compile = null;
        compiledAgainst = null;
    }

    private static boolean parses(String text) {
        try {
            return CstParser.parse(text).errors().isEmpty();
        } catch (RuntimeException | StackOverflowError _) {
            return false;
        }
    }
}
