package souther.compiler.ast;

import souther.compiler.Reserved;
import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;

/**
 * A name, and the occurrence of it in the source that this one came from.
 *
 * <p>These are two questions with two answers, and a name is asked both. Which name is it — the one a
 * declaration and a reference have to agree on, the one a wire tag is written from, the one a
 * {@code --behavior} argument is matched against — is {@link #canonical()}, and canonically
 * equivalent spellings give one answer because they are one text (ADR-0095). Where is it written and
 * how far does it reach — what a diagnostic underlines, what a rename rewrites, what a cursor is on
 * — is {@link #spelling()} and {@link #pos()}, and those are the characters on disk, which a
 * decomposed spelling has more of than the composed name it denotes.
 *
 * <p>The two travel together because the second cannot be recovered from the first. Reading a width
 * off the canonical name puts every range short by however many combining marks the author typed,
 * and the failure is invisible until someone writes one: the underline stops mid-name, a rename
 * leaves the marks behind, a cursor on the last character is answered about nothing. Any caller
 * holding a name and a position as two values is a caller that can pair a name with somewhere it is
 * not written, so there is no form here that takes them apart.
 *
 * <p>A name no one wrote — one a desugaring minted, one a pass synthesized — is {@link #synthetic}:
 * it has a canonical form and an anchor to complain at, and no spelling, because there is no place
 * in the source where those characters are.
 */
public record WrittenName(String canonical, String spelling, SourcePos pos) {

    public WrittenName {
        if (canonical == null) {
            throw new IllegalArgumentException("a name has a canonical form");
        }
        if (spelling != null && !canonical.equals(Reserved.name(spelling))) {
            throw new IllegalArgumentException(
                    "`" + spelling + "` is not a spelling of `" + canonical + "`");
        }
    }

    /**
     * A name the author wrote, read off the source that spells it. The only door in for a spelling:
     * canonicalizing happens here, so the name and the characters it was written with come from one
     * place and cannot be given separately.
     */
    public static WrittenName of(String spelling, SourcePos pos) {
        return new WrittenName(Reserved.name(spelling), spelling, pos);
    }

    /**
     * A name no one wrote, anchored where a complaint about it belongs. {@code anchor} is a form in
     * the source holding something else, so it says nothing about how wide this name is there.
     */
    public static WrittenName synthetic(String name, SourcePos anchor) {
        return new WrittenName(Reserved.name(name), null, anchor);
    }

    /** Whether the source spells this name — false for one a pass minted. */
    public boolean authored() {
        return spelling != null;
    }

    /** The text to quote: what the author typed, or the name itself where no one typed it. */
    public String quoted() {
        return spelling == null ? canonical : spelling;
    }

    /** How many UTF-16 units this occupies where it is written — what an underline covers. */
    public int width() {
        return quoted().length();
    }

    /**
     * How far past {@link #pos()} the last segment of a qualified name starts.
     *
     * <p>Counted in the spelling rather than in the name: renaming a type rewrites the {@code Amount}
     * of {@code up.Amount} and never the {@code up}, and a qualifier that composes to fewer units
     * than it was written with moves that boundary. Taking the offset off the canonical name puts
     * the rewrite inside the qualifier.
     */
    public int lastSegmentOffset() {
        return quoted().lastIndexOf('.') + 1;
    }

    /** How many units the last segment of a qualified name occupies. */
    public int lastSegmentWidth() {
        return width() - lastSegmentOffset();
    }

    /**
     * This name and a member taken off it, as the one qualified name {@code a.b} that the two spell
     * together, starting where this one starts.
     *
     * <p>The spelling is the two joined by a dot, which is what the source has where a qualified
     * name is written the ordinary way. A part nobody wrote makes the whole unwritten: there is no
     * run of characters that spells it.
     */
    public WrittenName then(WrittenName member) {
        String joined = authored() && member.authored() ? spelling + "." + member.spelling() : null;
        return new WrittenName(canonical + "." + member.canonical(), joined, pos);
    }

    /** The characters this name occupies — what a report underlines. Null where the name has no
     *  place at all, which is a report with nothing to point at rather than one pointing at zero. */
    public Region region() {
        return pos == null ? null : Region.ofWidth(pos, width());
    }

    /** The same name at a different place — what a pass stamping a call site over a copy does. */
    public WrittenName at(SourcePos moved) {
        return new WrittenName(canonical, spelling, moved);
    }

    @Override
    public String toString() {
        return canonical;
    }
}
