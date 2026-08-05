package souther.compiler.ast;

import souther.compiler.Reserved;
import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;

/**
 * A name, and the occurrence of it in the source that this one came from.
 *
 * <p>These are two questions with two answers, and a name is asked both. Which name is it — the one
 * a declaration and a reference have to agree on, the one a wire tag is written from, the one a
 * {@code --behavior} argument is matched against — is {@link #canonical()}, and canonically
 * equivalent spellings give one answer because they are one text (ADR-0095). Where is it written and
 * how far does it reach — what a diagnostic underlines, what a rename rewrites, what a cursor is on
 * — is {@link #occurrence()}, which is a place in a file and not anything countable in the name.
 *
 * <p>The two travel together because the second cannot be recovered from the first. Reading a width
 * off the canonical name puts every range short by however many combining marks the author typed,
 * and the failure is invisible until someone writes one: the underline stops mid-name, a rename
 * leaves the marks behind, a cursor on the last character is answered about nothing. Any caller
 * holding a name and a position as two values is a caller that can pair a name with somewhere it is
 * not written, so there is no form here that takes them apart.
 *
 * <p>{@link #lastSegment()} is where the last dot-separated part is written, read off the token that
 * spells it rather than counted in the name: renaming a type rewrites the {@code Amount} of
 * {@code up.Amount} and never the {@code up}, and the two are not a fixed distance apart. A
 * qualified name is read over meaningful tokens, so {@code up . Amount} is one name and so is one
 * carried over a line break by a comment — and an offset counted in {@code "up.Amount"} lands in the
 * wrong column of both.
 *
 * <p>{@link #spelling()} is what a report quotes: the parts joined by dots, which is the name as its
 * author means it whatever sits between them. It is a claim about the name and not about the file;
 * the file is {@link #occurrence()}'s to answer for.
 *
 * <p>A name no one wrote — one a desugaring minted, one a pass synthesized — is {@link #synthetic}:
 * it has a canonical form and somewhere to complain at, and no spelling, because there is no place
 * in the source where those characters are.
 */
public record WrittenName(String canonical, String spelling, Region occurrence, Region lastSegment) {

    public WrittenName {
        if (canonical == null) {
            throw new IllegalArgumentException("a name has a canonical form");
        }
        if (spelling != null && !canonical.equals(Reserved.name(spelling))) {
            throw new IllegalArgumentException(
                    "`" + spelling + "` is not a spelling of `" + canonical + "`");
        }
        if (spelling != null && occurrence == null) {
            throw new IllegalArgumentException(
                    "`" + spelling + "` is spelled somewhere, or it is not a spelling");
        }
        if ((occurrence == null) != (lastSegment == null)) {
            throw new IllegalArgumentException(
                    "a name written somewhere has its last segment written there too");
        }
    }

    /**
     * A name the author wrote as one token, read off the source that spells it. The one door in for
     * a spelling that occupies a single run of characters: canonicalizing happens here, so the name
     * and the place it was written come from one place and cannot be given separately.
     */
    public static WrittenName of(String spelling, SourcePos pos) {
        Region at = pos == null ? null : Region.ofWidth(pos, spelling.length());
        return new WrittenName(Reserved.name(spelling), spelling, at, at);
    }

    /**
     * A name no one wrote, anchored where a complaint about it belongs. {@code anchor} is a form in
     * the source holding something else, so the width taken there is the name's own, that being all
     * there is to take.
     */
    public static WrittenName synthetic(String name, SourcePos anchor) {
        String canonical = Reserved.name(name);
        Region at = anchor == null ? null : Region.ofWidth(anchor, canonical.length());
        return new WrittenName(canonical, null, at, at);
    }

    /** Whether the source spells this name — false for one a pass minted. */
    public boolean authored() {
        return spelling != null;
    }

    /** The text to quote: what the author typed, or the name itself where no one typed it. */
    public String quoted() {
        return spelling == null ? canonical : spelling;
    }

    /** Where the name starts, or null where it is written nowhere at all. */
    public SourcePos pos() {
        return occurrence == null ? null : occurrence.start();
    }

    /** The characters this name occupies — what a report underlines. Null where the name has no
     *  place at all, which is a report with nothing to point at rather than one pointing at zero. */
    public Region region() {
        return occurrence;
    }

    /**
     * Whether {@code at} is one of the characters this name occupies, the far end included so that a
     * cursor resting after the last character is still on the name.
     */
    public boolean covers(SourcePos at) {
        return occurrence != null && holds(occurrence, at);
    }

    /**
     * Whether this name is written inside {@code other}'s occurrence — which of two names that both
     * cover a cursor is the one the cursor is on, a container writing its element's name inside its
     * own span.
     */
    public boolean within(WrittenName other) {
        return occurrence != null && other != null && other.occurrence != null
                && holds(other.occurrence, occurrence.start())
                && holds(other.occurrence, occurrence.end());
    }

    /** Whether {@code at} lies in {@code region}, both ends included and the file counted. */
    private static boolean holds(Region region, SourcePos at) {
        SourcePos start = region.start();
        SourcePos end = region.end();
        if (start == null || end == null || at == null
                || !java.util.Objects.equals(at.sourceId(), start.sourceId())) {
            return false;
        }
        return !before(at, start) && !before(end, at);
    }

    /** Whether {@code a} comes before {@code b} in the file they share. */
    private static boolean before(SourcePos a, SourcePos b) {
        return a.line() != b.line() ? a.line() < b.line() : a.column() < b.column();
    }

    /**
     * This name and a member taken off it, as the one qualified name {@code a.b} that the two spell
     * together.
     *
     * <p>The place is read off the two occurrences rather than assumed: it runs from where this one
     * starts to where the member ends, and the last segment is the member's own. A part nobody wrote
     * makes the whole unwritten — no run of characters spells it — and what is left is somewhere to
     * complain at.
     */
    public WrittenName then(WrittenName member) {
        String joined = canonical + "." + member.canonical();
        if (!authored() || !member.authored()) {
            return new WrittenName(joined, null, occurrence, lastSegment);
        }
        return new WrittenName(joined, spelling + "." + member.spelling(),
                new Region(occurrence.start(), member.occurrence.end()), member.occurrence);
    }

    /** The same name at a different place — what a pass stamping a call site over a copy does. */
    public WrittenName at(SourcePos moved) {
        return spelling == null ? synthetic(canonical, moved) : of(spelling, moved);
    }

    @Override
    public String toString() {
        return canonical;
    }
}
