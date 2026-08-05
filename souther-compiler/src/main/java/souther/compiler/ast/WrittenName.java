package souther.compiler.ast;

import souther.compiler.Reserved;
import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * A name, and the occurrence of it in the source that this one came from.
 *
 * <p>These are two questions with two answers, and a name is asked both. Which name is it — the one
 * a declaration and a reference have to agree on, the one a wire tag is written from, the one a
 * {@code --behavior} argument is matched against — is {@link #canonical()}, and canonically
 * equivalent spellings give one answer because they are one text (ADR-0095). Where is it written —
 * what a report underlines, what a rename rewrites, what a cursor is on — is {@link #segments()}.
 *
 * <p>The two travel together because the second cannot be recovered from the first. Reading a width
 * off the canonical name puts every range short by however many combining marks the author typed,
 * and the failure is invisible until someone writes one: the underline stops mid-name, a rename
 * leaves the marks behind, a cursor on the last character is answered about nothing. Any caller
 * holding a name and a position as two values is a caller that can pair a name with somewhere it is
 * not written, so there is no form here that takes them apart.
 *
 * <p>The place is <b>the tokens</b> and not the stretch of file they lie in. A qualified name is read
 * over meaningful tokens, so {@code up . Amount} is one name and so is one a comment carries over a
 * line break — and the whitespace, the dots and the comment between the parts are not the name. Two
 * questions want two answers here as well, and this is the second pair the design got wrong:
 * {@link #region()} is what a report underlines, one continuous stretch, comment and all, because an
 * underline with holes in it is not something to read. {@link #covers} is whether a cursor is on the
 * name, and it is on it only where a token is. Answering the second with the first put
 * go-to-definition and rename under the cursor in the middle of a comment.
 *
 * <p>{@link #spelling()} is what a report quotes: the parts joined by dots, which is the name as its
 * author means it whatever sits between them. It is a claim about the name and not about the file.
 *
 * <p>A name no one wrote — one a desugaring minted, one a pass synthesized — is {@link #synthetic}:
 * it has a canonical form and somewhere to complain at, and no spelling, because there is no place
 * in the source where those characters are.
 */
public record WrittenName(String canonical, String spelling, List<Region> segments) {

    public WrittenName {
        if (canonical == null) {
            throw new IllegalArgumentException("a name has a canonical form");
        }
        segments = segments == null ? List.of() : List.copyOf(segments);
        if (spelling != null && !canonical.equals(Reserved.name(spelling))) {
            throw new IllegalArgumentException(
                    "`" + spelling + "` is not a spelling of `" + canonical + "`");
        }
        if (spelling != null && segments.isEmpty()) {
            throw new IllegalArgumentException(
                    "`" + spelling + "` is spelled somewhere, or it is not a spelling");
        }
        for (Region segment : segments) {
            if (!Objects.equals(segment.start().sourceId(), segments.get(0).start().sourceId())) {
                throw new IllegalArgumentException("`" + canonical + "` is written in one file");
            }
        }
    }

    /**
     * A name the author wrote as one token, read off the source that spells it. The one door in for
     * a spelling that occupies a single run of characters: canonicalizing happens here, so the name
     * and the place it was written come from one place and cannot be given separately.
     */
    public static WrittenName of(String spelling, SourcePos pos) {
        return new WrittenName(Reserved.name(spelling), spelling,
                pos == null ? List.of() : List.of(Region.ofWidth(pos, spelling.length())));
    }

    /**
     * A name no one wrote, anchored where a complaint about it belongs. {@code anchor} is a form in
     * the source holding something else, so the width taken there is the name's own, that being all
     * there is to take.
     */
    public static WrittenName synthetic(String name, SourcePos anchor) {
        String canonical = Reserved.name(name);
        return new WrittenName(canonical, null,
                anchor == null ? List.of() : List.of(Region.ofWidth(anchor, canonical.length())));
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
        return segments.isEmpty() ? null : segments.get(0).start();
    }

    /**
     * The stretch of file a report underlines: from where the name starts to where it ends, whatever
     * lies between its parts. Null where the name has no place at all, which is a report with
     * nothing to point at rather than one pointing at zero.
     *
     * <p>Not what {@link #covers} answers. An underline is read as one mark and a cursor is on one
     * character, so a comment inside a qualified name is under the underline and is not on the name.
     */
    public Region region() {
        return segments.isEmpty() ? null
                : new Region(segments.get(0).start(), segments.get(segments.size() - 1).end());
    }

    /** Where the last dot-separated part is written — the only part a rename rewrites, since
     *  renaming a type rewrites the {@code Amount} of {@code up.Amount} and never the {@code up}. */
    public Region lastSegment() {
        return segments.isEmpty() ? null : segments.get(segments.size() - 1);
    }

    /** Whether {@code at} is one of the characters that spell this name, the far end of a part
     *  included so that a cursor resting after its last character is still on it. */
    public boolean covers(SourcePos at) {
        return segments.stream().anyMatch(segment -> holds(segment, at));
    }

    /**
     * Whether this name is written inside {@code other}'s — which of two names that both cover a
     * cursor is the one the cursor is on, a container writing its element's name inside its own.
     */
    public boolean within(WrittenName other) {
        Region mine = region();
        Region theirs = other == null ? null : other.region();
        return mine != null && theirs != null
                && holds(theirs, mine.start()) && holds(theirs, mine.end());
    }

    /** Whether {@code at} lies in {@code region}, both ends included and the file counted. */
    private static boolean holds(Region region, SourcePos at) {
        SourcePos start = region.start();
        SourcePos end = region.end();
        if (start == null || end == null || at == null
                || !Objects.equals(at.sourceId(), start.sourceId())) {
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
     * <p>The parts are kept as the parts they are rather than merged into the stretch they span, so
     * what a report underlines and what a cursor is on stay two answers. A part nobody wrote makes
     * the whole unwritten — no run of characters spells it — and what is left is somewhere to
     * complain at.
     */
    public WrittenName then(WrittenName member) {
        String joined = canonical + "." + member.canonical();
        if (!authored() || !member.authored()) {
            return new WrittenName(joined, null, segments);
        }
        List<Region> both = new ArrayList<>(segments);
        both.addAll(member.segments);
        return new WrittenName(joined, spelling + "." + member.spelling(), both);
    }

    @Override
    public String toString() {
        return canonical;
    }
}
