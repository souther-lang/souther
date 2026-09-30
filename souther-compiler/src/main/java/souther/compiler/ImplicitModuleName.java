package souther.compiler;

import souther.compiler.cst.IdentifierAlphabet;

/**
 * What a lone source with no {@code module} header is called.
 *
 * <p>The specification names it after the file it was read from — the file-name stem — and names it
 * {@code Main} only where there is no file, a source handed over as a string. Written once here,
 * because every way into the compiler that holds a file has to give the same answer for it: the
 * classes a build writes land in a package of this name, and a second rule would put one file's
 * classes in two places depending on which tool built it.
 *
 * <p>Not what the source is called. A source that writes a header is called what it says, and this
 * is only what it falls back to where it says nothing.
 */
public final class ImplicitModuleName {

    /** What a header-less source handed over with no file name is called. */
    public static final String OF_A_TEXT = "Main";

    /** What a header-less file is called when its stem is not a name a module can take. */
    private static final String OF_AN_UNUSABLE_STEM = "main";

    private ImplicitModuleName() {}

    /**
     * What a header-less source read from {@code fileName} is called: the name up to its first dot.
     *
     * <p>Canonicalized before it is judged, not after: a file delivered by macOS carries its name
     * decomposed, so the same file would otherwise be judged as two spellings on two machines.
     *
     * <p>A stem is usable where it is a name as the language spells one ({@link IdentifierAlphabet}),
     * so what a module may be called does not depend on whether it was named by a header or by its
     * file, nor on which JDK the compile ran on.
     *
     * @param fileName the file's own name, with no directory in front of it
     */
    public static String ofFileName(String fileName) {
        int dot = fileName.indexOf('.');
        String stem = CanonicalNames.name(dot < 0 ? fileName : fileName.substring(0, dot));
        return IdentifierAlphabet.isName(stem) ? stem : OF_AN_UNUSABLE_STEM;
    }
}
