package souther.compiler.cst;

import souther.compiler.text.UnicodeProperty;

import java.util.Set;

/**
 * Which characters a name is made of. Souther's identifier is UAX #31's default form,
 * {@code XID_Start XID_Continue*}, against the Unicode version this file names.
 *
 * <p>The language owns this rather than borrowing it. Asking the running JDK — {@code
 * Character.isJavaIdentifierStart} — answers Java's question, which admits {@code $} and a leading
 * {@code _} because Java wanted them, and there is no version in the answer at all: the alphabet
 * would then move with whatever JDK a compile happens to run on, and a name is part of what a
 * compiled module promises, since a published helper's body travels in the jar as source and is
 * lexed again by the importing compiler.
 *
 * <p>The alphabet is the Unicode Character Database's own text, carried as a resource and read by
 * {@link UnicodeProperty}. It is not a table generated from that text, because a generated table is
 * a second copy of an answer and would have to be kept in step with the first; and it is not
 * derived from general categories either, because UAX #44 says to take {@code XID_Start} and
 * {@code XID_Continue} from {@code DerivedCoreProperties.txt} rather than to re-derive them. Moving
 * to a later Unicode version is replacing that one file, which is a change to what the language
 * reads and moves the boundary version with it.
 */
public final class IdentifierAlphabet {

    private IdentifierAlphabet() {}

    /** The property file, an excerpt of {@code DerivedCoreProperties.txt} holding its header and
     *  the two properties a name is spelled from. */
    private static final String RESOURCE = "identifier-alphabet.txt";

    private static final Set<String> WRITTEN = Set.of("XID_Start", "XID_Continue");

    private static final UnicodeProperty START = UnicodeProperty.read(IdentifierAlphabet.class,
            RESOURCE, "DerivedCoreProperties", WRITTEN, Set.of("XID_Start"));
    private static final UnicodeProperty CONTINUE = UnicodeProperty.read(IdentifierAlphabet.class,
            RESOURCE, "DerivedCoreProperties", WRITTEN, Set.of("XID_Continue"));

    /** The Unicode version the alphabet is read against, taken from the file's own first line
     *  ({@code # DerivedCoreProperties-17.0.0.txt}) so that the data and the version it is called
     *  cannot come apart. */
    public static String unicodeVersion() {
        return START.unicodeVersion();
    }

    /** Whether a name may begin with {@code codePoint}. */
    public static boolean isStart(int codePoint) {
        return START.has(codePoint);
    }

    /** Whether a name may carry on with {@code codePoint}. Every start is a continue, so this is
     *  the wider of the two. */
    public static boolean isContinue(int codePoint) {
        return CONTINUE.has(codePoint);
    }

    /**
     * Whether {@code written} is a name.
     *
     * <p>A name in a source file is a name because the scan read it as one. A name arriving from
     * outside a source file was read by nothing — the stem of a file the compiler was pointed at,
     * the name an embedding gives a source with no header — and is held to the alphabet here
     * instead, so that what a module may be called does not depend on which way it was named.
     */
    public static boolean isName(String written) {
        if (written == null || written.isEmpty() || !isStart(written.codePointAt(0))) {
            return false;
        }
        return written.codePoints().skip(1).allMatch(IdentifierAlphabet::isContinue);
    }

    /**
     * The characters a name may begin with, written as the body of a regular expression's character
     * class ({@code A-Za-z\x{00AA}…}).
     *
     * <p>A tool that colours source cannot call the two questions above — an editor grammar is a
     * regular expression and runs in an engine of its own — so what it can be given is the same
     * answer in the form it does read. Written from the ranges here rather than approximated by an
     * ASCII pattern or a Unicode property the engine may not have, so the editor and the compiler
     * admit one set of names and a test can hold them against each other.
     */
    public static String startClass() {
        return characterClass(START.ranges());
    }

    /** The characters a name may carry on with, as a character class body. */
    public static String continueClass() {
        return characterClass(CONTINUE.ranges());
    }

    private static String characterClass(int[] ranges) {
        StringBuilder out = new StringBuilder();
        for (int i = 0; i < ranges.length; i += 2) {
            out.append(escaped(ranges[i]));
            if (ranges[i + 1] != ranges[i]) {
                out.append('-').append(escaped(ranges[i + 1]));
            }
        }
        return out.toString();
    }

    /** A code point as a class writes it: the letters and digits as themselves, so that the common
     *  part of the class stays readable, and everything else by number. */
    private static String escaped(int codePoint) {
        boolean plain = (codePoint >= 'a' && codePoint <= 'z')
                || (codePoint >= 'A' && codePoint <= 'Z')
                || (codePoint >= '0' && codePoint <= '9');
        return plain ? String.valueOf((char) codePoint) : String.format("\\x{%04X}", codePoint);
    }
}
