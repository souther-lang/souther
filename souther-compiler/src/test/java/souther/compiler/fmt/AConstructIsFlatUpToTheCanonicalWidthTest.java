package souther.compiler.fmt;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a construct that can break decides to. {@link TheCanonicalFormBreaksAtTheEnclosingStructureTest}
 * writes each construct far over the width and pins the multi-line form it takes; this writes the same
 * kinds of construct at the width and one column either side of it, so that the column the decision
 * turns on is stated rather than left to a fixture that happens to be long enough.
 *
 * <p>Each row of {@link #sites} is one construct whose layout the width decides, written with a slot
 * that pads it to any column. Every row is padded to the same three widths, and the answer is the same
 * for all of them: a construct whose line would be {@value #WIDTH} columns or fewer is written on one
 * line, and one column more breaks it. A construct with no row here is one whose conditional break has
 * a fixture over the width and none at it.
 */
class AConstructIsFlatUpToTheCanonicalWidthTest {

    /** The canonical width, written here rather than read from {@link Formatter} — the boundary is
     * what these fixtures state, so a formatter that moved it has to fail them. */
    private static final int WIDTH = 100;

    /**
     * A construct written on one line, with {@code %s} where padding goes. The padding lengthens one
     * identifier, string or name, so a wider fixture is the same construct rather than a different
     * one, and the only thing that moves between the three widths is the column.
     *
     * @param deciding the substring on the line whose width decides this construct's layout — the
     *     line the padding lengthens
     */
    record Site(String name, String template, String deciding) {
        @Override
        public String toString() {
            return name;
        }
    }

    static Stream<Site> sites() {
        return Stream.of(
                new Site("exposing list",
                        """
                        module fmtprobe exposing ( alphaName%s, betaName )
                        """,
                        "exposing"),

                new Site("import name list",
                        """
                        module fmtprobe exposing ( f )

                        import some.place ( alphaName%s, betaName )
                        """,
                        "import"),

                new Site("definition parameter list",
                        """
                        module fmtprobe exposing ( f )

                        let f (alphaParam%s: Int, betaParam: Int): Int =
                            someName
                        """,
                        "let f ("),

                new Site("behavior parameter list",
                        """
                        module fmtprobe exposing ( b )

                        behavior b : (alphaParam%s: Int, betaParam: Int) -> R
                        """,
                        "behavior b : ("),

                new Site("definition body",
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int = someFunctionName%s(alpha)
                        """,
                        "= someFunctionName"),

                new Site("intrinsic body",
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int = intrinsic "int.someName%s"
                        """,
                        "intrinsic"),

                new Site("behavior pipeline",
                        """
                        module fmtprobe exposing ( b )

                        behavior b = alphaStage%s >-> betaStage
                        """,
                        ">->"),

                new Site("constructs clause",
                        """
                        module fmtprobe exposing ( b )

                        behavior b : (a: A) -> R
                            constructs AlphaMade%s, BetaMade
                        """,
                        "constructs"),

                new Site("return type union",
                        """
                        module fmtprobe exposing ( b )

                        behavior b : (a: A) -> AlphaOut%s | BetaOut
                        """,
                        "-> AlphaOut"),

                new Site("sum cases",
                        """
                        module fmtprobe exposing ( V )

                        data V = AlphaCase%s | BetaCase
                        """,
                        "data V ="),

                new Site("example row",
                        """
                        module fmtprobe exposing ( j )

                        example j
                            | "someDescription%s" : (Alpha(1)) -> Gamma
                        """,
                        "someDescription"),

                // The row is written over several lines already, so the bindings are the construct
                // whose own width is being asked about: a row short enough to fit on one line breaks
                // at its `:` and `->` before its bindings are ever measured.
                new Site("example with bindings",
                        """
                        module fmtprobe exposing ( j )

                        example j
                            | "a description long enough that the row is written over more than one line"
                                : (Alpha(1)) with betaBind%s = two, gammaBind = three
                                -> Gamma
                        """,
                        "with betaBind"),

                new Site("call arguments",
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int =
                            someFunction(alphaArgument%s, betaArgument)
                        """,
                        "someFunction("),

                new Site("list literal",
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int =
                            [alphaElement%s, betaElement]
                        """,
                        "[alphaElement"),

                new Site("record literal",
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int =
                            Receipt { alphaField%s = one, betaField = two }
                        """,
                        "Receipt {"),

                new Site("tuple expression",
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int =
                            (alphaElement%s, betaElement, gammaElement)
                        """,
                        "(alphaElement"),

                new Site("list comprehension",
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int =
                            [alphaElement%s | betaGuard, gammaGuard]
                        """,
                        "| betaGuard"),

                new Site("if expression",
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int =
                            if alphaCond%s then betaThen else gammaElse
                        """,
                        "if alphaCond"),

                new Site("operator chain",
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int =
                            alphaTerm%s + betaTerm + gammaTerm
                        """,
                        "+ betaTerm"));
    }

    /** {@code site} written so that its deciding line is exactly {@code columns} wide. */
    private static String at(Site site, int columns) {
        int unpadded = decidingLine(site, site.template().formatted("")).length();
        assertTrue(columns >= unpadded,
                site.name() + " is already " + unpadded + " columns with no padding");
        return site.template().formatted("x".repeat(columns - unpadded));
    }

    /** The one line of {@code text} the site's layout decision turns on. */
    private static String decidingLine(Site site, String text) {
        List<String> found = new ArrayList<>();
        for (String line : text.split("\n", -1)) {
            if (line.contains(site.deciding())) {
                found.add(line);
            }
        }
        assertEquals(1, found.size(),
                site.name() + ": `" + site.deciding() + "` is on " + found.size() + " lines of:\n" + text);
        return found.get(0);
    }

    private static int decidingLineIndex(Site site, String text) {
        String[] lines = text.split("\n", -1);
        for (int i = 0; i < lines.length; i++) {
            if (lines[i].contains(site.deciding())) {
                return i;
            }
        }
        throw new AssertionError(site.name() + ": nothing holds `" + site.deciding() + "`");
    }

    /**
     * The padding lands the deciding line on the column the row is about, and leaves every other line
     * under it. A fixture a column off asks about a column beside the boundary rather than the
     * boundary, and would pass either answer; one whose widest line is somewhere else asks about that
     * line instead.
     */
    @ParameterizedTest(name = "{0}")
    @MethodSource("sites")
    void theFixtureIsAsWideAsItClaims(Site site) {
        for (int columns : new int[] {WIDTH - 1, WIDTH, WIDTH + 1}) {
            String source = at(site, columns);
            assertEquals(columns, decidingLine(site, source).length(),
                    site.name() + " at " + columns + " columns:\n" + source);
            for (String line : source.split("\n", -1)) {
                assertTrue(line.length() <= columns,
                        site.name() + ": another line is " + line.length() + " columns wide, so the"
                                + " width decides that one and not the construct: " + line);
            }
        }
    }

    /** At the width, and a column under it, the construct stays on its line. Written already in its
     * canonical form, so this says the formatter leaves it there rather than what it would move it to. */
    @ParameterizedTest(name = "{0}")
    @MethodSource("sites")
    void aConstructWhoseLineFitsTheWidthKeepsIt(Site site) {
        assertEquals(at(site, WIDTH - 1), Formatter.format(at(site, WIDTH - 1)));
        assertEquals(at(site, WIDTH), Formatter.format(at(site, WIDTH)));
    }

    /** One column more and it breaks. */
    @ParameterizedTest(name = "{0}")
    @MethodSource("sites")
    void oneColumnOverTheWidthBreaksTheConstruct(Site site) {
        String source = at(site, WIDTH + 1);
        String formatted = Formatter.format(source);
        assertNotEquals(source, formatted,
                site.name() + " stayed on a line of " + (WIDTH + 1) + " columns");
        assertEquals(formatted, Formatter.format(formatted),
                site.name() + ": the broken form is not a fixed point");
    }

    /**
     * The construct broke where its layout had a break to take, and nothing before that point was
     * written differently: the first line of the broken form is what the flat line held up to there.
     * Without this, a formatter that answered the width by rewriting the construct — or by breaking
     * some other construct on the line — would pass {@link #oneColumnOverTheWidthBreaksTheConstruct}.
     */
    @ParameterizedTest(name = "{0}")
    @MethodSource("sites")
    void whatIsWrittenBeforeTheBreakIsWhatTheFlatLineHeld(Site site) {
        String source = at(site, WIDTH + 1);
        String formatted = Formatter.format(source);
        int index = decidingLineIndex(site, source);
        String flat = source.split("\n", -1)[index];
        String opened = formatted.split("\n", -1)[index];
        assertTrue(opened.length() < flat.length() && flat.startsWith(opened),
                site.name() + ": the line the break opens is `" + opened + "`, which is not what the"
                        + " flat line `" + flat + "` held up to there");
    }

    /**
     * One construct inside another, at the three combinations of the two being written flat or broken.
     * The padding is chosen so that each row sits at a boundary: the widest padding one of the three
     * layouts takes, and one column past it.
     *
     * <p>The fourth combination is not a layout: a construct written over several lines leaves every
     * construct holding it written over several lines too, whatever the width, so an inner break is
     * never taken under a flat outer one.
     */
    record Nesting(String name, int pad, String expected) {
        @Override
        public String toString() {
            return name + " (pad " + pad + ")";
        }
    }

    private static String nestedSource(int pad) {
        return """
                module fmtprobe exposing ( f )

                let f (a: Int): Int = outerCall(innerCall(alphaArg%s, betaArg), gammaArg)
                """.formatted("x".repeat(pad));
    }

    static Stream<Nesting> nestings() {
        return Stream.of(
                new Nesting("both flat", 29,
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int = outerCall(innerCall(alphaArg%s, betaArg), gammaArg)
                        """),

                new Nesting("both flat, under the definition body", 30,
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int =
                            outerCall(innerCall(alphaArg%s, betaArg), gammaArg)
                        """),

                new Nesting("both flat, at the width", 47,
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int =
                            outerCall(innerCall(alphaArg%s, betaArg), gammaArg)
                        """),

                new Nesting("outer broken, inner flat", 48,
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int =
                            outerCall(
                                innerCall(alphaArg%s, betaArg),
                                gammaArg
                            )
                        """),

                new Nesting("outer broken, inner flat at the width", 63,
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int =
                            outerCall(
                                innerCall(alphaArg%s, betaArg),
                                gammaArg
                            )
                        """),

                new Nesting("both broken", 64,
                        """
                        module fmtprobe exposing ( f )

                        let f (a: Int): Int =
                            outerCall(
                                innerCall(
                                    alphaArg%s,
                                    betaArg
                                ),
                                gammaArg
                            )
                        """));
    }

    @ParameterizedTest(name = "{0}")
    @MethodSource("nestings")
    void nestedConstructsBreakFromTheOutsideIn(Nesting nesting) {
        String expected = nesting.expected().formatted("x".repeat(nesting.pad()));
        assertEquals(expected, Formatter.format(nestedSource(nesting.pad())));
        assertEquals(expected, Formatter.format(expected),
                nesting.name() + ": the canonical form is not a fixed point");
    }

    /**
     * Each of these three layouts is the widest its shape reaches, or the first column past one that
     * is: the row at a boundary has a line of exactly the width, and the row a column past it has the
     * shape the next row up. Rows chosen a few columns away from the boundary would show the same
     * three combinations and say nothing about where any of them ends.
     */
    @ParameterizedTest(name = "{0}")
    @MethodSource("nestings")
    void eachNestingSitsAtTheBoundaryItIsAbout(Nesting nesting) {
        String expected = nesting.expected().formatted("x".repeat(nesting.pad()));
        int widest = 0;
        for (String line : expected.split("\n", -1)) {
            widest = Math.max(widest, line.length());
        }
        boolean atTheWidth = widest == WIDTH;
        boolean oneColumnPast = Formatter.format(nestedSource(nesting.pad() - 1))
                .equals(nesting.expected().formatted("x".repeat(nesting.pad() - 1)));
        assertTrue(atTheWidth || !oneColumnPast,
                nesting.name() + ": the widest line is " + widest + " columns and one column less"
                        + " takes the same shape, so this row is not at a boundary");
    }
}
