package souther.cli.init;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * A Gradle build somebody else wrote: what it calls the project, and what makes it compile a model.
 *
 * <p>The plugin, and the Souther it compiles with written once, in its extension. The plugin adds the
 * runtime the generated code calls at that version, and a dependency a Gradle plugin adds is in the
 * metadata the project publishes — so unlike Maven there is no dependency for the script to declare.
 */
final class GradleBuild {

    private GradleBuild() {}

    /**
     * The block telling the plugin which Souther to compile with, which it has no default for.
     *
     * <p>The same text in Kotlin and Groovy but for the quotes, both assigning the extension's
     * property.
     */
    static String extension(String southerVersion, boolean kotlin) {
        String quote = kotlin ? "\"" : "'";
        return "souther {\n    southerVersion = " + quote + southerVersion + quote + "\n}\n";
    }

    /** How Kotlin and Groovy each write a plugin in a {@code plugins} block. */
    private static final String KOTLIN_LINE =
            "id(\"" + BuildPlugins.GRADLE_ID + "\") version \"" + BuildPlugins.GRADLE_VERSION + "\"";

    private static final String GROOVY_LINE =
            "id '" + BuildPlugins.GRADLE_ID + "' version '" + BuildPlugins.GRADLE_VERSION + "'";

    private static final Pattern GROUP = Pattern.compile(
            "(?m)^\\s*group\\s*(?:=|\\()?\\s*[\"']([^\"']+)[\"']");

    private static final Pattern ROOT_PROJECT_NAME = Pattern.compile(
            "(?m)^\\s*rootProject\\.name\\s*(?:=|\\()?\\s*[\"']([^\"']+)[\"']");

    /** Where a {@code plugins} block opens, at the top level of the script. */
    private static final Pattern PLUGINS = Pattern.compile("(?m)^\\s*plugins\\s*\\{");

    /** Whether the file is written in Kotlin, which is what its name says. */
    static boolean isKotlin(String fileName) {
        return fileName.endsWith(".kts");
    }

    /** What the script sets as the group, or null where it sets none. */
    static String groupOf(String script) {
        Matcher found = GROUP.matcher(script);
        return found.find() ? found.group(1) : null;
    }

    /** What the settings script calls the root project, or null where it does not name it. */
    static String rootProjectNameOf(String settings) {
        Matcher found = ROOT_PROJECT_NAME.matcher(settings);
        return found.find() ? found.group(1) : null;
    }

    /** What a script says about the plugin, which is not always "yes" or "no". */
    enum Applied {
        /**
         * It is requested in the `plugins` block and applied there, and the script sets the
         * extension's version in a form this reads ({@code tellsTheVersion}). Nothing to add.
         */
        ALREADY,
        /**
         * It is applied there, and the script sets no version in a form this reads.
         * Refused rather than added to. The plugin has no default and stops a project with a model
         * that names none, so leaving the script as it is would leave a project that does not build
         * once this command has written its model; and writing the block would override a version
         * given somewhere this does not read — a convention plugin, another script — with this
         * command's own.
         */
        UNTOLD,
        /** The script does not name it. A line goes into the `plugins` block. */
        NOT_YET,
        /**
         * It is named somewhere this does not read it as applying: outside the {@code plugins}
         * block, or inside it with {@code apply false}. Refused rather than added to — Gradle
         * refuses a second request for a plugin already requested, so the line this would write is
         * one that breaks the build, and answering "already" would leave a project that compiles no
         * Souther and was told it was set up.
         */
        SOMEWHERE_ELSE
    }

    /**
     * What this script says about the plugin.
     *
     * <p>Read off the {@code plugins} block with the comments taken out, rather than off the text.
     * A search of the text called `id("…") apply false` an applied plugin, and a comment naming it
     * one too. Where the block is, and where it closes, is read off the script with its strings
     * taken out as well; what the block requests is read off the strings, which is where a plugin
     * id is written.
     */
    static Applied appliedIn(String script, boolean kotlin) {
        Read read = Read.of(script, kotlin);
        Matcher found = PLUGINS.matcher(read.code());
        if (found.find()) {
            int close = closingBrace(read.code(), found.end() - 1);
            if (close >= 0) {
                String block = read.said().substring(found.end(), close);
                String rest = read.said().substring(0, found.start())
                        + read.said().substring(close + 1);
                if (requestsIt(block)) {
                    if (!applies(block)) {
                        return Applied.SOMEWHERE_ELSE;
                    }
                    // Yes only where every character was placed: a block read past something the
                    // walk could not place may be inside it.
                    return read.certain() && tellsTheVersion(read.code()) ? Applied.ALREADY
                            : Applied.UNTOLD;
                }
                return rest.contains(BuildPlugins.GRADLE_ID) ? Applied.SOMEWHERE_ELSE
                        : Applied.NOT_YET;
            }
        }
        return read.said().contains(BuildPlugins.GRADLE_ID) ? Applied.SOMEWHERE_ELSE
                : Applied.NOT_YET;
    }

    /** Whether the block asks for the plugin at all. */
    private static boolean requestsIt(String block) {
        return block.contains(BuildPlugins.GRADLE_ID);
    }

    /**
     * Whether the request in this block applies the plugin.
     *
     * <p>{@code apply false} asks for it on the class path without applying it, which is how a
     * root project names a version for its subprojects. The line is read on its own: another
     * plugin's {@code apply false} says nothing about this one.
     */
    private static boolean applies(String block) {
        for (String line : block.lines().toList()) {
            if (line.contains(BuildPlugins.GRADLE_ID)) {
                return !APPLY_FALSE.matcher(line).find();
            }
        }
        return false;
    }

    /** Where a plugin is asked for without being applied. */
    private static final Pattern APPLY_FALSE = Pattern.compile("apply\\s+false");

    /** A {@code souther} block opening at the start of a line. */
    private static final Pattern EXTENSION_BLOCK = Pattern.compile("(?m)^[ \\t]*souther\\s*\\{");

    /** The version set at the start of a line inside that block, by assignment or {@code set}. */
    private static final Pattern SETS_IN_THE_BLOCK =
            Pattern.compile("(?m)^[ \\t]*southerVersion\\s*(?:=|\\.set\\s*\\()");

    /** The version set at the start of a line through the extension's name. */
    private static final Pattern SETS_THROUGH_THE_EXTENSION =
            Pattern.compile("(?m)^[ \\t]*souther\\.southerVersion\\s*(?:=|\\.set\\s*\\()");

    /**
     * Whether the script sets the extension's version in one of the two forms this reads:
     * {@code southerVersion = …} or {@code southerVersion.set(…)} directly in a top-level
     * {@code souther} block, or {@code souther.southerVersion} assigned or set at the top level.
     *
     * <p>Only those, because a yes here is what lets a model be written into the project, and a yes
     * this could not stand behind leaves a project that stops at {@code compileSouther}. A name that
     * merely reads the same — a local {@code val southerVersion}, the words inside a string of any
     * kind, a block inside {@code subprojects} that configures some other project — sets nothing
     * here. A version given in a form this does not read is answered no, and the refusal says what
     * to write.
     *
     * @param code the script as {@code Read.code} has it, so that nothing a match lands on is inside
     *             a string or a comment
     */
    private static boolean tellsTheVersion(String code) {
        Matcher through = SETS_THROUGH_THE_EXTENSION.matcher(code);
        while (through.find()) {
            if (atTopLevel(code, through.start())) {
                return true;
            }
        }
        Matcher block = EXTENSION_BLOCK.matcher(code);
        while (block.find()) {
            if (!atTopLevel(code, block.start())) {
                continue;
            }
            int close = closingBrace(code, block.end() - 1);
            if (close < 0) {
                continue;
            }
            String inside = code.substring(block.end(), close);
            Matcher sets = SETS_IN_THE_BLOCK.matcher(inside);
            while (sets.find()) {
                if (atTopLevel(inside, sets.start())) {
                    return true;
                }
            }
        }
        return false;
    }

    /** Whether {@code index} is inside no brace of {@code code}, which holds no strings. */
    private static boolean atTopLevel(String code, int index) {
        int depth = 0;
        for (int i = 0; i < index; i++) {
            char c = code.charAt(i);
            if (c == '{') {
                depth++;
            } else if (c == '}') {
                depth--;
            }
        }
        return depth == 0;
    }

    /**
     * A script, read once, as the two texts the questions above are asked of.
     *
     * <p>Both are the script with some of it replaced by spaces, the line breaks kept, so an offset in
     * one is the same place in the other and in the script. {@code said} has its comments taken out:
     * it is what the build runs, strings and all, and a plugin id is a string. {@code code} has its
     * strings taken out as well: what is left is where a block opens and closes and where a line
     * begins, which no text inside a string is.
     *
     * <p>One reading for both, so that what is a string is decided in one place. A {@code souther}
     * block written inside a string, of whichever kind, is then not a block of the script's to any
     * question asked of it.
     */
    private record Read(String said, String code, boolean certain) {

        static Read of(String script, boolean kotlin) {
            Scan scan = new Scan(script, kotlin);
            scan.walk(0, false);
            return new Read(scan.said.toString(), scan.code.toString(), scan.certain);
        }
    }

    /**
     * The one walk over a script's comments and strings, in the script's own language.
     *
     * <p>Both languages have {@code "…"} and {@code """…"""}, where a template is code — which may
     * hold strings and braces of its own — and {@code '…'}, where it is not; Groovy has
     * {@code '''…'''} beside it, and {@code $/…/$}, which takes a template too. A backslash escapes
     * what follows in the single-quoted forms; a triple-quoted string ends at the first triple quote.
     * A Kotlin block comment holds block comments of its own, and a Groovy one ends at the first
     * {@code *}{@code /}.
     *
     * <p>{@code certain} is whether every character was read as one of those or as code. It is not
     * where the walk met something it cannot place: a string or a comment that does not close, or,
     * in Groovy, a {@code /} that is not a comment's, which opens a string or divides according to
     * what came before it — a question for a parser and not for this. What was read past such a
     * place is read anyway, and nothing that depends on it being right may be answered yes.
     */
    private static final class Scan {

        private final String script;
        private final boolean kotlin;
        private final StringBuilder said;
        private final StringBuilder code;
        private boolean certain = true;

        Scan(String script, boolean kotlin) {
            this.script = script;
            this.kotlin = kotlin;
            this.said = new StringBuilder(script);
            this.code = new StringBuilder(script);
        }

        /**
         * Code from {@code from}: to the end of the script, or, where {@code template}, to the brace
         * closing the template it is the code of, whose index is returned.
         */
        int walk(int from, boolean template) {
            int depth = 0;
            int i = from;
            while (i < script.length()) {
                if (script.startsWith("//", i)) {
                    int end = script.indexOf('\n', i);
                    end = end < 0 ? script.length() : end;
                    blank(said, i, end);
                    blank(code, i, end);
                    i = end;
                } else if (script.startsWith("/*", i)) {
                    int end = endOfComment(i);
                    blank(said, i, end);
                    blank(code, i, end);
                    i = end;
                } else if (script.startsWith("\"\"\"", i)) {
                    i = string(i, "\"\"\"", true, false);
                } else if (!kotlin && script.startsWith("'''", i)) {
                    i = string(i, "'''", false, false);
                } else if (!kotlin && script.startsWith("$/", i)) {
                    i = dollarSlashy(i);
                } else if (script.charAt(i) == '"') {
                    i = string(i, "\"", true, true);
                } else if (script.charAt(i) == '\'') {
                    i = string(i, "'", false, true);
                } else if (!kotlin && script.charAt(i) == '/') {
                    certain = false;
                    i++;
                } else {
                    char c = script.charAt(i);
                    if (c == '{') {
                        depth++;
                    } else if (c == '}') {
                        if (template && depth == 0) {
                            return i;
                        }
                        depth--;
                    }
                    i++;
                }
            }
            if (template) {
                certain = false;
            }
            return script.length();
        }

        /** The string opened at {@code open}, taken out of {@code code}; where it ends. */
        private int string(int open, String quote, boolean templates, boolean escapes) {
            int i = open + quote.length();
            while (i < script.length()) {
                if (escapes && script.charAt(i) == '\\') {
                    i += 2;
                } else if (templates && script.startsWith("${", i)) {
                    i = walk(i + 2, true) + 1;
                } else if (script.startsWith(quote, i)) {
                    int end = i + quote.length();
                    blank(code, open, end);
                    return end;
                } else {
                    i++;
                }
            }
            certain = false;
            blank(code, open, script.length());
            return script.length();
        }

        /**
         * Where the block comment opened at {@code open} ends: a Kotlin one after every comment
         * opened inside it has closed, a Groovy one at the first close.
         */
        private int endOfComment(int open) {
            int depth = 0;
            int i = open;
            while (i < script.length()) {
                if (script.startsWith("/*", i)) {
                    depth = kotlin || depth == 0 ? depth + 1 : depth;
                    i += 2;
                } else if (script.startsWith("*/", i)) {
                    i += 2;
                    if (--depth == 0) {
                        return i;
                    }
                } else {
                    i++;
                }
            }
            certain = false;
            return script.length();
        }

        /**
         * The Groovy string opened by {@code $/} at {@code open}, taken out of {@code code}; where it
         * ends. {@code $$} and {@code $/} inside it are escapes, and a template is code.
         */
        private int dollarSlashy(int open) {
            int i = open + 2;
            while (i < script.length()) {
                if (script.startsWith("$$", i) || script.startsWith("$/", i)) {
                    i += 2;
                } else if (script.startsWith("${", i)) {
                    i = walk(i + 2, true) + 1;
                } else if (script.startsWith("/$", i)) {
                    blank(code, open, i + 2);
                    return i + 2;
                } else {
                    i++;
                }
            }
            certain = false;
            blank(code, open, script.length());
            return script.length();
        }

        /** {@code from}..{@code to} of {@code text} as spaces, keeping the line breaks. */
        private void blank(StringBuilder text, int from, int to) {
            for (int i = from; i < Math.min(to, text.length()); i++) {
                if (text.charAt(i) != '\n') {
                    text.setCharAt(i, ' ');
                }
            }
        }
    }

    /**
     * The script with the plugin applied and told which Souther to compile with.
     *
     * <p>The extension goes at the end, after everything the script already says: a script that did
     * not apply the plugin has no {@code souther} block to add to.
     */
    static String withThePluginApplied(String script, boolean kotlin, String southerVersion) {
        String applied = withThePluginLine(script, kotlin);
        String separator = applied.endsWith("\n") ? "\n" : "\n\n";
        return applied + separator + extension(southerVersion, kotlin);
    }

    /**
     * The script with the plugin's line in its {@code plugins} block.
     *
     * <p>Into the {@code plugins} block where there is one, since a second block is an error Gradle
     * reports rather than a second list. A script with none gets one at the top, which is the only
     * place a {@code plugins} block may be.
     */
    private static String withThePluginLine(String script, boolean kotlin) {
        String line = kotlin ? KOTLIN_LINE : GROOVY_LINE;
        // Found in the script with its comments and strings taken out, and written into the script
        // itself. Blanking keeps every other character where it was, so an offset means the same
        // thing in both — and a `plugins {` that is there only because somebody commented an old
        // one out, or wrote one in a string, is not a block this writes into.
        String code = Read.of(script, kotlin).code();
        Matcher found = PLUGINS.matcher(code);
        if (!found.find()) {
            return "plugins {\n    " + line + "\n}\n\n" + script;
        }
        int close = closingBrace(code, found.end() - 1);
        if (close < 0) {
            return "plugins {\n    " + line + "\n}\n\n" + script;
        }
        int lineStart = script.lastIndexOf('\n', close - 1) + 1;
        String before = script.substring(lineStart, close);
        if (before.isBlank()) {
            return script.substring(0, lineStart) + before + "    " + line + "\n"
                    + script.substring(lineStart);
        }
        // A block written on one line — `plugins { java }`. The line goes before the brace rather
        // than before the line: written before the line it would land outside the block it was
        // meant to go inside, and a script whose plugin is applied at the top level does not
        // evaluate.
        String outer = before.substring(0, before.length() - before.stripLeading().length());
        return script.substring(0, close) + "\n" + outer + "    " + line + "\n" + outer
                + script.substring(close);
    }

    /**
     * Where the block opened at {@code open} closes, or -1 where nothing closes it.
     *
     * <p>Counted over {@code Read.code}, which has no strings or comments in it, so a {@code "}"}
     * inside a string is not read as the end of the block it sits in.
     */
    private static int closingBrace(String code, int open) {
        int depth = 0;
        for (int i = open; i < code.length(); i++) {
            char c = code.charAt(i);
            if (c == '{') {
                depth++;
            } else if (c == '}') {
                if (--depth == 0) {
                    return i;
                }
            }
        }
        return -1;
    }
}
