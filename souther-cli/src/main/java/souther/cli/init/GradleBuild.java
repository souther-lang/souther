package souther.cli.init;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * A Gradle build somebody else wrote: what it calls the project, and the one line that makes it
 * compile a model.
 *
 * <p>One line and no version to keep in step. The plugin adds the runtime the generated code calls,
 * at the version of the Souther it compiles with, and a dependency a Gradle plugin adds is in the
 * metadata the project publishes — so unlike Maven there is nothing for the build script to declare
 * beside the plugin itself.
 */
final class GradleBuild {

    private GradleBuild() {}

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
        /** It is requested in the `plugins` block and applied there. Nothing to add. */
        ALREADY,
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
     * one too.
     */
    static Applied appliedIn(String script) {
        String said = withoutComments(script);
        Matcher found = PLUGINS.matcher(said);
        if (found.find()) {
            int close = closingBrace(said, found.end() - 1);
            if (close >= 0) {
                String block = said.substring(found.end(), close);
                String rest = said.substring(0, found.start()) + said.substring(close + 1);
                if (requestsIt(block)) {
                    return applies(block) ? Applied.ALREADY : Applied.SOMEWHERE_ELSE;
                }
                return rest.contains(BuildPlugins.GRADLE_ID) ? Applied.SOMEWHERE_ELSE
                        : Applied.NOT_YET;
            }
        }
        return said.contains(BuildPlugins.GRADLE_ID) ? Applied.SOMEWHERE_ELSE : Applied.NOT_YET;
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
        for (String line : block.split("\n")) {
            if (line.contains(BuildPlugins.GRADLE_ID)) {
                return !APPLY_FALSE.matcher(line).find();
            }
        }
        return false;
    }

    /** Where a plugin is asked for without being applied. */
    private static final Pattern APPLY_FALSE = Pattern.compile("apply\\s+false");

    /**
     * The script with its comments taken out, so that what is read is what the build runs.
     *
     * <p>Replaced with spaces rather than removed, so nothing that was on two lines becomes one.
     */
    private static String withoutComments(String script) {
        StringBuilder out = new StringBuilder(script.length());
        for (int i = 0; i < script.length(); i++) {
            char c = script.charAt(i);
            if (c == '/' && i + 1 < script.length() && script.charAt(i + 1) == '/') {
                int end = script.indexOf('\n', i);
                end = end < 0 ? script.length() : end;
                blank(out, script, i, end);
                i = end - 1;
            } else if (c == '/' && i + 1 < script.length() && script.charAt(i + 1) == '*') {
                int end = script.indexOf("*/", i);
                end = end < 0 ? script.length() : end + 2;
                blank(out, script, i, end);
                i = end - 1;
            } else if (c == '"' || c == '\'') {
                int end = endOfString(script, i);
                out.append(script, i, Math.min(end + 1, script.length()));
                i = end;
            } else {
                out.append(c);
            }
        }
        return out.toString();
    }

    /** {@code from}..{@code to} as spaces, keeping the line breaks that were in it. */
    private static void blank(StringBuilder out, String script, int from, int to) {
        for (int i = from; i < to; i++) {
            out.append(script.charAt(i) == '\n' ? '\n' : ' ');
        }
    }

    /**
     * The script with the plugin applied.
     *
     * <p>Into the {@code plugins} block where there is one, since a second block is an error Gradle
     * reports rather than a second list. A script with none gets one at the top, which is the only
     * place a {@code plugins} block may be.
     */
    static String withThePluginApplied(String script, boolean kotlin) {
        String line = kotlin ? KOTLIN_LINE : GROOVY_LINE;
        Matcher found = PLUGINS.matcher(script);
        if (!found.find()) {
            return "plugins {\n    " + line + "\n}\n\n" + script;
        }
        int close = closingBrace(script, found.end() - 1);
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
     * <p>Braces are counted outside strings and comments, so a {@code "}"} inside a string is not
     * read as the end of the block it sits in.
     */
    private static int closingBrace(String script, int open) {
        int depth = 0;
        for (int i = open; i < script.length(); i++) {
            char c = script.charAt(i);
            if (c == '/' && i + 1 < script.length() && script.charAt(i + 1) == '/') {
                int end = script.indexOf('\n', i);
                i = end < 0 ? script.length() : end;
            } else if (c == '/' && i + 1 < script.length() && script.charAt(i + 1) == '*') {
                int end = script.indexOf("*/", i);
                i = end < 0 ? script.length() : end + 1;
            } else if (c == '"' || c == '\'') {
                i = endOfString(script, i);
            } else if (c == '{') {
                depth++;
            } else if (c == '}') {
                if (--depth == 0) {
                    return i;
                }
            }
        }
        return -1;
    }

    /** Where the string opened at {@code quote} ends, taking a backslash as escaping what follows. */
    private static int endOfString(String script, int quote) {
        char q = script.charAt(quote);
        for (int i = quote + 1; i < script.length(); i++) {
            char c = script.charAt(i);
            if (c == '\\') {
                i++;
            } else if (c == q) {
                return i;
            }
        }
        return script.length();
    }
}
