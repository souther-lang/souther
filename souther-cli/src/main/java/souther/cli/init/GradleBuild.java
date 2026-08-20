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

    /** Whether the script already applies the Souther plugin. */
    static boolean declaresThePlugin(String script) {
        return script.contains(BuildPlugins.GRADLE_ID);
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
        String indent = script.substring(lineStart, close);
        String inner = indent.isBlank() ? indent + "    " : "    ";
        return script.substring(0, lineStart) + inner + line + "\n" + script.substring(lineStart);
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
