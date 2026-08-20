package souther.cli.init;

import souther.compiler.cst.CstLexer;
import souther.compiler.cst.IdentifierAlphabet;

/**
 * What a build calls a project — its {@code groupId} and {@code artifactId} — and the module name
 * that follows from it.
 *
 * <p>Asked for rather than guessed at. A directory name is not a group and a git remote is not one
 * either, so a project being created has to be given both; a project that already has a build has
 * written them down, and they are read from there.
 *
 * <p>The module name is derived and not a fourth thing to keep in step. A module header is the Java
 * package the generated classes go into, so a project whose coordinate and module disagree has two
 * names for one thing — which is the drift {@code init} exists to remove. What the derivation has to
 * do is write what Maven allows in a coordinate and a name cannot carry: {@code org.souther-lang} is
 * a group of this project's own, and {@code org.souther-lang.souther-cli} is not a module name.
 */
public record Coordinate(String groupId, String artifactId) {

    /** What a coordinate is written as, where a refusal has to name the form. */
    static final String FORM = "<groupId>:<artifactId>";

    /**
     * The coordinate this text writes, or null where it does not write one.
     *
     * <p>Both halves are required and neither may be blank: {@code :hello} and {@code com.example:}
     * are lines that left one out, and a coordinate with a part missing is not a coordinate with a
     * default.
     */
    static Coordinate written(String text) {
        int colon = text.indexOf(':');
        if (colon < 0 || text.indexOf(':', colon + 1) >= 0) {
            return null;
        }
        String group = text.substring(0, colon).trim();
        String artifact = text.substring(colon + 1).trim();
        return group.isEmpty() || artifact.isEmpty() ? null : new Coordinate(group, artifact);
    }

    /** The coordinate as a build writes it. */
    @Override
    public String toString() {
        return groupId + ":" + artifactId;
    }

    /**
     * The module name this coordinate derives, or null where it derives none.
     *
     * <p>A hyphen becomes an underscore, which is what turns {@code com.acme:billing-service} into
     * {@code com.acme.billing_service}. That is what the neighbours do with the same problem —
     * {@code cargo new --lib crate-demo} builds {@code crate_demo}, {@code uv init --lib py-demo}
     * writes {@code src/py_demo}, and JLS 6.1 says to replace a hyphen in a package name with an
     * underscore — and it keeps the two spellings a reader has to match one substitution apart
     * rather than an unrecoverable one.
     *
     * <p>What comes out is held against the language: a segment that is not a name, or is a word the
     * language has taken, is not one this can put in a module header, and the author is asked for
     * {@code --module} rather than handed a file that does not parse.
     */
    public String moduleName() {
        StringBuilder name = new StringBuilder();
        for (String segment : (groupId + "." + artifactId).split("\\.")) {
            String written = segment.replace('-', '_');
            if (!isAName(written)) {
                return null;
            }
            name.append(name.isEmpty() ? "" : ".").append(written);
        }
        return name.toString();
    }

    /**
     * Whether this is a name the language reads as one.
     *
     * <p>Both halves are asked of what decides them. The alphabet is the one a source is scanned
     * against, which is not Java's: {@code billing_service} is a name and {@code _x} is not, since
     * an underscore carries a name on and begins none. The keywords come from the lexer that
     * reserves them. Written out here instead, either would go on admitting what the compiler had
     * stopped admitting, and what a reader would get is a generated file that does not parse.
     */
    static boolean isAName(String segment) {
        return IdentifierAlphabet.isName(segment) && !CstLexer.keywords().contains(segment);
    }

    /** Whether every segment of this dotted name is one the language reads as a name. */
    static boolean isAModuleName(String written) {
        if (written.isEmpty() || written.startsWith(".") || written.endsWith(".")) {
            return false;
        }
        for (String segment : written.split("\\.", -1)) {
            if (!isAName(segment)) {
                return false;
            }
        }
        return true;
    }
}
