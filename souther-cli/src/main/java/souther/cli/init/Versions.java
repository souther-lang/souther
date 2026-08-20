package souther.cli.init;

import java.io.IOException;
import java.io.InputStream;
import java.io.UncheckedIOException;
import java.util.Properties;

/**
 * The versions a project this command writes declares, taken from the build that produced this
 * compiler.
 *
 * <p>Written in at build time rather than in the code here. A generated build file pins the world as
 * it was when this compiler was released, and there is no getting away from that — what there is to
 * avoid is pinning it twice. JUnit and Surefire are what this build runs its own tests with, and
 * they are what it hands a project to run its own. A number repeated here would be a second
 * statement of each, and the day one of them moved the other would go on being handed to readers.
 *
 * <p>Only what a project cannot be given any other way is here. The Souther version comes from the
 * manifest of the running compiler, and the build plugins are released on their own series, so
 * neither is this build's to state.
 */
final class Versions {

    private Versions() {}

    private static final String RESOURCE = "/souther/cli/init/versions.properties";

    private static final Properties STATED = read();

    /** The JUnit a generated project's test is written against. */
    static String junit() {
        return stated("junit.version");
    }

    /** The Surefire a generated Maven project runs that test with. */
    static String surefire() {
        return stated("surefire.version");
    }

    private static Properties read() {
        Properties properties = new Properties();
        try (InputStream in = Versions.class.getResourceAsStream(RESOURCE)) {
            if (in == null) {
                throw new IllegalStateException("this build has no " + RESOURCE);
            }
            properties.load(in);
        } catch (IOException e) {
            throw new UncheckedIOException("unreadable " + RESOURCE, e);
        }
        return properties;
    }

    /**
     * What the file states under this name, refusing a build that left it unfilled.
     *
     * <p>A resource copied without filtering carries the property's own spelling, and a version of
     * {@code ${junit.version}} reaches a reader as a build file that resolves nothing. Said here
     * rather than left to their build to report.
     */
    private static String stated(String name) {
        String version = STATED.getProperty(name, "");
        if (version.isEmpty() || version.startsWith("${")) {
            throw new IllegalStateException(RESOURCE + " states no " + name
                    + ": this compiler was built without filtering it");
        }
        return version;
    }
}
