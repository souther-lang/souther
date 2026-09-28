package souther.compiler.cst.contract;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

/**
 * The syntax contract this repository publishes, read from where {@code souther-syntax} carries
 * it: {@code META-INF/souther/syntax}, copied there from the repository's {@code syntax/}.
 *
 * <p>Read from the artifact and not from the repository root, so a test that reads it is also
 * a test that the artifact carries it.
 */
final class SyntaxContract {

    private SyntaxContract() {}

    static final String ROOT = "/META-INF/souther/syntax/";

    static Grammar grammar() {
        return Grammar.read(text("grammar.ebnf"));
    }

    static String text(String relative) {
        try {
            return Files.readString(path(relative), StandardCharsets.UTF_8);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    static Path path(String relative) {
        URL found = SyntaxContract.class.getResource(ROOT + relative);
        if (found == null) {
            throw new IllegalStateException("souther-syntax does not carry " + ROOT + relative);
        }
        try {
            return Path.of(found.toURI());
        } catch (URISyntaxException e) {
            throw new IllegalStateException(e);
        }
    }
}
