package souther.compiler.io;

import java.io.IOException;
import java.nio.file.DirectoryIteratorException;
import java.nio.file.DirectoryStream;
import java.nio.file.Files;
import java.nio.file.Path;

/**
 * What a directory holds, one entry at a time, with a failure part way through said as the checked
 * {@link IOException} it is.
 *
 * <p>{@link Files#list} and {@link Files#walk} report a directory they could not read to the end by
 * throwing an unchecked exception out of the middle of a stream, past the {@code catch (IOException)}
 * written around them to say what such a directory means. Read here, the error reaches that catch.
 * A walk of a tree is {@link ConfinedTree#walk}, which says what it could not see.
 */
public final class Listing {

    private Listing() {
    }

    /** What is done with one entry of a directory. */
    @FunctionalInterface
    public interface Each {
        void accept(Path entry) throws IOException;
    }

    /** Hands each entry of {@code directory} to {@code each}, in the order the directory gives. */
    public static void each(Path directory, Each each) throws IOException {
        try (DirectoryStream<Path> held = Files.newDirectoryStream(directory)) {
            for (Path entry : held) {
                each.accept(entry);
            }
        } catch (DirectoryIteratorException e) {
            throw e.getCause();
        }
    }

    /** Whether {@code directory} holds anything. */
    public static boolean anyIn(Path directory) throws IOException {
        try (DirectoryStream<Path> held = Files.newDirectoryStream(directory)) {
            return held.iterator().hasNext();
        } catch (DirectoryIteratorException e) {
            throw e.getCause();
        }
    }
}
