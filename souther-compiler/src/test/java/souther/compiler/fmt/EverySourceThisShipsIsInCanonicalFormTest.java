package souther.compiler.fmt;

import org.junit.jupiter.api.Test;
import souther.compiler.Reserved;

import java.io.IOException;
import java.io.InputStream;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The standard library is written in the form {@code souther fmt} writes.
 *
 * <p>It is the only Souther source this project ships, and {@code souther api --source} prints it
 * to a reader. Source the product hands out and its own formatter rejects is the product
 * contradicting itself, and it is also the whole of the evidence for the canonical form: a form
 * nothing is required to be in is one that can drift from every document describing it with nothing
 * to say which of the two moved. This is what requires it of something.
 *
 * <p>The modules are read through {@link Reserved#MODULES} and the same resource path the prelude
 * loads them by, so a module added there is covered by this without being added here. A list
 * written out again is a second answer to which modules there are, and the one that goes stale is
 * the copy.
 *
 * <p>What is checked is the text, not that the formatter is happy: formatting is compared against
 * the file as it is on disk. Asking the formatter whether it would change anything is asking the
 * thing under test.
 */
class EverySourceThisShipsIsInCanonicalFormTest {

    @Test
    void everyStandardLibraryModuleIsWrittenAsTheFormatterWritesIt() {
        List<String> differ = new ArrayList<>();
        for (Reserved.StdlibModule module : Reserved.MODULES) {
            String resource = "/" + module.moduleName().replace('.', '/') + ".sou";
            String source = read(resource);
            if (!source.equals(Formatter.format(source))) {
                differ.add(resource);
            }
        }
        assertEquals(List.of(), differ,
                differ.size() + " of " + Reserved.MODULES.size() + " shipped modules are not in"
                        + " canonical form; run `souther fmt -w` over"
                        + " souther-compiler/src/main/resources/souther/");
    }

    /** The sweep covers every module the prelude loads, so a run that found nothing to check would
     *  pass the assertion above without having asked anything. */
    @Test
    void thereAreModulesToCheck() {
        assertTrue(Reserved.MODULES.size() >= 10,
                "only " + Reserved.MODULES.size() + " modules were swept");
    }

    private static String read(String resource) {
        try (InputStream in = EverySourceThisShipsIsInCanonicalFormTest.class
                .getResourceAsStream(resource)) {
            if (in == null) {
                throw new IllegalStateException("the prelude resource " + resource + " is missing");
            }
            return new String(in.readAllBytes(), StandardCharsets.UTF_8);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }
}
