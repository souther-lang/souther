package souther.compiler.meta;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.IOException;
import java.io.OutputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.zip.ZipEntry;
import java.util.zip.ZipOutputStream;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A class path entry is read the same way whether the project it belongs to was built into a
 * directory or packaged into a jar, and an entry that has no copy of the class contributes nothing
 * rather than ending the search.
 */
class ModulePathTest {

    private static final byte[] CLASS = {(byte) 0xCA, (byte) 0xFE, (byte) 0xBA, (byte) 0xBE, 1};

    private static Path classesDir(Path dir, byte[] bytes) throws IOException {
        Path file = dir.resolve("shared/billing/Amount.class");
        Files.createDirectories(file.getParent());
        Files.write(file, bytes);
        return dir;
    }

    private static Path jar(Path file, byte[] bytes) throws IOException {
        try (OutputStream out = Files.newOutputStream(file);
                ZipOutputStream zip = new ZipOutputStream(out)) {
            zip.putNextEntry(new ZipEntry("shared/billing/Amount.class"));
            zip.write(bytes);
            zip.closeEntry();
        }
        return file;
    }

    @Test
    void aClassComesOutOfADirectoryEntry(@TempDir Path dir) throws IOException {
        ModulePath path = ModulePath.ofClassPath(List.of(classesDir(dir, CLASS)));

        assertArrayEquals(CLASS, path.bytes("shared.billing.Amount"));
        assertNull(path.bytes("shared.billing.Missing"));
    }

    @Test
    void aClassComesOutOfAJarEntry(@TempDir Path dir) throws IOException {
        ModulePath path = ModulePath.ofClassPath(List.of(jar(dir.resolve("billing.jar"), CLASS)));

        assertArrayEquals(CLASS, path.bytes("shared.billing.Amount"));
        assertNull(path.bytes("shared.billing.Missing"));
    }

    @Test
    void theEntriesAreReadInOrderAndOnesWithoutTheClassAreSkipped(@TempDir Path dir)
            throws IOException {
        byte[] second = {(byte) 0xCA, (byte) 0xFE, (byte) 0xBA, (byte) 0xBE, 2};
        Path empty = Files.createDirectories(dir.resolve("empty"));
        Path absent = dir.resolve("never-built");
        ModulePath path = ModulePath.ofClassPath(List.of(
                empty,
                absent,
                classesDir(Files.createDirectories(dir.resolve("first")), CLASS),
                jar(dir.resolve("second.jar"), second)));

        assertArrayEquals(CLASS, path.bytes("shared.billing.Amount"));
    }

    @Test
    void nothingStaysOpenSoThePathCanBeBuiltPerCompile(@TempDir Path dir) throws IOException {
        Path jar = jar(dir.resolve("billing.jar"), CLASS);
        for (int i = 0; i < 200; i++) {
            assertArrayEquals(CLASS, ModulePath.ofClassPath(List.of(jar)).bytes("shared.billing.Amount"));
        }
        Files.delete(jar);   // a handle left open would keep this from being replaceable on Windows
    }

    @Test
    void twoPathsOverTheSameEntriesAreTheSamePath(@TempDir Path dir) throws IOException {
        // A language server rebuilds its path on every request and keeps one compilation between
        // edits. If a path were only ever equal to itself, that compilation would be thrown away and
        // started again on every keystroke, and nothing would say so.
        Path classes = classesDir(dir, CLASS);
        assertEquals(ModulePath.ofClassPath(List.of(classes)),
                ModulePath.ofClassPath(List.of(classes)));
        assertNotEquals(ModulePath.ofClassPath(List.of(classes)),
                ModulePath.ofClassPath(List.of()));
    }
}
