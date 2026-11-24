package souther.compiler.core;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An operation that answers a list of what a set or a map holds says its list has no order.
 *
 * <p>Whether a fold walks its list in an order the model names is read off the kernels the list is
 * made of, so a kernel added to the library that lists a collection and is not marked leaves every
 * fold over it asked for rows that turn on the order the host happens to keep. Held against the
 * library's own declarations, so the kernel that is added is the one this fails for.
 */
class EveryKernelThatListsASetOrAMapSaysItHasNoOrderTest {

    private static final Pattern LISTS = Pattern.compile(
            "^let (\\w+) \\([^)]*\\): List<.*> = intrinsic \"([\\w.]+)\"$");

    @Test
    void everyIntrinsicOfASetOrAMapThatAnswersAListIsMarked() {
        List<String> unmarked = new ArrayList<>();
        int listing = 0;
        for (String module : List.of("set", "map")) {
            for (String line : source(module).split("\n")) {
                Matcher found = LISTS.matcher(line.strip());
                if (!found.matches()) {
                    continue;
                }
                listing++;
                Kernel kernel = kernelOf(found.group(2));
                if (!kernel.listsInNoOrder()) {
                    unmarked.add(kernel + " (" + found.group(1) + " of " + module + ")");
                }
            }
        }
        assertEquals(List.of(), unmarked, "the lists these answer have an order the model names");
        assertEquals(4, listing, "the declarations were read: Set.toList and Map's three");
    }

    @Test
    void noKernelOutsideASetOrAMapIsMarked() {
        for (Kernel each : Kernel.values()) {
            if (each.listsInNoOrder()) {
                assertTrue(each.key().startsWith("set.") || each.key().startsWith("map."),
                        () -> each + " lists what is neither a set nor a map");
            }
        }
    }

    private static Kernel kernelOf(String key) {
        for (Kernel each : Kernel.values()) {
            if (each.key().equals(key)) {
                return each;
            }
        }
        throw new AssertionError("the library declares `" + key + "` and no kernel is named so");
    }

    private static String source(String module) {
        try (InputStream in = Kernel.class.getResourceAsStream("/souther/" + module + ".sou")) {
            assertNotNull(in, "the library holds " + module);
            return new String(in.readAllBytes(), StandardCharsets.UTF_8);
        } catch (IOException e) {
            throw new AssertionError(e);
        }
    }
}
