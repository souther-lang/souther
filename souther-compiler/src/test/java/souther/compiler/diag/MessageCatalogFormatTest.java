package souther.compiler.diag;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.Properties;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Every message in the catalog is a {@link java.text.MessageFormat} pattern, where a lone {@code '}
 * opens a quoted run and {@code ''} is the apostrophe itself. A message that writes {@code a data's}
 * therefore quotes the whole rest of itself: the apostrophe disappears and every {@code {n}} after it
 * renders literally, as the placeholder rather than the value.
 *
 * <p>Nothing caught that, because a message is only read when its diagnostic fires and the result is
 * prose nobody diffs. This renders each one with stand-in arguments and fails on any placeholder that
 * survived.
 */
class MessageCatalogFormatTest {

    private static final Pattern PLACEHOLDER = Pattern.compile("\\{(\\d)}");

    @Test
    void everyEnglishMessageSubstitutesAllOfItsArguments() throws IOException {
        assertEquals(List.of(), unsubstituted("/souther/compiler/diag/messages.properties", Locale.ENGLISH));
    }

    @Test
    void everyJapaneseMessageSubstitutesAllOfItsArguments() throws IOException {
        assertEquals(List.of(),
                unsubstituted("/souther/compiler/diag/messages_ja.properties", Locale.JAPANESE));
    }

    /** The keys whose rendering still contains a {@code {n}} — one per line, so a failure names them
     *  all rather than the first. */
    private static List<String> unsubstituted(String resource, Locale locale) throws IOException {
        Properties catalog = new Properties();
        try (InputStream in = MessageCatalogFormatTest.class.getResourceAsStream(resource)) {
            catalog.load(new InputStreamReader(in, StandardCharsets.UTF_8));
        }
        List<String> broken = new ArrayList<>();
        for (String key : catalog.stringPropertyNames()) {
            String template = catalog.getProperty(key);
            int arity = arityOf(template);
            if (arity == 0) {
                continue;
            }
            Object[] args = new Object[arity];
            for (int i = 0; i < arity; i++) {
                args[i] = "<arg" + i + ">";
            }
            String rendered = Messages.get(key, locale, args);
            if (PLACEHOLDER.matcher(rendered).find()) {
                broken.add(key + " -> " + rendered);
            }
        }
        broken.sort(String::compareTo);
        return broken;
    }

    /** One past the highest argument index the pattern names. */
    private static int arityOf(String template) {
        Matcher m = PLACEHOLDER.matcher(template);
        int highest = -1;
        while (m.find()) {
            highest = Math.max(highest, Integer.parseInt(m.group(1)));
        }
        return highest + 1;
    }
}
