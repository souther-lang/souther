package souther.compiler.diag;

import souther.compiler.diag.msg.MessageTemplate;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The grammar of an entry filled by name, as one parser.
 *
 * <p>What reads an entry and what checks one are the same code, so this is where the grammar itself
 * is written down. A template read one way by the renderer and another by the check is how a name
 * nothing fills reached a reader as braces.
 *
 * <p>A brace of its own is written twice. Both of them: closing only the opening one would take
 * {@code {name}}} — a value and a stray brace — for something the author meant.
 */
class ACatalogEntryIsReadOneWayTest {

    private static List<String> names(String written) {
        return MessageTemplate.parse(written).names();
    }

    private static List<String> wrong(String written) {
        return MessageTemplate.parse(written).malformations();
    }

    private static String literal(String written) {
        StringBuilder out = new StringBuilder();
        for (MessageTemplate.Part part : MessageTemplate.parse(written).parts()) {
            if (part instanceof MessageTemplate.Part.Text text) {
                out.append(text.written());
            }
        }
        return out.toString();
    }

    @Test
    void aNameBetweenBracesIsAValueTheEntryWrites() {
        assertEquals(List.of("field", "heldBy"), names("Field `{field}` from `{heldBy}`."));
        assertEquals(List.of(), wrong("Field `{field}` from `{heldBy}`."));
    }

    @Test
    void aDoubledBraceIsABraceOfItsOwn() {
        assertEquals(List.of(), names("Put it in a block (`-> {{ match ... }}`)."));
        assertEquals(List.of(), wrong("Put it in a block (`-> {{ match ... }}`)."));
        assertEquals("Put it in a block (`-> { match ... }`).",
                literal("Put it in a block (`-> {{ match ... }}`)."));
    }

    @Test
    void aDoubledBraceAroundANameIsThatTextAndNotAValue() {
        assertEquals(List.of(), names("{{name}}"));
        assertEquals("{name}", literal("{{name}}"));
    }

    @Test
    void aBraceNothingClosesIsRefused() {
        assertEquals(List.of("a brace nothing closes: {field"), wrong("takes {field"));
    }

    @Test
    void aClosingBraceNothingOpensIsRefused() {
        assertEquals(List.of("a closing brace nothing opens: }"), wrong("`{name}}` is invalid"));
        assertEquals(List.of("name"), names("`{name}}` is invalid"));
    }

    @Test
    void aBraceHoldingSomethingThatIsNotANameIsRefused() {
        assertEquals(List.of("a brace holding something that is not a value's name: {held by}"),
                wrong("from `{held by}`"));
        assertEquals(List.of("a brace holding something that is not a value's name: {}"),
                wrong("an empty {} says nothing"));
    }

    /**
     * A name is a component's name, and an underscore is part of one.
     *
     * <p>So {@code {held_by}} is a name this entry writes and not a malformation — what refuses it
     * is the message not carrying a value under it, which is the other half of the same rule. The
     * two are worth keeping apart: one is an entry nobody can read, the other an entry read against
     * the wrong message.
     */
    @Test
    void anUnderscoreIsPartOfAName() {
        assertEquals(List.of("held_by"), names("from `{held_by}`"));
        assertEquals(List.of(), wrong("from `{held_by}`"));
    }
}
