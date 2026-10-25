package souther.compiler.meaning;

import net.unit8.notation199x.pattern.PatternMeaning;

import java.util.Objects;

/**
 * The strings a statement about a string is about, spelled once.
 *
 * <p>A statement is told apart from another by what it states, and what it states here is a set of
 * strings, which a meaning says by its structure. Spelled out, that structure is as long as the
 * meaning is deep, and a statement is made again as its denial every time a reader asks for one:
 * if each of them spelled the set again, the spelling would be paid for as often as the statement
 * is turned over. So it is spelled where the set is made, and a statement and its denial hold the
 * one value.
 *
 * <p>Two of these are one where they are spelled alike. The spelling is of the meaning and of
 * nothing else, so it is equal exactly where the meanings are.
 *
 * @param meaning the strings
 * @param spelled the meaning written out, from the meaning whatever is handed in
 */
public record StringsLanguage(PatternMeaning meaning, String spelled) {

    public StringsLanguage {
        Objects.requireNonNull(meaning, "a set of strings is said by a meaning");
        spelled = meaning.toString();
    }

    public StringsLanguage(PatternMeaning meaning) {
        this(meaning, null);
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof StringsLanguage that && spelled.equals(that.spelled);
    }

    @Override
    public int hashCode() {
        return spelled.hashCode();
    }

    @Override
    public String toString() {
        return spelled;
    }
}
