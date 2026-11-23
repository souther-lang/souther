package souther.compiler.partition;

import java.util.List;

/**
 * What a fixture is written as: a word, or texts between an opening and a closing with commas
 * between them.
 *
 * <p>Put together when it is asked for and not when it is made. A value is written from its parts
 * up, and whoever composes one asks for the text of the whole: putting together the text at each
 * level writes what stands deepest once for every level above it.
 *
 * <p>Two of these are equal where the texts are, however each was put together.
 */
public final class FixtureText {

    private sealed interface Form {

        /** The text, put together. */
        record Word(String text) implements Form {}

        /** What it is put together of. */
        record Around(String opening, List<FixtureText> within, String closing) implements Form {

            public Around {
                within = List.copyOf(within);
            }
        }
    }

    /** What it is put together of, until something asked for the text, and the text from there on:
     *  a row is kept longer than what it was composed of. Either says the same text, so a reader
     *  that meets one while another reader puts the other there reads no different a text. */
    private Form form;

    private FixtureText(Form form) {
        this.form = form;
    }

    /** A text written as it is, which is some text. */
    static FixtureText word(String text) {
        if (text == null || text.isBlank()) {
            throw new IllegalArgumentException("a fixture is written as some text");
        }
        return new FixtureText(new Form.Word(text));
    }

    /** {@code within} between {@code opening} and {@code closing}. */
    static FixtureText around(String opening, List<FixtureText> within, String closing) {
        return new FixtureText(new Form.Around(opening, within, closing));
    }

    /** The text. */
    public String written() {
        return switch (form) {
            case Form.Word(String text) -> text;
            case Form.Around around -> {
                StringBuilder out = new StringBuilder();
                write(around, out);
                String text = out.toString();
                form = new Form.Word(text);
                yield text;
            }
        };
    }

    private static void write(Form form, StringBuilder out) {
        switch (form) {
            case Form.Word(String text) -> out.append(text);
            case Form.Around(String opening, List<FixtureText> within, String closing) -> {
                out.append(opening);
                for (int at = 0; at < within.size(); at++) {
                    if (at > 0) {
                        out.append(", ");
                    }
                    write(within.get(at).form, out);
                }
                out.append(closing);
            }
        }
    }

    @Override
    public boolean equals(Object other) {
        return this == other
                || (other instanceof FixtureText text && written().equals(text.written()));
    }

    @Override
    public int hashCode() {
        return written().hashCode();
    }

    @Override
    public String toString() {
        return written();
    }
}
