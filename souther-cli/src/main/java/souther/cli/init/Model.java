package souther.cli.init;

import java.util.List;

/**
 * How much of a model a new project starts with.
 *
 * <p>Three levels and it stays three. Choosing by subject matter — {@code --model ordering},
 * {@code --model invoicing} — would mean carrying a library of models inside this jar and a list
 * that grows with it, and a list nobody can read is what a starting command becomes when its
 * templates are a catalogue.
 *
 * <p>What separates them is what the first build answers. {@code none} is a module and nowhere for
 * a rule to live yet; {@code minimal} is a value with a rule on it, which is the smallest thing this
 * language is for; {@code full} is a model whose {@code example} rows and whose Java test both
 * answer on the first run, so that {@code mvn test} and {@code souther examples} say something
 * before a line has been written.
 */
public enum Model {

    NONE("none"),
    MINIMAL("minimal"),
    FULL("full");

    private final String spelling;

    Model(String spelling) {
        this.spelling = spelling;
    }

    String spelling() {
        return spelling;
    }

    /** The level this text names, or null where it names none. */
    static Model written(String text) {
        for (Model model : values()) {
            if (model.spelling.equals(text)) {
                return model;
            }
        }
        return null;
    }

    /** Every level, in the order a refusal lists them. */
    static List<String> spellings() {
        return java.util.Arrays.stream(values()).map(Model::spelling).toList();
    }
}
