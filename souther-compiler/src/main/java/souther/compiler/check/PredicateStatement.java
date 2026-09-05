package souther.compiler.check;

/**
 * What a rule about the values at a position states, in the words the model states it in.
 *
 * <p>What a class such a rule makes is called. A class is not the rule that made it and not where
 * that rule was written — it is a set of the position's values, and what names one is what a value
 * in it satisfies. So this is the meaning and never the provenance: {@code PredicateOrigin} says
 * which authored rule and which reading of it produced a piece of evidence, and two copies of one
 * helper have two of those and one of these.
 *
 * <p><b>Not the source text, and not a pattern either.</b> An author may write the same rule two
 * ways and a document should call the class it makes one thing, so what is kept is what the rule
 * says rather than the spelling that reached it. And what the rule admits is a
 * {@link souther.compiler.regex.PatternPlan}'s to build, which stays below the crossing that builds
 * it — a label made out of one would put the machine's own vocabulary into a document.
 *
 * <p><b>One arm per way a rule reads, and not one field bent to hold them all.</b> A library
 * predicate applied to a position and a value the model singles out are two shapes on the page and
 * two sentences to a reader, and a type that held the second as an operation called {@code =} would
 * be a document naming an operation the language does not have.
 */
public sealed interface PredicateStatement {

    /**
     * A library operation applied to what stands at the position: {@code String.startsWith("JP", x)}.
     *
     * <p>Both parts come off the call. Every predicate over a string in this compiler's table takes
     * what the author wrote first and the position second, so a statement is the operation's name
     * and that one argument, whichever of them it is.
     *
     * @param operation what the model calls the operation, as an author writes it
     * @param written   the text the author wrote in it
     */
    record Applying(String operation, String written) implements PredicateStatement {

        public Applying {
            if (operation == null || written == null) {
                throw new IllegalArgumentException(
                        "an applied rule states some operation over some text");
            }
        }

        @Override
        public String saidOf(String subject) {
            return operation + "(" + quoted(written) + ", " + subject + ")";
        }
    }

    /**
     * A value the model singles out: {@code x = "JP"}.
     *
     * <p>Its own arm because it is its own sentence. Read as an operation applied to the position, a
     * document would name a function nobody wrote, and the day the language gains one by that name
     * the two would be indistinguishable.
     *
     * @param written the value, as a source carries it
     */
    record Equalling(String written) implements PredicateStatement {

        public Equalling {
            if (written == null) {
                throw new IllegalArgumentException("a rule that singles a value out has one");
            }
        }

        @Override
        public String saidOf(String subject) {
            return subject + " = " + quoted(written);
        }
    }

    /**
     * The rule as it would be written about {@code subject}.
     *
     * <p>The subject is handed in because a class is about a position and the name a reader knows
     * that position by is the reader's. Written with the name the body happened to bind, a class of
     * one position would be called two things in two behaviors that both write the rule.
     */
    String saidOf(String subject);

    /** And the values it leaves, said the same way. */
    default String deniedOf(String subject) {
        return "not " + saidOf(subject);
    }

    /** The text as a source carries it, so that a label reads back as something somebody wrote. */
    static String quoted(String text) {
        StringBuilder out = new StringBuilder("\"");
        text.codePoints().forEach(each -> out.append(switch (each) {
            case '"' -> "\\\"";
            case '\\' -> "\\\\";
            case '\n' -> "\\n";
            case '\r' -> "\\r";
            case '\t' -> "\\t";
            default -> Character.toString(each);
        }));
        return out.append('"').toString();
    }
}
