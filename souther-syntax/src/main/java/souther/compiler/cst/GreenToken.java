package souther.compiler.cst;

/** A green leaf: its kind and the exact source text it covers (trivia tokens included). */
public record GreenToken(SyntaxKind kind, String text) implements Green {

    @Override
    public int width() {
        return text.length();
    }

    @Override
    public int depth() {
        return 1;
    }

    @Override
    public void appendText(StringBuilder sb) {
        sb.append(text);
    }
}
