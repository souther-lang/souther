package souther.compiler.fmt;

/** Where something was written in a laid-out canonical form: from {@code start} up to {@code end}. */
record Span(int start, int end) {

    @Override
    public String toString() {
        return start + ".." + end;
    }
}
