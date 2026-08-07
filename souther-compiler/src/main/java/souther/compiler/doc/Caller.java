package souther.compiler.doc;

/**
 * Who a command is answering, so that what an answer offers next is something that caller can do.
 *
 * <p>The doc and api answers are written once and reached over two wires. A line that says how to
 * see more has to name a way of asking, and the two callers ask differently: a reader at a prompt
 * has subcommands and flags, an MCP client has tools and their arguments. Naming the other one's
 * spelling sends the reader somewhere they cannot go.
 *
 * <p>Every such offer lives here rather than at the place that prints it, so that adding a caller
 * is answering these questions once instead of finding every message that asks them.
 *
 * <p>These are the offers a command composes. A document that sends its reader somewhere writes
 * the same kind of offer in its own text, as an {@link Affordance}, and this is what picks its
 * spelling too.
 */
enum Caller {

    CLI, MCP;

    /** How to see every specification section and every shipped doc topic. */
    String everySectionAndTopic() {
        return switch (this) {
            case CLI -> "`souther doc` lists every section and topic";
            case MCP -> "`doc_read` with no `name` lists every section and topic";
        };
    }

    /** How to see every specification section. */
    String everySection() {
        return switch (this) {
            case CLI -> "`souther doc` lists every section";
            case MCP -> "`doc_read` with no `name` lists every section";
        };
    }

    /** How to ask a search for the hits it held back. */
    String everyHit() {
        return switch (this) {
            case CLI -> "`--limit 0` for all of them";
            case MCP -> "`limit: 0` for all of them";
        };
    }

    /** How to read a stdlib module's own source, where what a signature means is written. */
    String stdlibSource(String module) {
        return Affordance.STDLIB_SOURCE.spelled(this, module) + " for what it means";
    }
}
