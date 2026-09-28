package souther.lsp;

import souther.test.OnlyARowIsCalledARow;

/**
 * Only a row is called a row.
 *
 * <p>The rule this repository holds every module to, said here about this one. This module asks the
 * compiler about rows and hands an editor what it answered; what it holds of its own is an
 * editor's, so the rule has no admitting side to state here and the prohibition is the whole of it.
 *
 * <p>Which is the case the rule is most worth having in: a reader here meets both vocabularies at
 * once, and a name that says row while holding an offer, a count or a position is read as the
 * compiler's word for a line.
 */
class OnlyARowIsCalledARowTest extends OnlyARowIsCalledARow {

    OnlyARowIsCalledARowTest() {
        super(LspMethod.class, "the language server holds no rows of its own");
    }
}
