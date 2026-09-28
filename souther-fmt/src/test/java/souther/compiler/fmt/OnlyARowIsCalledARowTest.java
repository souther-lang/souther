package souther.compiler.fmt;

import souther.test.OnlyARowIsCalledARow;

/**
 * Only a row is called a row.
 *
 * <p>The rule this repository holds every module to, said here about this one. A row of an
 * {@code example} is a compiler type and the formatter is not under the compiler, so there is
 * nothing here that could be one: the rule has no admitting side to state and the prohibition is
 * the whole of it. Declaring a row here would mean saying which type that is and what may hold one,
 * which is what the compiler's own copy of this does.
 */
class OnlyARowIsCalledARowTest extends OnlyARowIsCalledARow {

    OnlyARowIsCalledARowTest() {
        super(Columns.class, "the formatter holds no rows");
    }
}
