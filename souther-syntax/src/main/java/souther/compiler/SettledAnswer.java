package souther.compiler;

/**
 * Something the front end settled about a declaration: what a type is, what a name reaches, which
 * binding a use is of, which slot a parameter fills.
 *
 * <p>Said by the type. A form a declaration is made of is one of these, a form of the grammar, or
 * something this compile keeps about reading and building it ({@link RecordOfTheBuilding}) — and
 * where a form's file sits tells those apart from nothing, the front end writing its answers beside
 * what it keeps about arriving at them.
 *
 * <p>What it is and never what is done with it. A reader that holds two builds to each other
 * depends on what is settled here, which is why it is worth saying which forms those are; whether
 * such a reader looks at a particular one is that reader's own answer, written where it reads.
 *
 * <p>Declared here rather than beside the answers, because the forms a declaration is made of are
 * not all in one place: a position and the span it stands in are written where the text is read,
 * and a vocabulary a form cannot see is one that form cannot speak.
 */
public interface SettledAnswer {
}
