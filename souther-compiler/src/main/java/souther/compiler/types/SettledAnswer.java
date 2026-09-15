package souther.compiler.types;

/**
 * Something the front end settled about a declaration: what a type is, what a name reaches, which
 * binding a use is of, which slot a parameter fills.
 *
 * <p>Said by the type and not read off where its file sits. Everything the front end settles is
 * written in this package, and so is everything this compile keeps about how it built what it built
 * ({@link RecordOfTheBuilding}) — a reader that took the package for the answer would hand one to
 * both, and to whatever is written here next.
 *
 * <p>What it is and not what is done with it. A reader that holds two builds to each other depends
 * on what is settled here, which is why it is worth saying which types those are; whether it reads
 * a particular one, and how, is that reader's own answer and is written where it reads.
 */
public interface SettledAnswer {
}
