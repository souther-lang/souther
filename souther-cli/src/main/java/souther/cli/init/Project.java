package souther.cli.init;

/**
 * What a project this command writes for is: its coordinate, the module its sources declare, how
 * much of a model it starts with, and the Souther it is compiled by.
 *
 * <p>All four are settled before a file is written. Each of them is read by more than one template —
 * the module name is a header, a Java package and a directory — and deciding one of them inside a
 * template would be deciding it once per file.
 *
 * @param coordinate what the build calls this project
 * @param moduleName the header the {@code .sou} declares, which is also the package it generates into
 * @param model how much of a model to start with
 * @param build the build system the project is run by
 * @param southerVersion the Souther the project compiles with, which is the one that generated it
 */
public record Project(Coordinate coordinate, String moduleName, Model model, BuildSystem build,
                      String southerVersion) {

    /**
     * The file stem the module's sources are written under: what the module is called, last segment
     * first.
     *
     * <p>The module's own last segment rather than the artifact it was derived from. The two differ
     * exactly where the artifact carries a hyphen, and a file called {@code billing-service.sou}
     * declaring {@code com.acme.billing_service} beside a {@code com/acme/billing_service/} of Java
     * spells one name two ways. A file is named after what it declares.
     */
    String sourceStem() {
        return moduleName.substring(moduleName.lastIndexOf('.') + 1);
    }

    /** Where a Java source of this module's package goes, under a source root. */
    String packagePath() {
        return moduleName.replace('.', '/');
    }
}
