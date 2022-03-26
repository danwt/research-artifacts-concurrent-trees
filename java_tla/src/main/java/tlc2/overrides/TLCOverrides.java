package tlc2.overrides;

public class TLCOverrides implements ITLCOverrides {

    @SuppressWarnings("rawtypes")
    @Override
    public Class[] get() {
        try {

            return new Class[] { TreeGeneration.class, Linearizability.class};

        } catch (NoClassDefFoundError e) {
            System.out.println("Could not load custom operator overload index classes");
            throw e;
        }
    }
}