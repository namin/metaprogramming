import java.lang.reflect.*;

public class Naughty {
    public static void main(String[] args) throws Exception {
        RatNum r = new RatNum(6, 3);
        System.out.println("6/3 is "+r);

        Class<?> c = r.getClass();

        Field field = c.getDeclaredField("denom");

        field.setAccessible(true);
        Field mods = Field.class.getDeclaredField("modifiers");
        mods.setAccessible(true);
        mods.setInt(field, field.getModifiers() & ~Modifier.FINAL);

        field.setInt(r, 2);

        System.out.println("6/3 is "+r);
    }
}
