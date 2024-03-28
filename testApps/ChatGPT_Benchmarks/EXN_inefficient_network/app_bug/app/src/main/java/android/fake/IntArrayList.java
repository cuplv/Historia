package android.fake;

public class IntArrayList {
    int[] values;

    public IntArrayList(int size){
        values = new int[size];
    }

    public void add(int value, int index){
        values[index] = value;
    }
    public int get(int index){
        return values[index];
    }
    public int size(){
        return values.length;
    }
}
