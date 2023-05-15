
class Queue {
    var list: array<int>;
    var size: int;
    var first: int;

    ghost var list_ghost: array<int>;
    ghost var size_ghost: int;

    // Invariant: size is non-negative
    // Invariant: size is less than or equal to the length of list
    // Invariant: all elements of list before index size are valid
    // Invariant: all elements of list after index size are zero
    predicate Valid()
        reads *
    {
        0 <= size <= list.Length
        // forall i :: 0 <= i < size ==> list[i] |-> ? &&
        // forall i :: size <= i < list.Length ==> list[i] == 0
    }

    constructor()
        ensures Valid()
    {
        list := new int[100];
        size := 0;
        first := 0;
    }

    method enqueue(x: int)
        requires Valid()
        // ensures size_ghost == old(size_ghost) + 1
        // ensures list_ghost[size_ghost - 1] == x
        ensures Valid()
        modifies list, this
    {
        list[size] := x;
        size := size + 1;

    }

    method grow() 
        requires Valid()
        ensures list.Length == 2 * old(list.Length)
        modifies this
    {
        var new_list := new int[list.Length * 2];

        var i := 0;
        while (i < size) 
            invariant i >= 0;
            invariant i <= size;
            decreases size - i;
        {
            new_list[i] := list[i];
            i := i + 1;
        }

        list := new_list;
    }

    method pop() {}

    method contains() {}

    method length() {}

    method isEmpty() {}

    method concat() {}
}