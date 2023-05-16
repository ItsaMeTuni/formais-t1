
class {:autocontracts} Queue {

    ghost var contents: seq<int>;

    var list: array<int>
    var head: nat
    var tail: nat
    var size: nat

    ghost predicate Valid()
    {
        list.Length > 0 &&
        size == |contents| &&
        (size <= 1 <==> head == tail) &&
        (size > 1 ==> (head + size - 1) % list.Length == tail) &&

        0 <= head < list.Length &&
        0 <= tail < list.Length &&
        contents == 
            if size > 0 then
                if head > tail
                then list[head..] + list[..tail + 1]
                else list[head..tail + 1]
            else []
    }

    constructor()
        ensures contents == []
    {
        contents := [];

        list := new int[10];
        head := 0;
        tail := 0;
        size := 0;
    }

    // method enqueue(x: int) 
    //     ensures contents == old(contents) + [x]
    // {
    //     if size + 1 > list.Length
    //     {
    //         // grow
    //     }
    // }

    method grow()
        requires size > 0
        ensures contents == old(contents)
        ensures list.Length == 2 * old(list.Length)
    {
        var new_list := new int[list.Length * 2];

        forall i: nat | 0 <= i < size { 
            new_list[i] := list[(head + i) % list.Length];
        }

        list := new_list;
        head := 0;
        tail := size - 1;

        contents := list[..size];
        Repr := {this, list};
    }

    // method dequeue() returns (x: int)
    //     requires |contents| > 0
    //     ensures x == old(contents)[0]
    //     ensures contents == old(contents)[1..]
    // {}

    method contains(x: int) returns (r: bool)
        ensures r <==> x in contents
    {
        r := if size > 0 then
                if head > tail
                then x in list[head..] + list[..tail + 1]
                else x in list[head..tail + 1]
            else false;
    }

    method length() returns (l: nat) 
        ensures l == |contents|
    {
        l := size;
    }

    method isEmpty() returns (r: bool)
        ensures r <==> |contents| == 0
    {
        r := size == 0;
    }

    // method concat(other: Queue) returns (r: Queue)
    //     ensures r.contents == contents + other.contents
    // r = new Queue;
    // r.Repr := {r, r.list};
    // {}
}