class {:autocontracts} Queue {

    ghost var contents: seq<int>;

    var list: array<int>
    var head: nat
    var tail: nat
    var size: nat

    ghost predicate Valid()
    {
        list.Length >= 10 &&
        size == |contents| &&
        size <= list.Length &&
 
        0 <= head < list.Length &&
        0 <= tail < list.Length &&

        (if head <= tail then size == tail - head
        else (head + size) % list.Length == tail) &&
        
        contents == 
            if size > 0 then
                if head > tail
                then list[head..] + list[..tail]
                else list[head..tail]
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

    method enqueue(x: int) 
        ensures contents == old(contents) + [x]
        ensures size == old(size) + 1
    {
        if size == list.Length {
            grow();
        }

        tail := (tail + 1) % list.Length;
        list[tail] := x;
        size := size + 1;
        contents := contents + [x];
    }

    method grow()
        requires size == list.Length
        ensures contents == old(contents)
        ensures size == old(size)
        ensures list.Length == 2 * old(list.Length)
    {
        var new_list := new int[list.Length * 2];

        forall i: nat | 0 <= i < list.Length { 
            new_list[i] := list[(head + i) % list.Length];
        }

        list := new_list;
        head := 0;
        tail := size - 1;

        Repr := {this, list};
    }

    method dequeue() returns (x: int)
        requires |contents| > 0
        ensures x == old(contents[0])
        ensures contents == old(contents[1..])
    {
        x := list[head];
        list[head] := 0;
        head := (head + 1) % list.Length;
        size := size - 1;
        contents := contents[1..];
    }

    method contains(x: int) returns (r: bool)
        ensures r <==> x in contents
    {
        r := if size > 0 then
                if head >= tail
                then x in list[head..] + list[..tail]
                else x in list[head..tail]
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