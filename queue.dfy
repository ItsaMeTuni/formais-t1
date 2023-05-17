// Trabalho 1 de Metodos Formais
// Lucas Antunes
// Henrique Xavier
// Louise Dornelles
// Gabriel Panho
// Arthur Maia

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

        (head < tail ==> size == tail - head) &&
        (head == tail ==> size == 0 || size == list.Length) &&
        (head > tail ==> (head + size) % list.Length == tail) &&
        
        contents == 
            if size > 0 then
                if head >= tail
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
    {
        if size == list.Length {
            grow();
        }
        enqueue_append(x);
    }

    method enqueue_append(x: int)
        requires size < list.Length
        ensures contents == old(contents) + [x]
    {
        list[tail] := x;
        tail := (tail + 1) % list.Length;
        size := size + 1;
        contents := contents + [x];
    }

    method grow()
        requires size == list.Length
        ensures contents == old(contents)
        ensures size == old(size)
        ensures size < list.Length
    {
        var new_list := new int[list.Length + 10];

        forall i: nat | 0 <= i < list.Length { 
            new_list[i] := list[(head + i) % list.Length];
        }

        list := new_list;
        head := 0;
        tail := size;

        Repr := {this, list};
    }

    method dequeue() returns (x: int)
        requires |contents| > 0
        ensures x == old(contents[0])
        ensures contents == old(contents[1..])
    {
        x := list[head];
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

    method concat(other: Queue) returns (r: Queue)
        requires size > 0
        requires other.size > 0
        requires other != this
        requires other.Valid()
        ensures r.contents == contents + other.contents
    {
        r := new Queue();

        r.append(this);
        r.append(other);
    }

    method append(other: Queue)
        requires other != this
        requires other.Valid()
        ensures contents == old(contents) + other.contents
    {
        var i := 0;
        while i < other.size
            invariant other.Valid()
            invariant Valid()
        {
            var x := other.peek(i);
            enqueue(x);
            i := i + 1;
        }
    }

    method peek(idx: nat) returns (x: int)
    requires size > 0
    requires idx < size
    ensures x == contents[idx]
    {
        x := list[(head + idx) % list.Length];
    }
}

method Main()
{
    var q := new Queue();
    q.enqueue(1);
    q.enqueue(2);
    q.enqueue(3);
    q.enqueue(4);
    q.enqueue(5);
    q.enqueue(6);
    q.enqueue(7);
    q.enqueue(8);
    q.enqueue(9);
    q.enqueue(10);
    q.enqueue(11);
    assert q.contents == [1,2,3,4,5,6,7,8,9,10,11];

    var l := q.length();
    assert l > 10;

    var deq := q.dequeue();
    assert q.contents == [2,3,4,5,6,7,8,9,10,11];
    assert deq == 1;

    l := q.length();
    assert l == 10;

    var cnt := q.contains(5);
    assert cnt;

    cnt := q.contains(1);
    assert !cnt;

    var empty := q.isEmpty();
    assert !empty;

    var peek := q.peek(0);
    assert peek == 2;

    var q2 := new Queue();
    q2.enqueue(12);
    q2.enqueue(13);

    var q3 := q.concat(q2);
    assert q3.contents == [2,3,4,5,6,7,8,9,10,11,12,13];
}

