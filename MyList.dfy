interface IMyList {
  ghost int[] list_ghost
  ghost var size_ghost: int
}

class MyList implements IMyList {
  var list: array<int> := new int[100];
  var size: int := 0;

  ghost var list_ghost: array<int> := list;
  ghost var size_ghost: int := size;

  // Invariant: size is non-negative
  // Invariant: size is less than or equal to the length of list
  // Invariant: all elements of list before index size are valid
  // Invariant: all elements of list after index size are zero
  predicate Valid() {
    0 <= size <= list.Length &&
    forall i :: 0 <= i < size ==> list[i] |-> ? &&
    forall i :: size <= i < list.Length ==> list[i] == 0
  }

  constructor() 
    ensures Valid()
  {
    list := new int[100];
    size := 0;
  }

  method size() returns (result: int)
    requires Valid()
  {
    result := size;
  }

  method isEmpty() returns (result: bool)
    requires Valid()
  {
    result := size == 0;
  }
}
