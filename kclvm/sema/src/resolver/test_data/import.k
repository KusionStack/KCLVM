import abc # unable to import
import import_test.a
import import_test.a # reimport
import import_test.c  # test unused import for mixin name
import import_test.d # test unused import for parent name
import import_test.e # test unused import for union type
import import_test.f as g # test unused import for union type

schema Main(d.Parent):
    mixin [c.TestOfMixin]
    age?: int = 18
    person?: a.Person
    list_union_type: [e.UnionType|int]
    dict_union_type: {g.UnionType|int:float}

import import_test.b  

if a._a > 1:
    _c = 1
elif a._a == 1:
    _c = 2
else:
    _c = 3

p = Main{
    age = b._b
}
