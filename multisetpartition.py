r"""
Forms of multiset partitions
"""
#*****************************************************************************
#       Copyright (C) 2018 Mike Zabrocki <zabrocki@mathstat.yorku.ca>,
#
#  Distributed under the terms of the GNU General Public License (GPL)
#
#    This code is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
#    General Public License for more details.
#
#  The full text of the GPL is available at:
#
#                  http://www.gnu.org/licenses/
#*****************************************************************************
r"""
    REFERENCES:

    .. [OZ15] R. Orellana, M. Zabrocki, Symmetric group characters as symmetric
    functions, :arXiv:`1605.06672`

    .. [OZ17] R. Orellana, M. Zabrocki, Products of characters of the symmetric
    group, :arXiv:`1709.08098`
"""

print("Loading MultiSetPartition, SetPartitionofMultiSet, MultiSetPartitions and SetPartitionsofMultiSet")
print("BiSetPartition, BiSetPartitions, MCPartition, MCPartitions (v 6.0 date: Feb 8, 2020)")
print("key_lex, key_rlex, key_grlex")
#print("grlex_msp, lex_msp, gr_rev_lex_msp, rev_lex_msp, rev_gr_revlex_msp, last_letter_order_bsp")
# history
# v 1.0 16/11/18 : first working version of MultiSetPartition
# v 1.1 16/11/18 : added some functionality (e.g. is_atomic, to_composition)
# v 1.2 16/11/19 : added an optional parameter to specify the total order on the multisets
# v 1.3 17/1/22 : added comparison function lex_msp
# v 1.4 17/2/21 : new methods raise_content, restrict, smash_product (but not documentation)
# v 1.5 17/2/23 : added gr_rev_lex_msp, rev_lex_msp (but not documentation)
# v 1.6 17/3/14 : added rev_gr_rev_msp (but this is experimental and documentation is not right)
# v 2.0 17/3/14 : first working version of SetPartitionofMultiSet
# v 2.1 17/3/15 : factored out common elements from MultiSetPartition and wrote code that is compatible for both classes
# v 2.2 17/3/19 : corrected bug where the empty partition is handled
# v 2.3 17/3/21 : fixed smash_product and added documentation for restrict and smash_product
# v 2.4 17/4/26 : corrected doc tests
# v 3.0 17/8/11 : added BiSetPartition and BiSetPartitions
# v 3.1 17/8/16 : corrected some documentation, rlex_bsp is the best order for BiSetPartitions
# v 3.2 17/9/23 : added is_coarser method, changed "Multiset" to "MultiSet" globally
# v 3.3 17/10/10 : added an optional parameter "shifted" to smash_product
# v 3.4 17/10/21 : added standardize operation
# v 4.0 17/10/28 : added class of all MultiSetPartitions so that MultiSetPartitions() works
# v 5.0 18/1/7 : added classes MCPartition and MCPartitions
# v 5.0.1 20/2/08 : updated print statements for compatibility with python3
# v 6.0 20/2/08 : comparison functions in sorted updated to key functions for python3
# TODO: some comparison functions still need to be turned into key functions for compatablity with python3
# TODO: check if it tries to create a Multiset partition or set partition incorrectly
# TODO: make a better smash product
# TODO: get the parent structure of these methods right
# sage: Partition([3,2]).parent()
# Partitions
# sage: MultiSetPartition([[1],[2,2,1]]).parent()
# multi-set partitions with content vector [2, 2]
# TODO: put comparison function in global options instead of as a parameter and then fix parent problem
# TODO: put repr and latex output as a global option



from sage.combinat.combinat import CombinatorialElement
from sage.structure.unique_representation import UniqueRepresentation
from sage.structure.parent import Parent
from sage.combinat.composition import Composition
from sage.categories.finite_enumerated_sets import FiniteEnumeratedSets
from sage.combinat.partition import Partition
from sage.combinat.vector_partition import VectorPartition, VectorPartitions
#from sage.misc.misc import uniq

class MSP(CombinatorialElement):
    def __init__(self, parent, msp):
        r"""
        Initialize ``self``.

        INPUT:

        - ``msp`` - a list of lists

        EXAMPLES::

            sage: elt =  MultiSetPartition([[1,1,2], [2, 2, 1]])
            sage: TestSuite(elt).run(skip = ["_test_pickling"])
            sage: elt =  SetPartitionofMultiSet([[1],[1,2],[2,1],[2]])
            sage: TestSuite(elt).run(skip = ["_test_pickling"])
        """
        if parent._key is not None:
            nsp = sorted([sorted(A) for A in msp if A!=[]],key=parent._key)
        else:
            nsp = sorted([sorted(A) for A in msp if A!=[]])
        CombinatorialElement.__init__(self, parent, nsp)

    def _repr_pp(self):
        r"""
        Represent multi-sets separated by "|" and partition enclosed by "{}"

        It was a choice to use ``_repr_pp_short`` for the pp function
        This representation will be used if the content vector has length
        longer than 9.

        EXAMPLES::

            sage: for msp in MultiSetPartitions([2,2]):
            ....:     print(msp._repr_pp())
            ....:     
            {1|1|2|2}
            {1, 1|2|2}
            {1|1, 2|2}
            {1, 1, 2|2}
            {1|1|2, 2}
            {1, 1|2, 2}
            {1|1, 2, 2}
            {1, 2|1, 2}
            {1, 1, 2, 2}
            sage: for msp in SetPartitionsofMultiSet([2,2]):
            ....:     print(msp._repr_pp())
            ....:     
            {1|1|2|2}
            {1|1, 2|2}
            {1, 2|1, 2}
        """
        return "{"+"".join(str(self[i])[1:-1]+"|" for i in range(len(self)-1))+str(self[-1])[1:-1]+"}"

    def _repr_pp_short(self):
        r"""
        Represent multi-sets separated by "|" and enclosed the partition by "{}"

        MultiSets are represented strings of symbols not separated by commas

        EXAMPLES::

            sage: for msp in MultiSetPartitions([2,2]):
            ....:     print(msp._repr_pp_short())
            {1|1|2|2}
            {11|2|2}
            {1|12|2}
            {112|2}
            {1|1|22}
            {11|22}
            {1|122}
            {12|12}
            {1122}
            sage: for msp in SetPartitionsofMultiSet([2,2]):
            ....:     print(msp._repr_pp_short())
            ....:     
            {1|1|2|2}
            {1|12|2}
            {12|12}
        """
        return "{"+"".join("".join(str(a) for a in self[i])+"|" for i in
            range(len(self)-1))+"".join(str(a) for a in self[-1])+"}"

    def pp(self):
        r"""
        pretty print of a multi-set partition

        EXAMPLES::

            sage: for msp in MultiSetPartitions([2,2]):
            ....:     msp.pp()
            {1|1|2|2}
            {11|2|2}
            {1|12|2}
            {112|2}
            {1|1|22}
            {11|22}
            {1|122}
            {12|12}
            {1122}
            sage: for msp in SetPartitionsofMultiSet([2,2]):
            ....:     msp.pp()
            ....:     
            {1|1|2|2}
            {1|12|2}
            {12|12}
        """
        if len(self.content_vector())>9:
            print(self._repr_pp())
        else:
            print(self._repr_pp_short())

    def content_vector(self):
        r"""
        The list whose `i^{th}` entry is the number of `i+1`s in
        the multi-set partition

        EXAMPLES::

            sage: MultiSetPartition([[1,1,2],[2, 2, 1]]).content_vector()
            [3, 3]
            sage: MultiSetPartition([[1,1,3],[3, 3, 1]]).content_vector()
            [3, 0, 3]
            sage: SetPartitionofMultiSet([[1],[1,2],[2,1],[2]]).content_vector()
            [3, 3]
            sage: SetPartitionofMultiSet([[1],[1,3],[3,1],[3]]).content_vector()
            [3, 0, 3]
        """
        return self.parent().content_vector()

    def length(self):
        r"""
        The number of parts of the multi-set partition

        EXAMPLES::

            sage: MultiSetPartition([[1,1,2],[2, 2, 1]]).length()
            2
            sage: MultiSetPartition([[1,1,3],[3, 3],[1]]).length()
            3
            sage: SetPartitionofMultiSet([[1],[1,2],[2,1],[2]]).length()
            4
            sage: SetPartitionofMultiSet([[1,2,3],[1,3],[1]]).length()
            3
        """
        return len(self)

    def size(self):
        r"""
        The number of entries in all of the multi-sets in the partition

        EXAMPLES::

            sage: MultiSetPartition([[1,1,2],[2, 2, 1]]).size()
            6
            sage: MultiSetPartition([[1,1,3],[3, 3, 1],[2,2]]).size()
            8
            sage: SetPartitionofMultiSet([[1],[1,2],[2,1],[2]]).size()
            6
            sage: SetPartitionofMultiSet([[1,2,3],[1,3],[1]]).size()
            6
        """
        return len(sum(self,[]))

    def unique_multisets(self):
        r"""
        A list of multi-sets that appear in the multi-set partition or
        set partition without repetition and in the same order in which
        they are stored.
        
        EXAMPLES::

            sage: msp = MultiSetPartition([[1],[2],[1,2],[1,2],[3],[3],[1,3],[1,3],[1,3]]); msp
            [[1], [1, 2], [1, 2], [1, 3], [1, 3], [1, 3], [2], [3], [3]]
            sage: msp.unique_multisets()
            [[1], [1, 2], [1, 3], [2], [3]]
            sage: spm = SetPartitionofMultiSet([[2],[1],[1],[1],[1,2],[2,1]]); spm
            [[1], [1], [1], [1, 2], [1, 2], [2]]
            sage: spm.unique_multisets()
            [[1], [1, 2], [2]]
        """
        if self.parent()._key is not None:
            return sorted(map(list,list(set(map(tuple,self)))),key=self.parent()._key)
        else:
            return sorted(map(list,list(set(map(tuple,self)))))

    unique_sets = unique_multisets

    def to_vector_partition(self):
        r"""
        A VectorPartition object equivalent to the multi-set partition or set
        partition

        EXAMPLES::

            sage: [msp.to_vector_partition() for msp in MultiSetPartitions([2,1])]
            [[[0, 1], [1, 0], [1, 0]], [[0, 1], [2, 0]], [[1, 0], [1, 1]], [[2, 1]]]
            sage: [spm.to_vector_partition() for spm in SetPartitionsofMultiSet([2,1])]
            [[[0, 1], [1, 0], [1, 0]], [[1, 0], [1, 1]]]
        """
        m = len(self.content_vector())
        return VectorPartition([[A.count(i) for i in range(1,m+1)] for A in self])

    def to_partition(self):
        r"""
        The multiplicity partition of the multi-set partition

        This is a partition that lists how many times sets appear in the
        multi-set partition.

        EXAMPLES::

            sage: MultiSetPartition([[1],[2],[1,2],[1,2],[3],[3],[1,3],[1,3],[1,3]]).to_partition()
            [3, 2, 2, 1, 1]
            sage: [msp.to_partition() for msp in MultiSetPartitions([2,2])]
            [[2, 2], [2, 1], [1, 1, 1], [1, 1], [2, 1], [1, 1], [1, 1], [2], [1]]
            sage: SetPartitionofMultiSet([[1],[2],[1,2],[1,2],[3],[3],[1,3],[1,3],[1,3]]).to_partition()
            [3, 2, 2, 1, 1]
            sage: [spm.to_partition() for spm in SetPartitionsofMultiSet([2,2])]
            [[2, 2], [1, 1, 1], [2]]
        """
        return Partition(sorted([list(self).count(list(S)) for S in self.unique_multisets()], reverse=True))

    def to_composition(self):
        r"""
        The multiplicity composition of the multi-set partition

        This is a composition that lists how many times sets appear in the
        multi-set partition, but it depends on the order that they are stored

        Default is that multi-set partitions are sorted in lex order

        EXAMPLES::

            sage: msp = MultiSetPartition([[1],[2],[1,2],[1,2],[3],[3],[1,3],[1,3],[1,3]]); msp
            [[1], [1, 2], [1, 2], [1, 3], [1, 3], [1, 3], [2], [3], [3]]
            sage: msp.to_composition()
            [1, 2, 3, 1, 2]
            sage: [msp.to_composition() for msp in MultiSetPartitions([2,2])]
            [[2, 2], [1, 2], [1, 1, 1], [1, 1], [2, 1], [1, 1], [1, 1], [2], [1]]
            sage: MultiSetPartition([[1,1],[2],[2]]).to_composition()
            [1, 2]
            sage: MultiSetPartition([[1,1],[2],[2]],grlex_msp).to_composition()
            [2, 1]
            sage: spm = SetPartitionofMultiSet([[1],[2],[1,2],[1,2],[3],[3],[1,3],[1,3],[1,3]]); spm
            [[1], [1, 2], [1, 2], [1, 3], [1, 3], [1, 3], [2], [3], [3]]
            sage: spm.to_composition()
            [1, 2, 3, 1, 2]
            sage: [spm.to_composition() for spm in SetPartitionsofMultiSet([2,2])]
            [[2, 2], [1, 1, 1], [2]]
            sage: SetPartitionofMultiSet([[1,2],[2],[2]]).to_composition()
            [1, 2]
            sage: SetPartitionofMultiSet([[1,2],[2],[2]],grlex_msp).to_composition()
            [2, 1]
        """
        return Composition([list(self).count(list(S)) for S in self.unique_multisets()])

    def is_atomic(self):
        r"""
        Test if a multi-set partition is atomic
        
        A multi-set partition is atomic if there is an ``r`` such that some
        sets have all values ``<= r`` and some have all values ``>r``

        EXAMPLES::

            sage: filter(lambda msp: msp.is_atomic(), MultiSetPartitions([2,2]))
            [[[1], [1, 2], [2]],
             [[1, 1, 2], [2]],
             [[1], [1, 2, 2]],
             [[1, 2], [1, 2]],
             [[1, 1, 2, 2]]]
            sage: filter(lambda msp: not msp.is_atomic(), MultiSetPartitions([2,2]))
            [[[1], [1], [2], [2]],
             [[1, 1], [2], [2]],
             [[1], [1], [2, 2]],
             [[1, 1], [2, 2]]]
             sage: filter(lambda msp: not msp.is_atomic(), SetPartitionsofMultiSet([2,2]))
             [[[1], [1], [2], [2]]]
             sage: filter(lambda msp: msp.is_atomic(), SetPartitionsofMultiSet([2,2]))
             [[[1], [1, 2], [2]], [[1, 2], [1, 2]]]
        """
        vs = sorted(list(set(sum(self,[]))))[:-1]
        return not any(all(all(i<=r for i in S) or all(i>r for i in S) for S in self) for r in vs)

    def raise_content(self, r):
        r"""
        add `r` to each entry in the multi-set partition

        INPUT:
 
        - ``r`` -- an integer (if `r` is negative it will decrease the entries)

        OUTPUT:
 
        - a multi-set partition

        EXAMPLES::

            sage: msp = MultiSetPartition([[1,1],[1,2],[1]])
            sage: msp.raise_content(4)
            [[5], [5, 5], [5, 6]]
            sage: spm = SetPartitionofMultiSet([[1,2],[1,2],[1]])
            sage: spm.raise_content(4)
            [[5], [5, 6], [5, 6]]
        """
        MSP = self.parent().Element
        return MSP([[a+r for a in ms] for ms in self])

    def to_list(self):
        r"""
        return a list of lists that represents the (multi-)set partition

        OUTPUT:

        - a list of lists

        EXAMPLES::

            sage: MultiSetPartition([[1,1],[1,2],[1]]).to_list()
            [[1], [1, 1], [1, 2]]
            sage: SetPartitionofMultiSet([[1,2],[1,2],[1]]).to_list()
            [[1], [1, 2], [1, 2]]
        """
        return self._list

    def standardize(self):
        r"""
        A set partition which has the same structure as ``self``.

        OUTPUT:

        - a set partition

        EXAMPLES::

            sage: MultiSetPartition([[1], [1, 1], [1, 2]]).standardize()
            {{1}, {2, 3}, {4, 5}}
            sage: MultiSetPartition([[1,1,2],[1,2],[1],[1]]).standardize()
            {{1}, {2}, {3, 4, 6}, {5, 7}}
        """
        cv = self.content_vector()
        adder = [sum(cv[:i]) for i in range(len(cv))]
        def inc(b):
            adder[b-1]+=1
            return adder[b-1]
        return SetPartition([[inc(a) for a in part] for part in self])

    def restrict(self, U):
        r"""
        Restrict a (multi-)set partition so that the elements are in a set

        INPUT:

        - ``U`` -- restrict a set, list or iterator

        OUTPUT:

        - a (multi-)set partition

        EXAMPLES::

            sage: msp = MultiSetPartition([[1], [1, 1], [1, 2]])
            sage: msp.restrict([2])
            [[2]]
            sage: msp.restrict([1])
            [[1], [1], [1, 1]]
            sage: spm = SetPartitionofMultiSet([[1],[1],[1,2],[1,2],[2]])
            sage: spm.restrict([1])
            [[1], [1], [1], [1]]
            sage: spm.restrict([2])
            [[2], [2], [2]]
        """
        MSP = self.parent().Element
        return MSP([[a for a in ms if a in U] for ms in self])

    def smash_product(self, other, shifted=True):
        r"""
        Dumb implementation of the product on (multi-)set partitions

        INPUT:

        - ``other`` -- a (multi-)set partition (same type as ``self``)
        - ``shifted`` -- (optional: default True) a boolean indicating if the
            content should be shifted by the maximum value in ``self``

        OUTPUT:

        - an iterator for the (multi-)set partitions such that the restriction
        to 1 to the max value of ``self`` is ``self`` and the restriction
        for values greater than max is ``other``

        EXAMPLES::

            sage: spm = SetPartitionofMultiSet([[1],[1,2],[2]])
            sage: list(spm.smash_product([[1]]))
            [[[1], [1, 2], [2], [3]],
             [[1], [1, 2, 3], [2]],
             [[1, 2], [1, 3], [2]],
             [[1], [1, 2], [2, 3]]]
            sage: msp = MultiSetPartition([[1,1],[1,2,2]])
            sage: list(msp.smash_product([[1],[1]]))
            [[[1, 1], [1, 2, 2], [3], [3]],
             [[1, 1, 3], [1, 2, 2], [3]],
             [[1, 1], [1, 2, 2, 3], [3]],
             [[1, 1, 3], [1, 2, 2, 3]]]
             sage: list(msp.smash_product([[1],[1]], shifted=False))
             [[[1], [1], [1, 1], [1, 2, 2]],
              [[1], [1, 1, 1], [1, 2, 2]],
              [[1], [1, 1], [1, 1, 2, 2]],
              [[1, 1, 1], [1, 1, 2, 2]]]
        """
        MSP = self.parent().Element
        cntself = self.content_vector()
        d = len(cntself)
        msp = MSP(other).raise_content(d)
        cntother = msp.content_vector()[d:]
        for theta in self.parent().__classcall_private__(\
          self.parent().parent(), cntself+cntother, self.parent()._key):
            if theta.restrict(range(1,d+1))==self \
              and theta.restrict(range(d+1, d+len(cntother)+1))==msp:
              if shifted:
                  yield theta
              else:
                  yield MSP([[i for i in S if i<=d]+[i-d for i in S if i>d]\
                  for S in theta])

class MultiSetPartition(MSP):
    r"""
    The element class of multi-set parititions.  These
    elements are in bijection with elements of ``VectorPartition``

    Here we will represent a multi-set as an ordered list with
    repeated elements, and a multi-set partition is an ordered
    list of lists

    Input a multi-set partition is a list of lists.  Each of the lists will
    be sorted and the list of lists will be sorted (currently using the default
    sort order)

    EXAMPLES::

        sage: msp=MultiSetPartition([[1,3],[1],[1,3],[2],[1,2],[1],[1,2],[1,3],[2]]); msp
        [[1], [1], [1, 2], [1, 2], [1, 3], [1, 3], [1, 3], [2], [2]]
        sage: msp.content_vector()
        [7, 4, 3]
        sage: msp.length()
        9
        sage: msp.size()
        14
        sage: msp.to_partition()
        [3, 2, 2, 2]
        sage: msp.to_composition()
        [2, 2, 3, 2]
        sage: msp.is_atomic()
        True
        sage: msp.to_vector_partition()
        [[0, 1, 0], [0, 1, 0], [1, 0, 0], [1, 0, 0], [1, 0, 1], [1, 0, 1], [1,
        0, 1], [1, 1, 0], [1, 1, 0]]
        sage: msp.pp()
        {1|1|12|12|13|13|13|2|2}
    """
    @staticmethod
    def __classcall_private__(cls, msp, key=None):
        """
        Create a multi-set partition.

        INPUT:

        - ``msp`` - a list of lists
        - ``key`` - a keyfunction for sorting the multiset partition (optional)

        The comparison function should have as input two multisets
        ``A`` and ``B`` and output ``int(-1)`` if ``A<B``, ``int(0)`` if
        ``A==B`` and ``int(1)`` if ``A>B``.

        EXAMPLES::

            sage: MultiSetPartition([[1,1,2], [2, 2, 1]])
            [[1, 1, 2], [1, 2, 2]]
            sage: MultiSetPartition([[1,1,2], [1],[2]])
            [[1], [1, 1, 2], [2]]

        Note that ``grlex_msp`` is defined in ``multisetpartition.py``::
            sage: MultiSetPartition([[1,1,2], [1],[2]],grlex_msp) 
            [[1], [2], [1, 1, 2]]
            sage: MultiSetPartition([[1,1,2], [2, 2, 1]]).parent()
            multi-set partitions with content vector [3, 3]
        """
        if msp==[]:
            vec = []
        else:
            cnt = sum(msp,[])
            m = max(cnt)
            vec = [cnt.count(i) for i in range(1,m+1)]
        MP = MultiSetPartitions(vec, key)
        return MP(msp)

    def is_coarser(self, other):
        r"""
        Test if ``self`` is coarser than ``other``

        INPUT:

        - ``other`` - a list of lists or a multiset partition

        OUTPUT:

        - boolean

        EXAMPLES::

            sage: MultiSetPartition([[1],[2,2,1]]).is_coarser([[1],[2],[1,2]])
            True
            sage: MultiSetPartition([[1],[2,2,1]]).is_coarser([[1],[1],[1,2]])
            False
            sage: MultiSetPartition([[1],[2,2,1]]).is_coarser([[1,2],[1,2]])
            False
            sage: Poset([MultiSetPartitions([2,1]), lambda x,y: x.is_coarser(y)])
            Finite poset containing 4 elements
        """
        if self==other:
            return True
        parent = self.parent()
        ot = parent(other)
        if ot.length()<self.length():
            return False
        sp = SetPartitions(ot.length(), self.length())
        return any(self==parent([sum((ot[i-1] for i in pt),[]) for pt in A]) for A in sp)

class SetPartitionofMultiSet(MSP):
    r"""
    The element class of set parititions of a multiset.  These
    elements are in bijection with elements of ``VectorPartition``

    Here we will represent a set as an ordered list with
    unque elements, and a set partition of a multiset is an ordered
    list of lists

    Input a multi-set partition is a list of lists.  Each of the lists will
    be sorted and the list of lists will be sorted (currently using the default
    sort order)

    EXAMPLES::

        sage: msp=MultiSetPartition([[1,3],[1],[1,3],[2],[1,2],[1],[1,2],[1,3],[2]]); msp
        [[1], [1], [1, 2], [1, 2], [1, 3], [1, 3], [1, 3], [2], [2]]
        sage: msp.content_vector()
        [7, 4, 3]
        sage: msp.length()
        9
        sage: msp.size()
        14
        sage: msp.to_partition()
        [3, 2, 2, 2]
        sage: msp.to_composition()
        [2, 2, 3, 2]
        sage: msp.is_atomic()
        True
        sage: msp.to_vector_partition()
        [[0, 1, 0], [0, 1, 0], [1, 0, 0], [1, 0, 0], [1, 0, 1], [1, 0, 1], [1,
        0, 1], [1, 1, 0], [1, 1, 0]]
        sage: msp.pp()
        {1|1|12|12|13|13|13|2|2}
    """
    @staticmethod
    def __classcall_private__(cls, msp, key=None):
        """
        Create a multi-set partition.

        INPUT:

        - ``msp`` - a list of lists
        - ``key`` - a comparison function on multisets (optional)

        The comparison function should have as input two multisets
        ``A`` and ``B`` and output ``int(-1)`` if ``A<B``, ``int(0)`` if
        ``A==B`` and ``int(1)`` if ``A>B``.

        EXAMPLES::

            sage: MultiSetPartition([[1,1,2], [2, 2, 1]])
            [[1, 1, 2], [1, 2, 2]]
            sage: MultiSetPartition([[1,1,2], [1],[2]])
            [[1], [1, 1, 2], [2]]

        Note that ``grlex_msp`` is defined in ``multisetpartition.py``::
            sage: MultiSetPartition([[1,1,2], [1],[2]],grlex_msp) 
            [[1], [2], [1, 1, 2]]
            sage: MultiSetPartition([[1,1,2], [2, 2, 1]]).parent()
            multi-set partitions with content vector [3, 3]
        """
        if msp==[]:
            vec = []
        else:
            cnt = sum(msp,[])
            m = max(cnt)
            vec = [cnt.count(i) for i in range(1,m+1)]
        MP = SetPartitionsofMultiSet(vec, key)
        return MP(msp)

class MSPsofMultiSet(UniqueRepresentation, Parent):
    def __init__(self, vec, key=None, is_finite=True):
        r"""
        Initialize ``self``

        INPUT:

        - ``vec`` - a list indicating the content of the multisets
        - ``key`` - a comparison function on multisets (optional)

        The comparison function should have as input two multisets
        ``A`` and ``B`` and output ``int(-1)`` if ``A<B``, ``int(0)`` if
        ``A==B`` and ``int(1)`` if ``A>B``.

        TESTS::

            sage: MP = MultiSetPartitions([2, 2])
            sage: TestSuite(MP).run(skip=["_test_pickling", "_test_elements"])
        """
        if vec is not None:
            self._vec = vec
        self._key = key
        if is_finite:
            Parent.__init__(self, category = FiniteEnumeratedSets())
        else:
            Parent.__init__(self, category = InfiniteEnumeratedSets())

    def _element_constructor_(self, msp):
        r"""
        Construct an element of ``self``.

        EXAMPLES::

            sage: MP = MultiSetPartitions([2, 2])
            sage: elt = MP([[1, 2], [1, 2]]); elt
            [[1, 2], [1, 2]]
            sage: elt.parent() is MP
            True
        """
        return self.element_class(self, msp)

    def content_vector(self):
        r"""
        The list whose `i^{th}` entry is the number of `i+1`s in
        the multi-set partitions

        EXAMPLES::

            sage: MultiSetPartitions([3,2]).content_vector()
            [3, 2]
        """
        return list(self._vec)

    @staticmethod
    def from_vector_partition(self, llaa):
        r"""
        convert a vector partition to a multi-set partition

        Note that sometimes vector partitions are called multi-partitions

        INPUT:

        - ``llaa`` - a multi-partition or a vector partition

        EXAMPLES::

            sage: msp = MultiSetPartitions([2,1])
            sage: [msp.from_vector_partition(msp,v) for v in VectorPartitions([2,1])]
            [[[1], [1], [2]], [[1, 1], [2]], [[1], [1, 2]], [[1, 1, 2]]]
        """
        return self.element_class(self, [[i+1 for i in range(len(la))
            for j in range(la[i])] for la in llaa])

class BiSetPartition(MSP):
    r"""
    The element class of bi-set parititions.

    A bi-set partition is a list of sets of positive and negative entries
    (each set is represented as a an ordered list).  Each set may contain
    at most one negative entry.

    Input a bi-set partition is a list of lists.  Each of the lists will
    be sorted and the list of lists will be sorted (currently using the default
    sort order)

    EXAMPLES::

        sage: bsp=BiSetPartition([[1,-1,2],[-1,1],[1,-1],[1,2,3],[-2,3]]); bsp
        [[-2, 3], [-1, 1], [-1, 1, 2], [1, 2, 3]]
        sage: bsp.parent()
        bi-set partitions with content vectors [4, 2, 2] and [3, 1]
        sage: bsp.content_vector()
        [[4, 2, 2], [3, 1]]
        sage: bsp.length()
        5
        sage: bsp.size()
        12
        sage: bsp.to_partition()
        [2, 1, 1, 1]
        sage: bsp.to_composition()
        [1, 2, 1, 1]
        sage: bsp.is_atomic()
        True
        sage: bsp.to_vector_partition()
        [[0, 0, 1, 0, 1], [1, 0, 0, 1, 0], [1, 0, 0, 1, 0], [1, 1, 0, 1, 0], [1, 1, 1, 0, 0]]
        sage: bsp.pp()
        {-23|-11|-11|-112|123}
    """
    @staticmethod
    def __classcall_private__(cls, msp, key=None):
        """
        Create a bi-set partition.

        INPUT:

        - ``msp`` - a list of lists
        - ``key`` - a comparison function on sets (optional)

        The comparison function should have as input two sets
        ``A`` and ``B`` and output ``int(-1)`` if ``A<B``, ``int(0)`` if
        ``A==B`` and ``int(1)`` if ``A>B``.

        EXAMPLES::

            sage: BiSetPartition([[1,2],[2,1]])
            [[1, 2], [1, 2]]
            sage: BiSetPartition([[-1,1,2],[1],[2]])
            [[-1, 1, 2], [1], [2]]

        Note that ``rlex_bsp`` is defined in ``msp.py``::
            sage: BiSetPartition([[-1,1,2],[1],[2]],rlex_bsp)
            [[1], [2], [-1, 1, 2]]
            sage: BiSetPartition([[-1,1,2],[1],[2]],rlex_bsp).parent()
            bi-set partitions with content vectors [2, 2] and [1] with an order on sets specified
        """
        if msp==[]:
            vec1 = []
            vec2 = []
        else:
            cnt = sum(msp,[])
            m = max(cnt)
            vec1 = [cnt.count(i) for i in range(1,m+1)]
            r = min(cnt)
            vec2 = [cnt.count(i) for i in range(r,0)][::-1]
        MP = BiSetPartitions(vec1, vec2, key)
        return MP(msp)

    def to_vector_partition(self):
        r"""
        A ``VectorPartition`` object equivalent to the bi-set partition

        The positive entries are first and the negative are represented
        by the parts of the vector partition after.

        EXAMPLES::

            sage: [bsp.to_vector_partition() for bsp in BiSetPartitions([2],[2])]
            [[[0, 1], [0, 1], [1, 0], [1, 0]], [[0, 1], [1, 0], [1, 1]], [[1, 1], [1, 1]]]
        """
        m = len(self.parent()._vec1)
        return VectorPartition([[A.count(i) for i in range(1,m+1)]+\
          [A.count(-i) for i in range(1,len(self.parent()._vec2)+1)] \
          for A in self])

class BiSetPartitions(MSPsofMultiSet):
    r"""
    The class of bi-set partitions of a multi-set

    The sets of a bi-set partition have entries which are either ``1``
    through ``k`` or ``-1`` through ``-r``.  There is at most one negative
    entry in each set.  The sets are ordered in increasing order.

    Input a bi-set partition as a list of lists.  Each of the lists will
    be sorted and the list of lists will be sorted using the comparison
    function.

    Note that this class is in bijection with a subset of ``VectorPartitions``
    and it uses that class to make construct the list of bi-set partitions

    EXAMPLES::

        sage: BiSetPartitions([3,2,1],[1,2])
        bi-set partitions with content vectors [3, 2, 1] and [1, 2]
        sage: BiSetPartitions([3,2,1],[1,2]).cardinality()
        281
        sage: BiSetPartitions([2],[2,1]).list()

        [[[-2], [-1], [-1], [1], [1]],
         [[-2], [-1], [-1, 1], [1]],
         [[-2], [-1, 1], [-1, 1]],
         [[-2, 1], [-1], [-1], [1]],
         [[-2, 1], [-1], [-1, 1]]]
        sage: BiSetPartitions([2,1],[2]).list()

        [[[-1], [-1], [1], [1], [2]],
         [[-1], [-1], [1], [1, 2]],
         [[-1], [-1, 1], [1], [2]],
         [[-1], [-1, 2], [1], [1]],
         [[-1], [-1, 1, 2], [1]],
         [[-1], [-1, 1], [1, 2]],
         [[-1, 1], [-1, 1], [2]],
         [[-1, 1], [-1, 2], [1]],
         [[-1, 1], [-1, 1, 2]]]
    """
    def __init__(self, vec1, vec2, key=None):
        r"""
        Initialize ``self``

        INPUT:

        - ``vec1``, ``vec2`` - lists indicating the content of the sets
        - ``key`` - a comparison function on sets (optional)

        The comparison function should have as input two sets
        ``A`` and ``B`` and output ``int(-1)`` if ``A<B``, ``int(0)`` if
        ``A==B`` and ``int(1)`` if ``A>B``.

        TESTS::

            sage: BSP = BiSetPartitions([2, 2])
            sage: TestSuite(BSP).run(skip=["_test_pickling", "_test_elements"])
        """
        self._vec1 = vec1
        self._vec2 = vec2
        self._key = key
        Parent.__init__(self, category = FiniteEnumeratedSets())

    @staticmethod
    def __classcall_private__(cls, vec1, vec2, key=None):
        r"""
        Create the class of bi-set partitions of content ``vec1`` and ``vec2``

        INPUT:

        - ``vec1``, ``vec2`` - lists indicating the content of the sets
        - ``key`` - a comparison function on sets (optional)

        The comparison function should have as input two sets
        ``A`` and ``B`` and output ``int(-1)`` if ``A<B``, ``int(0)`` if
        ``A==B`` and ``int(1)`` if ``A>B``.

        EXAMPLES::

            sage: BiSetPartitions([3,2,1],[1,2])
            bi-set partitions with content vectors [3, 2, 1] and [1, 2]
        """
        return super(BiSetPartitions, cls).__classcall__(cls, tuple(vec1), tuple(vec2), key)

    def __repr__(self):
        r"""
        EXAMPLES::

            sage: BiSetPartitions([1,0,2,4],[0,1])
            bi-set partitions with content vectors [1, 0, 2, 4] and [0, 1]
            sage: BiSetPartitions([2],[2],rlex_bsp)
            bi-set partitions with content vectors [2] and [2] with an order on sets specified
        """
        extra = ''
        if self._key is not None:
            extra = ' with an order on sets specified'
        return 'bi-set partitions with content vectors %s and %s'%(list(self._vec1),list(self._vec2))+extra

    Element = BiSetPartition

    def __iter__(self):
        r"""
        Iterator for bi-set partitions.

        EXAMPLES::

            sage: BiSetPartitions([2],[2]).list()
            [[[-1], [-1], [1], [1]], [[-1], [-1, 1], [1]], [[-1, 1], [-1, 1]]]
            sage: BiSetPartitions([2,1],[1]).cardinality()
            6
        """
        if all(coord == 0 for coord in self._vec1+self._vec2):
            yield self.element_class(self, []) # the zero vector has only the empty partition
        else:
            for llaa in VectorPartitions(self._vec1+self._vec2):
                if max(flatten(llaa))<=1 and all(sum(A[len(self._vec1):])<=1 for A in llaa):
                    yield self.from_vector_partition(llaa)

    def content_vector(self):
        r"""
        The contect vectors of the bi-set partitions in the class

        A list of two lists, the first is the content of the positive
        entries, the second is the content of the negative entries

        EXAMPLES::

            sage: BiSetPartitions([3,2],[1,2]).content_vector()
            [[3, 2], [1, 2]]
        """
        return [list(self._vec1),list(self._vec2)]

    def from_vector_partition(self, llaa):
        r"""
        convert a vector partition to a bi-set partition

        INPUT:

        - ``llaa`` - a vector partition

        Note: we do not check for good input that the vector partition has
        entries <= 1 and that at most one of the entries representing the
        negative ones are equal to 1

        EXAMPLES::

            sage: bsp = BiSetPartitions([1],[1])
            sage: [bsp.from_vector_partition(v) for v in VectorPartitions([1,1])]
            [[[-1], [1]], [[-1, 1]]]
        """
        ell = len(self._vec1)
        k = len(self._vec2)
        return self.element_class(self, [[i+1 for i in range(ell) if la[i]]+
          [-i for i in range(1,k+1) if la[i+ell-1]] for la in llaa])

class MCPartition(MSP):
    r"""
    The element class of multiset common parititions (or MC partitions).

    An MC partition is a list of multisets of positive and negative entries
    (each multiset is represented as a an ordered list).  Each multiset may
    contain at most one negative entry.

    Input a MC partition is a list of lists.  Each of the lists will
    be sorted and the list of lists will be sorted (currently using the default
    sort order).

    This class of tableaux occurs in the paper [OZ17]_

    EXAMPLES::

        sage: mcp=MCPartition([[1,1,-1,2],[-1,1],[1,-1],[1,3,3],[-2,3]]); mcp
        [[-2, 3], [-1, 1], [-1, 1], [-1, 1, 1, 2], [1, 3, 3]]
        sage: mcp.parent()
        multiset common (MC) partitions with content vectors [5, 1, 3] and [3, 1]
        sage: mcp.content_vector()
        [[5, 1, 3], [3, 1]]
        sage: mcp.length()
        5
        sage: mcp.size()
        13
        sage: mcp.to_partition()
        [2, 1, 1, 1]
        sage: mcp.to_composition()
        [1, 2, 1, 1]
        sage: mcp.is_atomic()
        True
        sage: mcp.to_vector_partition()
        [[0, 0, 1, 0, 1], [1, 0, 0, 1, 0], [1, 0, 0, 1, 0], [1, 0, 2, 0, 0], [2, 1, 0, 1, 0]]
        sage: mcp.pp()
        {-23|-11|-11|-1112|133}
    """
    @staticmethod
    def __classcall_private__(cls, msp, key=None):
        """
        Create a multiset common partition.

        INPUT:

        - ``msp`` -- a list of lists
        - ``key`` -- a comparison function on sets (optional)

        The comparison function should have as input two sets
        ``A`` and ``B`` and output ``int(-1)`` if ``A<B``, ``int(0)`` if
        ``A==B`` and ``int(1)`` if ``A>B``.

        EXAMPLES::

            sage: MCPartition([[1,1,2],[1,2,1]])
            [[1, 1, 2], [1, 1, 2]]
            sage: MCPartition([[1,2,-1],[1],[2]])
            [[-1, 1, 2], [1], [2]]
            sage: MCPartition([[1,2,-1,-2],[1,-1],[2]]) # warning does not check for bad input
            [[-2, -1, 1, 2], [-1, 1], [2]]

        Note that ``rlex_bsp`` is defined in ``msp.py``::

            sage: MCPartition([[-1,1,2],[1],[2]],rlex_bsp)
            [[1], [2], [-1, 1, 2]]
            sage: MCPartition([[-1,1,2],[1],[2]],rlex_bsp).parent()
            multiset common (MC) partitions with content vectors [2, 2] and [1] with an order on sets specified
        """
        if msp==[]:
            vec1 = []
            vec2 = []
        else:
            cnt = sum(msp,[])
            m = max(cnt)
            vec1 = [cnt.count(i) for i in range(1,m+1)]
            r = min(cnt)
            vec2 = [cnt.count(i) for i in range(r,0)][::-1]
        MP = MCPartitions(vec1, vec2, key)
        return MP(msp)

    def to_vector_partition(self):
        r"""
        A ``VectorPartition`` object equivalent to the MC partition

        The positive entries are first and the negative are represented
        by the parts of the vector partition after.

        EXAMPLES::

            sage: [mcp.to_vector_partition() for mcp in MCPartitions([2],[2])]
            [[[0, 1], [0, 1], [1, 0], [1, 0]],
             [[0, 1], [0, 1], [2, 0]],
             [[0, 1], [1, 0], [1, 1]],
             [[0, 1], [2, 1]],
             [[1, 1], [1, 1]]]
        """
        m = len(self.parent()._vec1)
        return VectorPartition([[A.count(i) for i in range(1,m+1)]+\
          [A.count(-i) for i in range(1,len(self.parent()._vec2)+1)] \
          for A in self])

class MCPartitions(MSPsofMultiSet):
    r"""
    The class of multiset common (MC) partitions of a multi-set

    The multisets of an MC partition have entries which are either ``1``
    through ``k`` or ``-1`` through ``-r``.  There is at most one negative
    entry in each set.  The multisets are ordered in increasing order.

    Input an MC partition as a list of lists.  Each of the lists will
    be sorted and the list of lists will be sorted using the comparison
    function.

    Note that this class is in bijection with a subset of ``VectorPartitions``
    and it uses that class to make construct the list of MC partitions

    EXAMPLES::

        sage: MCPartitions([3,2,1],[1,2])
        multiset common (MC) partitions with content vectors [3, 2, 1] and [1, 2]
        sage: MCPartitions([3,2,1],[1,2]).cardinality()
        1067
        sage: MCPartitions([2],[2,1]).list()

        [[[-2], [-1], [-1], [1], [1]],
         [[-2], [-1], [-1], [1, 1]],
         [[-2], [-1], [-1, 1], [1]],
         [[-2], [-1], [-1, 1, 1]],
         [[-2], [-1, 1], [-1, 1]],
         [[-2, 1], [-1], [-1], [1]],
         [[-2, 1, 1], [-1], [-1]],
         [[-2, 1], [-1], [-1, 1]]]
        sage: MCPartitions([2,1],[2]).list()

        [[[-1], [-1], [1], [1], [2]],
         [[-1], [-1], [1, 1], [2]],
         [[-1], [-1], [1], [1, 2]],
         [[-1], [-1], [1, 1, 2]],
         [[-1], [-1, 1], [1], [2]],
         [[-1], [-1, 1, 1], [2]],
         [[-1], [-1, 2], [1], [1]],
         [[-1], [-1, 2], [1, 1]],
         [[-1], [-1, 1, 2], [1]],
         [[-1], [-1, 1], [1, 2]],
         [[-1], [-1, 1, 1, 2]],
         [[-1, 1], [-1, 1], [2]],
         [[-1, 1], [-1, 2], [1]],
         [[-1, 1, 1], [-1, 2]],
         [[-1, 1], [-1, 1, 2]]]
    """
    def __init__(self, vec1, vec2, key=None):
        r"""
        Initialize ``self``

        INPUT:

        - ``vec1``, ``vec2`` - lists indicating the content of the sets
        - ``key`` - a comparison function on sets (optional)

        The comparison function should have as input two sets
        ``A`` and ``B`` and output ``int(-1)`` if ``A<B``, ``int(0)`` if
        ``A==B`` and ``int(1)`` if ``A>B``.

        TESTS::

            sage: MCP = MCPartitions([2, 2],[2])
            sage: TestSuite(MCP).run(skip=["_test_pickling", "_test_elements"])
        """
        self._vec1 = vec1
        self._vec2 = vec2
        self._key = key
        Parent.__init__(self, category = FiniteEnumeratedSets())

    @staticmethod
    def __classcall_private__(cls, vec1, vec2, key=None):
        r"""
        Create the class of MC partitions of content ``vec1`` and ``vec2``

        INPUT:

        - ``vec1``, ``vec2`` - lists indicating the content of the sets
        - ``key`` - a comparison function on sets (optional)

        The comparison function should have as input two sets
        ``A`` and ``B`` and output ``int(-1)`` if ``A<B``, ``int(0)`` if
        ``A==B`` and ``int(1)`` if ``A>B``.

        EXAMPLES::

            sage: MCPartitions([3,2,1],[1,2])
            multiset common (MC) partitions with content vectors [3, 2, 1] and [1, 2]
        """
        return super(MCPartitions, cls).__classcall__(cls, tuple(vec1), tuple(vec2), key)

    def __repr__(self):
        r"""
        EXAMPLES::

            sage: MCPartitions([1,0,2,4],[0,1])
            multiset common (MC) partitions with content vectors [1, 0, 2, 4] and [0, 1]
            sage: MCPartitions([2],[2],rlex_bsp)
            multiset common (MC) partitions with content vectors [2] and [2] with an order on sets specified
        """
        extra = ''
        if self._key is not None:
            extra = ' with an order on sets specified'
        return 'multiset common (MC) partitions with content vectors %s and %s'%(list(self._vec1),list(self._vec2))+extra

    Element = MCPartition

    def __iter__(self):
        r"""
        Iterator for MC partitions.

        EXAMPLES::

            sage: MCPartitions([2],[2]).list()

            [[[-1], [-1], [1], [1]],
             [[-1], [-1], [1, 1]],
             [[-1], [-1, 1], [1]],
             [[-1], [-1, 1, 1]],
             [[-1, 1], [-1, 1]]]
            sage: MCPartitions([2,1],[1]).cardinality()
            11
        """
        if all(coord == 0 for coord in self._vec1+self._vec2):
            yield self.element_class(self, []) # the zero vector has only the empty partition
        else:
            for llaa in VectorPartitions(self._vec1+self._vec2):
                if all(sum(A[len(self._vec1):])<=1 for A in llaa):
                    yield self.from_vector_partition(llaa)

    def content_vector(self): # note that this could be common with bi-set partitions
        r"""
        The contect vectors of the MC partitions in the class

        A list of two lists, the first is the content of the positive
        entries, the second is the content of the negative entries

        EXAMPLES::

            sage: MCPartitions([3,2],[1,2]).content_vector()
            [[3, 2], [1, 2]]
        """
        return [list(self._vec1),list(self._vec2)]

    def from_vector_partition(self, llaa): # note that this could be common with bi-set partitions
        r"""
        convert a vector partition to an MC partition

        INPUT:

        - ``llaa`` - a vector partition

        Note: we do not check for good input that the vector partition has
        at most one of the entries representing the negative ones are equal to 1

        EXAMPLES::

            sage: MCP = MCPartitions([1],[1])
            sage: [MCP.from_vector_partition(v) for v in VectorPartitions([1,1])]
            [[[-1], [1]], [[-1, 1]]]
        """
        ell = len(self._vec1)
        k = len(self._vec2)
        return self.element_class(self, [sum(([i+1]*la[i] for i in range(ell)),[])+
          [-i for i in range(1,k+1) if la[i+ell-1]] for la in llaa])

class MultiSetPartitions(MSPsofMultiSet):
    r"""
    The class of multi-set partitions of a multi-set

    Here we will represent a multi-set as an ordered list with
    repeated elements, and a multi-set partition is an ordered
    list of lists

    Input a multi-set partition is a list of lists.  Each of the lists will
    be sorted and the list of lists will be sorted (currently using the default
    sort order)

    Note that this class is in bijection with ``VectorPartitions`` and it uses
    that class to make construct the list of multi-set partitions

    EXAMPLES::

        sage: MultiSetPartitions([2,2])
        multi-set partitions with content vector [2, 2]
        sage: MultiSetPartitions([2,2]).cardinality()
        9
        sage: MultiSetPartitions([2,2]).list()
        [[[1], [1], [2], [2]],
         [[1, 1], [2], [2]],
         [[1], [1, 2], [2]],
         [[1, 1, 2], [2]],
         [[1], [1], [2, 2]],
         [[1, 1], [2, 2]],
         [[1], [1, 2, 2]],
         [[1, 2], [1, 2]],
         [[1, 1, 2, 2]]]
        sage: ht = SymmetricFunctions(QQ).induced_trivial_character()
        sage: h = SymmetricFunctions(QQ).complete()
        sage: ht(h[4,3,1]).coefficient([1,1])
        19
        sage: len(filter(lambda msp: msp.to_partition()==[1,1],MultiSetPartitions([4,3,1])))
        19

    The default order for displaying multiset partitions is lexicographic,
    but we could reorder the multi-sets for combinatorial reasons.
    There is an optional comparison function that can be specifed.

    A function ``grlex_msp`` is defined in this file as an example.::

        sage: for msp in MultiSetPartitions([2,2],grlex_msp):
        ....:     msp.pp()
        {1|1|2|2}
        {2|2|11}
        {1|2|12}
        {2|112}
        {1|1|22}
        {11|22}
        {1|122}
        {12|12}
        {1122}
    """
    @staticmethod
    def __classcall_private__(cls, vec=None, key=None):
        r"""
        Create the class of multiset partitions of content ``vec``

        INPUT:

        - ``vec`` - a list indicating the content of the multisets
        - ``key`` - a comparison function on multisets (optional)

        The comparison function should have as input two multisets
        ``A`` and ``B`` and output ``int(-1)`` if ``A<B``, ``int(0)`` if
        ``A==B`` and ``int(1)`` if ``A>B``.

        EXAMPLES::

            sage: MultiSetPartitions([2, 1])
            multi-set partitions with content vector [2, 1]
        """
        if vec is None:
            return _MultiSetPartitions_all()
        if isinstance(vec, (list, tuple)) and \
            all(isinstance(a, (int, Integer)) for a in vec) and \
            all(a>=0 for a in vec):
            return super(MultiSetPartitions, cls).__classcall__(cls, tuple(vec), key)
        else:
            raise ValueError("%s must be a vector of non-negative integers"%vec)

    def __repr__(self):
        r"""
        EXAMPLES::

            sage: MultiSetPartitions([1,0,2,4])
            multi-set partitions with content vector [1, 0, 2, 4]
        """
        extra = ''
        if self._key is not None:
            extra = ' with an order on multisets specified'
        return 'multi-set partitions with content vector %s'%(list(self._vec))+extra

    Element = MultiSetPartition

    def __iter__(self):
        r"""
        Iterator for multi-set partitions.

        EXAMPLES::

            sage: MultiSetPartitions([2,1]).list()
            [[[1], [1], [2]], [[1, 1], [2]], [[1], [1, 2]], [[1, 1, 2]]]
            sage: MultiSetPartitions([2, 2]).cardinality()
            9
        """
        if all(coord == 0 for coord in self._vec):
            yield self.element_class(self, []) # the zero vector has only the empty partition
        else:
            for llaa in VectorPartitions(self._vec):
                yield self.from_vector_partition(self, llaa)

class _MultiSetPartitions_all(MultiSetPartitions):
    def __init__(self):
        """
        Initialize ``self``.

        TESTS::

            sage: MultiSPs = MultiSetPartitions()
            sage: TestSuite(MultiSPs).run()
        """
        MultiSetPartitions.__init__(self, None, None, False)

    def __repr__(self):
        """
        Return a string representation of ``self``.

        TESTS::

            sage: repr(MultiSetPartitions())
            'MultiSetPartitions'
        """
        return "MultiSetPartitions"

    def __iter__(self):
        NotImplemented

class SetPartitionsofMultiSet(MSPsofMultiSet):
    r"""
    The class of set partitions of a multi-set

    Here we will represent a set as an ordered list with no
    repeated elements, and a set partition of a multi-set is an ordered
    list of these sets with no repeated elements

    Input a set partition is a list of lists.  Each of the lists will be
    sorted and the list of lists will be sorted (currently using the default
    sort order)

    Note that this class is in bijection with ``VectorPartitions`` with the
    maximum part of the vector partition is 1.  It uses
    that class to make construct the list of multi-set partitions

    EXAMPLES::

        sage: SetPartitionsofMultiSet([2,2])
        set partitions of a multi-set with content vector [2, 2]
        sage: SetPartitionsofMultiSet([2,2]).cardinality()
        3
        sage: SetPartitionsofMultiSet([2,2]).list()
        [[[1], [1], [2], [2]], [[1], [1, 2], [2]], [[1, 2], [1, 2]]]

    The default order for displaying multiset partitions is lexicographic,
    but we could reorder the multi-sets for combinatorial reasons.
    There is an optional comparison function that can be specifed.

    A function ``grlex_msp`` is defined in this file as an example.::

        sage: for msp in SetPartitionsofMultiSet([2,2,2],grlex_msp):
        ....:     msp.pp()
        ....: 
        {1|1|2|2|3|3}
        {1|2|3|3|12}
        {3|3|12|12}
        {1|2|2|3|13}
        {1|1|2|3|23}
        {1|2|3|123}
        {2|3|12|13}
        {1|3|12|23}
        {3|12|123}
        {2|2|13|13}
        {1|2|13|23}
        {2|13|123}
        {1|1|23|23}
        {1|23|123}
        {12|13|23}
        {123|123}
    """
    @staticmethod
    def __classcall_private__(cls, vec, key=None):
        r"""
        Create the class of multiset partitions of content ``vec``

        INPUT:

        - ``vec`` - a list indicating the content of the multisets
        - ``key`` - a comparison function on multisets (optional)

        The comparison function should have as input two multisets
        ``A`` and ``B`` and output ``int(-1)`` if ``A<B``, ``int(0)`` if
        ``A==B`` and ``int(1)`` if ``A>B``.

        EXAMPLES::

            sage: SetPartitionsofMultiSet([2, 1])
            set partitions of a multi-set with content vector [2, 1]
        """
        return super(SetPartitionsofMultiSet, cls).__classcall__(cls, tuple(vec), key)

    def __repr__(self):
        r"""
        EXAMPLES::

            sage: SetPartitionsofMultiSet([1,0,2,4])
            set partitions of a multi-set with content vector [1, 0, 2, 4]
        """
        extra = ''
        if self._key is not None:
            extra = ' with an order on multisets specified'
        return 'set partitions of a multi-set with content vector %s'%(list(self._vec))+extra

    Element = SetPartitionofMultiSet

    def __iter__(self):
        r"""
        Iterator for multi-set partitions.

        EXAMPLES::

            sage: SetPartitionsofMultiSet([2,1]).list()
            [[[1], [1], [2]], [[1], [1, 2]]]
            sage: SetPartitionsofMultiSet([2, 2]).cardinality()
            3
        """
        if all(coord == 0 for coord in self._vec):
            yield self.element_class(self, []) # the zero vector has only the empty partition
        else:
            for llaa in VectorPartitions(self._vec):
                if max(flatten(llaa))<=1:
                    yield self.from_vector_partition(self, llaa)

#------------------------------------
#Key functions
#------------------------------------
def clean_msp(item):
    r"""
    Clean up item so that all the entries are positive (but those that
    were already positive are now > 1000
    """
    return [-a for a in item if a<=0]+[a+1000 for a in item if a>0]

def key_lex(item):
    r"""
    Key function for sorting: lex order on multisets

    EXAMPLES::

        sage: sorted([[1,1,2],[2],[1],[1,2],[1,1]], key=key_lex)
        [[1], [1, 1], [1, 1, 2], [1, 2], [2]]
    """
    return sorted(clean_msp(item))

def key_rlex(item):
    r"""
    Key function for sorting: lex order on multisets

    EXAMPLES::

        sage: sorted(([[1,1,2],[2],[1],[1,2],[1,1]], key=key_rlex)
        [[1], [1, 1], [2], [1, 2], [1, 1, 2]]
        sage: sorted([[1,2,2],[1,1,2],[1,2,3],[2,1,3],[1,1],[1,2],[1]], key=key_rlex)
        [[1], [1, 1], [1, 2], [1, 1, 2], [1, 2, 2], [2, 1, 3], [1, 2, 3]]
    """
    return sorted(clean_msp(item))[::-1]

def key_grlex(item):
    r"""
    This is an example of a comparsion function on the multisets

    EXAMPLES::

        sage: sorted([[2,3],[1,3],[2,2],[1,2],[1,1]], key=key_grlex)
        [[1, 1], [1, 2], [1, 3], [2, 2], [2, 3]]
        sage: sorted([[1,2,2],[1,1,3],[2],[1],[1,2],[1,1]], key=key_grlex)
        [[1], [2], [1, 1], [1, 2], [1, 1, 3], [1, 2, 2]]
    """
    return [len(item)]+sorted(clean_msp(item))

def key_grrlex(item):
    r"""
    This is an example of a comparsion function on the multisets

    EXAMPLES::

        sage: sorted([[2,3],[1,3],[2,2],[1,2],[1,1]], key=key_grrlex)
        [[1, 1], [1, 2], [2, 2], [1, 3], [2, 3]]
        sage: sorted([[1,2,2],[1,1,3],[2],[1],[1,2],[1,1]], key=key_grrlex)
        [[1], [2], [1, 1], [1, 2], [1, 2, 2], [1, 1, 3]]
    """
    return [len(item)]+sorted(clean_msp(item))[::-1]

#------------------------------------
#Below here are comparison functions which all need to be turned into key functions
# for compatibility with python3
#------------------------------------


def rlex_bsp( A, B ):
    r"""
    This is an example of a comparsion function on the multisets

    EXAMPLES::

        sage: sorted([[1,1,2],[2],[1],[1,2],[1,1],[-1],[-2],[1,1,-1],[1,1,-2],[1,-1],[1,-1],[1,-2]], key=key_rlex_bsp)
        [[-1],
         [-2],
         [1],
         [1, -1],
         [1, -1],
         [1, -2],
         [1, 1],
         [1, 1, -1],
         [1, 1, -2],
         [2],
         [1, 2],
         [1, 1, 2]]
    """
    if A==B:
        return int(0)
    pA=[a for a in A if a>0]
    pB=[b for b in B if b>0]
    if pA==pB:
        if min(A)<min(B):
            return int(1)
        else:
            return int(-1)
    if pA[::-1]<pB[::-1]:
        return int(-1)
    else:
        return int(1)

def last_letter_order_msp( A, B ):
    r"""
    EXAMPLES::
        sage: sorted([[1,1,2],[2],[1],[1,2],[1,1],[-1],[-2],[1,1,-1],[1,1,-2],[1,-1],[1,-1],[1,-2]], key=key_last_letter_order_msp)
        [[-1],
         [-2],
         [1],
         [1, -1],
         [1, -1],
         [1, -2],
         [1, 1],
         [1, 1, -1],
         [1, 1, -2],
         [1, 1, 2],
         [2],
         [1, 2]]
    """
    A = sorted(A)
    B = sorted(B)
    if len(A)==0:
        return int(-1)
    if len(B)==0:
        return int(1)
    if B[-1]>0 and A[-1]<0:
        return int(-1)
    if B[-1]<0 and A[-1]>0:
        return int(1)
    if B[-1]<0 and A[-1]<0:
        return last_letter_order_msp([-a for a in A], [-b for b in B])
    if A[-1]<B[-1]:
        return int(-1)
    if A[-1]>B[-1]:
        return int(1)
    if A[-1]==B[-1]:
        return last_letter_order_msp(A[:-1],B[:-1])

def grlex_msp( A, B ):
    r"""
    This is an example of a comparsion function on the multisets

    EXAMPLES::

        sage: sorted([[2,3],[1,3],[2,2],[1,2],[1,1]], key=key_grlex_msp)
        [[1, 1], [1, 2], [1, 3], [2, 2], [2, 3]]
        sage: sorted([[1,2,2],[1,1,3],[2],[1],[1,2],[1,1]], key=key_grlex_msp)
        [[1], [2], [1, 1], [1, 2], [1, 1, 3], [1, 2, 2]]
    """
    if A==B:
        return int(0)
    if len(A)<len(B):
        return int(-1)
    if len(A)==len(B) and A<B:
        return int(-1)
    else:
        return int(1)

def gr_rev_lex_msp( A, B ):
    r"""
    This is an example of a comparsion function on the multisets

    EXAMPLES::

        sage: sorted([[2,3],[1,3],[2,2],[1,2],[1,1]], key=key_gr_rev_lex_msp)
        [[1, 1], [1, 2], [2, 2], [1, 3], [2, 3]]
        sage: sorted([[1,2,2],[1,1,3],[2],[1],[1,2],[1,1]], key=key_gr_rev_lex_msp)
        [[1], [2], [1, 1], [1, 2], [1, 2, 2], [1, 1, 3]]
    """
    if A==B:
        return int(0)
    if len(A)<len(B):
        return int(-1)
    if len(A)==len(B) and list(reversed(A))<list(reversed(B)):
        return int(-1)
    else:
        return int(1)

def rev_gr_revlex_msp( A, B ):
    r"""
    This is an example of a comparsion function on the multisets

    EXAMPLES::

        sage: sorted([[2,3],[1,3],[2,2],[1,2],[1,1]], key=key_rev_gr_revlex_msp)
        [[2, 3], [1, 3], [2, 2], [1, 2], [1, 1]]
        sage: sorted([[1,2,2],[1,1,3],[2],[1],[1,2],[1,1]], key=key_rev_gr_revlex_msp)
        [[1], [2], [1, 2], [1, 1], [1, 1, 3], [1, 2, 2]]
    """
    if A==B:
        return int(0)
    if len(A)<len(B):
        return int(-1)
    if mod(len(A),2)==1 and len(A)==len(B) and list(A)<list(B):
        return int(-1)
    if mod(len(A),2)==0 and len(A)==len(B) and list(reversed(A))>list(reversed(B)):
        return int(-1)
    else:
        return int(1)
