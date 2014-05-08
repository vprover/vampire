/**
 * @file List.hpp
 * Implements class List<C> for lists.
 * @since 05/05/1999 Manchester
 * @since 29/05/1999 Manchester: setHead, setTail and conc added
 * @since 06/08/1999 moved from KK to Sat
 * @since 25/09/1999 Uppsala: lots of modifications
 * @since 17/10/1999 Manchester: moved back to kk
 * @since 26/02/2000 Manchester, inserted into library
 * @since 14/05/2000 Dallas, function length added
 * @since 15/05/2000 Dallas, function member added
 * @since 29/05/2000 Manchester, isNonEmpty added
 * @since 01/06/2000 Manchester, second added
 * @since 04/06/2000 Manchester, remove added
 * @since 04/06/2000 Manchester, nth() added
 * @since 10/12/2000 Manchester, class Iterator added
 * @since 17/12/2000 Manchester, Iterator::reset added
 * @since 02/01/2001 Manchester, addLast added
 * @since 07/01/2001 Manchester, pop changed to return a value
 * @since 29/03/2001 Manchester, two small bugs fixed
 * @since 09/05/2001 Manchester, DelIterator introduced
 * @since 05/05/2001 Manchester, deleteNth ()
 * @since 30/05/2001 Manchester, split
 * @since 30/05/2001 Manchester, append
 * @since 04/06/2001 Manchester, DelIterator::restore
 * @since 02/12/2003, Manchester, allocation changed to use Allocator
 */

#ifndef __list__
#  define __list__


#include "Forwards.hpp"

#include "Debug/Assertion.hpp"

#include "Allocator.hpp"
#include "VirtualIterator.hpp"

#if VDEBUG

#include <ostream>

#endif

namespace Lib {

/**
 * Class of generic of single-linked lists.
 */
template <class C>
class List
{
public:
  DECL_ELEMENT_TYPE(C);

  /** builds a single-element list */
  explicit inline List (C head)
    :
    _head(head),
    _tail(0)
  {
  } // List::List

  /** cons */
  inline List (C head, List* tail)
    :
    _head(head),
    _tail(tail)
  {
  } // List::List

  /** Dummy list constructor */
  inline List () {}

  /** creates an empty list */
  inline static List* empty ()
  { return 0; }

  /** true if the list is empty */
  inline bool isEmpty () const
  {
    return this == 0;
  } // List::isEmpty

  /** true if the list is non-empty */
  inline bool isNonEmpty () const
  {
    return this != 0;
  } // List::isNonEmpty

  /** return the tail of the list */
  inline List* tail() const
  {
    ASS_NEQ(this,0);

    return _tail;
  } // List::tail

  /** return a reference to the tail of the list */
  inline List*& tailReference ()
  {
    ASS_NEQ(this,0);

    return _tail;
  } // List::tailReference

  /** return a reference to the tail of the list */
  inline List** tailPtr ()
  {
    ASS_NEQ(this,0);

    return &_tail;
  } // List::tailReference

  /** return the head of the list */
  inline const C head () const
  {
    ASS_NEQ(this,0);

    return _head;
  } // List::head

  inline C head ()
  {
    ASS_NEQ(this,0);

    return _head;
  } // List::head

  inline C* headPtr ()
  {
    ASS_NEQ(this,0);
    return &(this->_head);
  }


  /** return the second element of the list */
  inline C second () const
  {
    return tail()->head();
  } // List::second

  /** Set the head of the list to hd */
  inline void setHead (C hd)
  {
    ASS_NEQ(this,0);

    _head = hd;
  } // List::setHead


  /** Set the tail of the list to tl */
  inline void setTail(List* tl)
  {
    ASS_NEQ(this,0);

    _tail = tl;
  } // list::setTail

  /** Destroy the list */
  void destroy ()
  {
    CALL("List::destroy");

    if (isEmpty()) return;
    List* current = this;

    for (;;) {
      List* next = current->tail();
      delete current;
      if (next->isEmpty()) return;
      current = next;
    }
  } // List::destroy

  /**
   * Destroy the list and apply delete() to every element of the list.
   * Naturally, the list must be a list of pointers.
   * @since 01/04/2006 Bellevue
   */
  void destroyWithDeletion()
  {
    CALL("List::destroyWithDeletion");

    if (isEmpty()) return;
    List* current = this;

    for (;;) {
      List* next = current->tail();
      delete current->head();
      delete current;
      if (next->isEmpty()) return;
      current = next;
    }
  } // List::destroyWithDeletion

  /** create a shallow copy of the list */
  List* copy () const
  {
    if (isEmpty()) return empty();

    List* result = new List;
    result->_head = _head;
    List* previous = result;
    List* rest = _tail;

    while (! rest->isEmpty()) {
      List* tmp = new List;
      tmp->_head = rest->_head;
      previous->_tail = tmp;
      previous = tmp;
      rest = rest->_tail;
    }

    previous->_tail = empty();
    return result;
  }  // List::copy

  /** appends snd to a copy of this list */
  List* append (List* snd)
  {
    if (isEmpty()) return snd;

    List* result = new List;
    result->setHead(head());
    List* previous = result;
    List* rest = tail();

    while(rest->isNonEmpty()) {
      List* tmp = new List;
      tmp->setHead(rest->head());
      previous->setTail(tmp);
      previous = tmp;
      rest = rest->tail();
    }

    previous->setTail(snd);
    return result;
  }  // List::append

  /** return the list obtained by adding elem as the first element
   *  of this list */
  inline List* cons(C elem)
  {
    return new List(elem,this);
  } // List::cons

  /** push elem to lst */
  inline static void push(C elem,List* &lst)
  {
    lst = lst->cons(elem);
  } // List::push

  /**
   * Push all elements from @b it iterator to the list.
   *
   * The first element in the iterator will end up as last in the list
   */
  template<class It>
  static void pushFromIterator(It it, List* &lst)
  {
    while(it.hasNext()) {
      push(it.next(), lst);
    }
  }

  /**
   * True if the list has the given length.
   * @since 10/06/2007 Manchester
   */
  bool hasLength(int length) const
  {
    ASS_GE(length,0);

    for (const List* lst = this;lst;lst = lst->tail()) {
      if (length == 0) return false;
      length--;
    }
    return length == 0;
  } // hasLength

  /** pop the first element and return it */
  inline static C pop(List* &lst)
  {
    CALL("List::pop");
    ASS_NEQ(lst,0);

    List* tail = lst->tail();
    C result = lst->head();
    delete lst;
    lst = tail;

    return result;
  } // List::pop

  /** destructive list concatenation
   *
   * The @b first list is traversed and the @b second is attached
   * to its end.*/
  static List* concat(List* first,List* second)
  {
    if (first == 0) return second;
    if (second == 0) return first;

    List* current = first;
    for (;;) {
      List* next = current->tail();
      if (! next) {
        current->setTail(second);
        return first;
      }
      current = next;
    }
  } // List::concat

  /** Destructive list reversal */
  List* reverse()
  {
    if (isEmpty()) return this;

    List* result = empty();
    List* lst = this;

    while (lst->isNonEmpty()) {
      List* tl = lst->tail();
      lst->setTail(result);
      result = lst;
      lst = tl;
    }

    return result;
  } // List::reverse

  /** return the length of the list */
  int length () const
  {
    int len = 0;

    for (const List* lst = this; lst->isNonEmpty(); lst = lst->tail()) {
      len ++;
    }

    return len;
  } // List::length

  /** True if elem is a member of the list, the comparison is made using == */
  bool member (C elem) const
  {
    for (const List* lst = this; lst->isNonEmpty(); lst = lst->tail()) {
      if (lst->head() == elem) return true;
    }

    return false;
  } // List::member

  /** Destructively removes the first occurrence of elem
   * from the list and returns the resulting list. Does nothing
   * if elem is not a member of the list.
   */
  List* remove (C elem)
  {
    if (isEmpty()) return this;

    if (head() == elem) {
      List* result = tail();
      delete this;
      return result;
    }
    if (tail()->isEmpty()) return this;

    List* current = this;
    List* next = tail();

    for (;;) {
      if (next->head() == elem) { // element found
        current->setTail(next->tail());
        delete next;
        return this;
      }
      current = next;
      next = next->tail();
      if (next->isEmpty()) return this;
    }
  } // List::remove

  /** Return the nth element, counting from 0 */
  C nth(int n) const
  {
    // nth element, counting from 0
    ASS_GE(n,0);

    const List* l = this;

    while (n != 0) {
      ASS_NEQ(l,0);

      l = l->tail();
      n--;
    }

    return l->head();
  } // nth

  /** delete the nth element and return it */
  static C deleteNth(List*& lst, int n)
  {
    // nth element, counting from 0
    ASS (n >= 0);

    C result;
    List* l = lst;
    ASS (lst->isNonEmpty());

    if (n == 0) {
      result = l->head();
      lst = l->tail();
      delete l;
      return result;
    }

    // n != 0
    List* next = l->tail();

    while (--n != 0) {
      l = next;
      next = next->tail();
      ASS (next->isNonEmpty());
    }
    //  now next must be deleted
    result = next->head();
    l->setTail(next->tail());
    delete next;

    return result;
  } // deleteNth

  /** Add  elem as the last element and return the resulting list */
  List* addLast (C elem)
  {
    if (! this) return new List (elem);

    // nonempty, trying to find the end
    List* current;
    for (current = this; current->_tail; current = current->_tail) {
    }

    current->setTail(new List(elem));

    return this;
  } // List::addLast

  /** Split the list into two sublists, first of the length n. Return
   *  the first sublist and save the second sublist in the variable rest. */
  List* split (int n, List*& rest)
  {
    if (! this) {
      ASS_EQ(n,0);
      rest = empty();
      return empty();
    }

    if (n == 0) {
      rest = empty();
      return this;
    }

    List* nth = this;
    while (--n > 0) {
      ASS_NEQ(nth,0);
      nth = nth->_tail;
    }

    ASS_NEQ(nth,0);
    rest = nth->_tail;
    nth->_tail = empty();
    return this;
  } // List::split

  /** iterator over the list elements */
  class Iterator {
  public:
    CLASS_NAME(List::Iterator);
    USE_ALLOCATOR(List::Iterator);
    
    DECL_ELEMENT_TYPE(C);

    inline Iterator() : _lst (0) {}

    inline explicit
    Iterator(List* l)
      : _lst (l)
    {}
    inline explicit
    Iterator(const List* l)
      : _lst (const_cast<List*>(l))
    {}

    /** return the next element */
    inline C next()
    {
      ASS_NEQ(_lst,0);

      C result = _lst->head();
      _lst = _lst->tail();
      return result;
    }

    /**
     * Return the element that will be returned by next (therefore hasNexgt()
     * must have returned true), but do not advance to a further element.
     */
    inline C peekAtNext()
    {
      return _lst->head();
    }

    /** True if there is a next element. */
    inline bool hasNext() const
    {
      return _lst->isNonEmpty();
    }

    inline void reset(List* l) { _lst = l; }

   private:
    /** the rest of the list */
    List* _lst;
  };

  /** iterator over references to list elements */
  class RefIterator {
   public:
     CLASS_NAME(List::RefIterator);
     USE_ALLOCATOR(List::RefIterator);
     
     DECL_ELEMENT_TYPE(C&);

    inline explicit
    RefIterator(List* l)
      : _lst (l)
    {}
    inline explicit
    RefIterator(const List* l)
      : _lst (const_cast<List*>(l))
    {}

    /** return the next element */
    inline C& next()
    {
      ASS_NEQ(_lst,0);

      C& result = _lst->_head;
      _lst = _lst->tail();
      return result;
    }

    /**
     * Return the element that will be returned by next (therefore hasNexgt()
     * must have returned true), but do not advance to a further element.
     */
    inline C& peekAtNext()
    {
      ASS_NEQ(_lst,0);
      return _lst->_head;
    }

    /** True if there is a next element. */
    inline bool hasNext() const
    { return _lst->isNonEmpty(); }

    inline void reset(List* l) { _lst = l; }

   private:
    /** the rest of the list */
    List* _lst;
  };

  class PtrIterator
  {
  public:
    CLASS_NAME(List::PtrIterator);
    USE_ALLOCATOR(List::PtrIterator);
    
    DECL_ELEMENT_TYPE(C*);
    inline
    PtrIterator(List* lst) : _l(lst) {}
    inline bool hasNext()
    { return _l->isNonEmpty(); }

    inline C* next()
    {
      C* res=_l->headPtr();
      _l=_l->tail();
      return res;
    }
  protected:
    List* _l;
  };


  /** Iterator that allows one to delete the current element */
  class DelIterator {
   public:
     CLASS_NAME(List::DelIterator);
     USE_ALLOCATOR(List::DelIterator);
     
    DECL_ELEMENT_TYPE(C);
    inline DelIterator (List*& l)
      :
      _lst(l),
      _prev(0),
      _cur(0)
    {}

    /** Reset the iterator to the beginning of the list */
    inline void reset()
    {
      _prev = 0;
      _cur = 0;
    } // reset

    /** return the next element */
    inline C next()
    {
      if (_cur) { // there was an element previously returned by next()
	_prev = _cur;
	_cur = _cur->tail();
	ASS_NEQ(_cur,0);
      }
      else { // result must be the first element of the list
	_cur = _lst;
      }
      return _cur->head();
    }

    /** True if there is a next element */
    inline bool hasNext()
    {
      if (_cur) { // there was an element previously returned by next()
	return _cur->tail() != 0;
      }
      return _lst->isNonEmpty();
    }

    /** Delete the current element */
    void del()
    {
      // we can only delete the element returned by next
      ASS_NEQ(_cur,0);
      // check that two delete requests in row did not occur
      ASS_NEQ(_cur,_prev);

      if (_cur == _lst) { // the first element must be deleted
	_lst = _lst->tail();
	delete _cur;
	_cur = 0;
	return;
      }

      // not the first element
      _prev->setTail(_cur->tail());
      delete _cur;
      _cur = _prev;
    } // List::DelIterator::del

    /**
     * Replace the current element by elem.
     */
    inline void replace(C elem)
    {
      ASS_NEQ(_cur,0);
      _cur->setHead(elem);
    } // DelIterator::replace

    /**
     * Insert a list of elements before the cursor. If the iteration
     * continues, the new list will not be returned by the iterator.
     * @pre At least one element should have been returned
     *   by a previous call to next() so _cur != null
     * @pre The preceding operation must not have been del()
     * @since 27/12/2007 Manchester
     */
    void insert (List* lst)
    {
      ASS_NEQ(_cur, _prev);
      if (! lst) return;

      List* last = lst;
      // lst is non-empty, find it's last element
      while (last->tail()) {
	last = last->tail();
      }

      if (_prev)
	_prev->setTail(lst);
      else _lst = lst;

      last->setTail(_cur);
      _prev = last;
    } // List::DelIterator::insert

    /**
     * Insert an element before the cursor. If the iteration
     * continues, the new element will not be returned by the iterator.
     * @pre At least one element should have been returned
     *   by a previous call to next() so _cur != null
     * @pre The preceding operation must not have been del()
     * @since 27/12/2007 Manchester
     */
    void insert (C elem)
    {
      ASS_NEQ(_cur, _prev);
      List* lst = new List(elem,_cur);
      if (_prev)
	_prev->setTail(lst);
      else _lst = lst;

      lst->setTail(_cur);
      _prev = lst;
    } // List::DelIterator::insert

  private:
    /** The reference to the list over which the iteration is done */
    List*& _lst;
    /** The element previous to _cur. If _cur is the first element
     *  then _prev=null */
    List* _prev;
    /** _cur is the element returned by the last next,
     * if _cur=null then no next was called */
    List* _cur;
  };

  /**
   * iterator over the list elements
   *
   * @warning All elements of this iterator must be yielded
   * or a memory leak will occur.
   */
  class DestructiveIterator {
  public:
    CLASS_NAME(List::DestructiveIterator);
    USE_ALLOCATOR(List::DestructiveIterator);
    
    DECL_ELEMENT_TYPE(C);

    inline explicit
    DestructiveIterator(List* l)
      : _lst (l)
    {}

    /** return the next element */
    inline C next()
    {
      ASS_NEQ(_lst,0);
      return List::pop(_lst);
    }

    /** True if there is a next element. */
    inline bool hasNext() const
    {
      return _lst->isNonEmpty();
    }
   private:
    /** the rest of the list */
    List* _lst;
  };

  // use allocator to (de)allocate objects of this class
  CLASS_NAME(List);
  USE_ALLOCATOR(List);

  /**
   * Class that allows to create a list initially by pushing elements
   * at the end of it.
   * @since 06/04/2006 Bellevue
   */
  class FIFO {
  public:
    /** constructor */
    inline explicit FIFO(List* &lst)
      : _last(0),
	_initial(lst)
    {
      ASS_EQ(_initial,0);
    }
    /** add element at the end of the original list */
    inline void push(C elem)
    {
      List* newLast = new List(elem);
      if (_last) 
	_last->setTail(newLast);
      else _initial = newLast;

      _last = newLast;
    } // FIFO::push

  private:
    /** last element */
    List* _last;
    /** reference to the initial element */
    List* &_initial;
  }; // class List::FIFO

protected:  // structure

  /** head of the list */
  C _head;
  /** tail of the list */
  List* _tail;
};  // class List

///@addtogroup Iterators
///@{

template<typename T>
typename List<T>::Iterator getContentIterator(List<T>* lst)
{
  return typename List<T>::Iterator(lst);
}

///@}?


///@addtogroup Reflection
///@{

/** see Reflection.hpp */
template<typename T>
struct ElementTypeInfo<List<T>* >
{
  typedef T Type;
};

/** see Reflection.hpp */
template<typename T>
struct IteratorTypeInfo<List<T>* >
{
  typedef typename List<T>::Iterator Type;
};
template<typename T>
struct IteratorTypeInfo<const List<T>*>
{
  typedef typename List<T>::Iterator Type;
};

///@}?

#if VDEBUG

template<typename T>
std::ostream& operator<< (ostream& out, const List<T>& lstr )
{
  const List<T>* lst=&lstr;
  out<<'[';

  while(lst) {
    out<<lst->head();
    lst=lst->tail();
    if (lst) out << ",\n";
  }

  return out<<']';
}

template<typename T>
std::ostream& operator<< (ostream& out, const List<T*>& lstr )
{
  const List<T*>* lst=&lstr;
  out<<'[';

  while(lst) {
    out<<(*lst->head());
    lst=lst->tail();
    if (lst) out << ",\n";
  }

  return out<<']';
}

#endif

}

#endif


