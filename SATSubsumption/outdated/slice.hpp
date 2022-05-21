#ifndef SLICE_HPP
#define SLICE_HPP


/// A fixed-size non-owning vector.
template < typename T >
class slice
{
  public:
    using value_type = T;
    using reference = value_type&;
    using const_reference = value_type const&;
    // using pointer = typename std::allocator_traits<STLAllocator<T>>::pointer;  // ???
    using pointer = T*;
    using const_pointer = T const*;
    using size_type = std::size_t;
    using difference_type = std::ptrdiff_t;

    using iterator = pointer;
    using const_iterator = const_pointer;

  public:
    slice(pointer data, size_type size)
      : m_data(data)
      , m_size(size)
    { }

    ~slice() = default;
    slice(slice const&) = default;
    slice(slice&&) = default;
    slice& operator=(slice const&) = default;
    slice& operator=(slice&&) = default;

    iterator begin()
    {
      return &m_data[0];
    }

    iterator end()
    {
      return &m_data[m_size];  // one past the end
    }

    const_iterator cbegin()
    {
      return &m_data[0];
    }

    const_iterator cend()
    {
      return &m_data[m_size];  // one past the end
    }

    reference operator[](size_type pos)
    {
      ASS_L(pos, m_size);
      return m_data[pos];
    }

    const_reference operator[](size_type pos) const
    {
      ASS_L(pos, m_size);
      return m_data[pos];
    }

    size_type size() const
    {
      return m_size;
    }

  private:
    pointer m_data;
    size_type m_size;
};


#endif /* !SLICE_HPP */
