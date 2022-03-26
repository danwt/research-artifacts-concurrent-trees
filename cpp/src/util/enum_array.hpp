#pragma once
#include <array>

template<typename ValueType, std::size_t Size, typename IndexType>
class EnumArray
{
public:
  ValueType& operator[](IndexType i)
  {
    return arr_[static_cast<std::size_t>(i)];
  }

  const ValueType& operator[](IndexType i) const
  {
    return arr_[static_cast<std::size_t>(i)];
  }

private:
  std::array<ValueType, Size> arr_;
};