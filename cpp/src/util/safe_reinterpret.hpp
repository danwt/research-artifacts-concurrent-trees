#pragma once

template <class From, class To> auto safe_reinterpret_cast(From from) -> To {
  static_assert(sizeof(From) <= sizeof(To), "Destination type too narrow");
  return reinterpret_cast<To>(from);
}