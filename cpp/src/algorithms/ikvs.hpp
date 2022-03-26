#pragma once
#include <optional>

using K = int;
using V = int;

class IKVS {
public:
  virtual ~IKVS() = 0;

  [[nodiscard]] virtual std::optional<V> get(K k) const = 0;
  virtual void insert(K k, V v) = 0;
  virtual void erase(K k) = 0;
  virtual bool internally_consistent() = 0;

protected:
  IKVS() = default;
  IKVS(IKVS const &) = default;
  IKVS(IKVS &&) = default;
  IKVS &operator=(IKVS const &) = default;
  IKVS &operator=(IKVS &&) = default;
};

inline IKVS::~IKVS() = default;
