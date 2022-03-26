#pragma once

#include "ikvs.hpp"
#include <optional>
#include <string>
#include <vector>

struct debug_graph {

  static std::string json_string_escaped(std::string s) {
    return "\"" + s + "\"";
  }

  static std::string json_pair(std::string s, std::string t) {
    return json_string_escaped(s) + ":" + t;
  }

  struct node {
    K k;
    std::optional<V> v;
    bool is_chunk_root;
    bool is_leaf;

    [[nodiscard]] std::string str() const {
      std::string s;
      s += "{";
      s += json_pair("key", std::to_string(k));
      if (v != std::nullopt) {
        s += "," + json_pair("val", std::to_string(*v));
      }
      s += "," + json_pair("is_chunk_root",
                           std::string(is_chunk_root ? "true" : "false"));
      s += "," + json_pair("is_leaf", std::string(is_leaf ? "true" : "false"));
      s += "}";
      return s;
    }
  };

  struct edge {
    node from;
    node to;
    bool left;
    bool parent;
    [[nodiscard]] std::string str() const {
      std::string s;
      s += "{";
      s += json_pair("from", from.str()) + ",";
      s += json_pair("to", to.str()) + ",";
      s += json_pair("left", std::string(left ? "true" : "false")) + ",";
      s += json_pair("parent", std::string(parent ? "true" : "false"));
      s += "}";

      return s;
    }
  };

  std::vector<edge> edges;
  node root;
  std::string title;

  std::string json_edges() {
    std::string s;

    s.push_back('[');
    for (int i{0}; i + 1 < edges.size(); ++i) {
      s += edges[i].str();
      s += ",";
    }
    if (!edges.empty()) {
      s += edges.back().str();
    }
    s.push_back(']');

    return s;
  }

  std::string json() {
    std::string s{"[graph]"};

    s += "{";
    s += json_pair("title", json_string_escaped(title)) + ",";
    s += json_pair("edges", json_edges());
    s += "}";

    return s;
  }
};
