#pragma once

#include <cstddef>
#include <functional>

struct l_tag;
struct r_tag;

template <typename T, typename Tag> struct NodeT {
  NodeT *l = nullptr;
  NodeT *r = nullptr;
  NodeT *p = nullptr;
  T v;

  void change_value(T const &i) {
    v = i;
    l = nullptr;
    r = nullptr;
    p = nullptr;
  }

  explicit NodeT(T const &i) : v(i) {}

  explicit NodeT(T &&i) : v(std::move(i)) {}
};

template <typename L, typename R>
struct Node_t : NodeT<L, l_tag>, NodeT<R, r_tag> {
  using nodel = NodeT<L, l_tag>;
  using noder = NodeT<R, r_tag>;

  Node_t(L const &l, R const &r) : nodel(l), noder(r) {}

  Node_t(L const &l, R &&r) : nodel(l), noder(std::move(r)) {}

  Node_t(L &&l, R const &r) : nodel(std::move(l)), noder(r) {}

  Node_t(L &&l, R &&r) : nodel(std::move(l)), noder(std::move(r)) {}
};

template <typename Type, typename Tag, typename Comp = std::less<Type>>
struct splay {
  using Node = NodeT<Type, Tag>;

public:
  splay() : root(nullptr) { }

  void set_comp(Comp const &c) noexcept { comp = &c; }

  Node *begin() const noexcept {
    if (!root)
      return nullptr;
    Node *n = root;
    while (n->l) {
      n = n->l;
    }
    return Splay(n);
  }

  Node *last() const noexcept {
    if (!root)
      return nullptr;
    Node *n = root;
    while (n->r) {
      n = n->r;
    }
    return Splay(n);
  }

  Node *insert(Node *n) noexcept {
    if (!root) {
      root = n;
      return root;
    }
    Node *P = root;
    while (true) {
      if (!(*comp)(P->v, n->v) && !(*comp)(n->v, P->v))
        break;
      if ((*comp)(n->v, (P->v))) {
        if (P->l)
          P = P->l;
        else {
          P->l = n;
          n->p = P;
          P = P->l;
          break;
        }
      } else {
        if (P->r)
          P = P->r;
        else {
          P->r = n;
          n->p = P;
          P = P->r;
          break;
        }
      }
    }
    return Splay(P);
  }

  Node *upper_bound(Type const &v) const noexcept {
    if (Splay(lower_bound(root, v)) == nullptr)
      return nullptr;
    return (*comp)(v, root->v) ? root : next(root);
  }

  Node *lower_bound(Type const &v) const { return Splay(lower_bound(root, v)); }

  Node *find(Type const &v) const noexcept {
    if (!root)
      return nullptr;
    lower_bound(v);
    return (!(*comp)(root->v, v) && !(*comp)(v, root->v)) ? root : nullptr;
  }

  bool erase(Node *N) noexcept {
    if (!Splay(N))
      return false;
    Node *P = N->l;
    if (!P) {
      root = N->r;
      if (root != nullptr)
        root->p = nullptr;
      return true;
    }
    while (P->r)
      P = P->r;
    if (N->r) {
      P->r = N->r;
      N->r->p = P;
    }
    root = N->l;
    if (root != nullptr)
      root->p = nullptr;
    return true;
  }

  Node *next(Node *n) const noexcept {
    if (n->r) {
      n = n->r;
      while (n->l) {
        n = n->l;
      }
      return n;
    }
    while (n->p && n->p->l != n) {
      n = n->p;
    }
    return n->p;
  }

  Node *prev(Node *n) const noexcept {
    if (n->l) {
      n = n->l;
      while (n->r) {
        n = n->r;
      }
      return n;
    }
    while (n->p && n->p->r != n) {
      n = n->p;
    }
    return n->p;
  }

private:
  Node *lower_bound(Node *r, Type const &v) const noexcept {
    if (r == nullptr) {
      return r;
    }
    if (!(*comp)(r->v, v)) {
      Node *lb = r;
      Node *rb = lower_bound(r->l, v);
      if (rb == nullptr)
        return lb;
      return rb;
    } else {
      return lower_bound(r->r, v);
    }
  }

  void rightRotate(Node *P) const noexcept {
    Node *T = P->l;
    Node *B = T->r;
    Node *D = P->p;
    if (D) {
      if (D->r == P)
        D->r = T;
      else
        D->l = T;
    }
    if (B)
      B->p = P;
    T->p = D;
    T->r = P;

    P->p = T;
    P->l = B;
  }

  void leftRotate(Node *P) const noexcept {
    Node *T = P->r;
    Node *B = T->l;
    Node *D = P->p;
    if (D) {
      if (D->r == P)
        D->r = T;
      else
        D->l = T;
    }
    if (B)
      B->p = P;
    T->p = D;
    T->l = P;

    P->p = T;
    P->r = B;
  }

  Node *Splay(Node *n) const noexcept {
    if (n == nullptr)
      return n;
    while (true) {
      Node *p = n->p;
      if (!p)
        break;
      Node *pp = p->p;
      if (!pp) // Zig
      {
        if (p->l == n)
          rightRotate(p);
        else
          leftRotate(p);
        break;
      }
      if (pp->l == p) {
        if (p->l == n) { // ZigZig
          rightRotate(pp);
          rightRotate(p);
        } else { // ZigZag
          leftRotate(p);
          rightRotate(pp);
        }
      } else {
        if (p->l == n) { // ZigZag
          rightRotate(p);
          leftRotate(pp);
        } else { // ZigZig
          leftRotate(pp);
          leftRotate(p);
        }
      }
    }
    root = n;
    return root;
  }

  mutable Node *root;
  Comp const *comp;
};

template <typename Left, typename Right, typename CompareLeft = std::less<Left>,
          typename CompareRight = std::less<Right>>
struct bimap {
private:
  using left_t = Left;
  using right_t = Right;

  size_t ssize = 0;

  using node = Node_t<Left, Right>;
  using node_l = NodeT<Left, l_tag>;
  using node_r = NodeT<Right, r_tag>;
  using left_splay = splay<Left, l_tag, CompareLeft>;
  using right_splay = splay<Right, r_tag, CompareRight>;

  left_splay spl_l;
  right_splay spl_r;
  CompareLeft compare_left;
  CompareRight compare_right;

public:
  struct left_iterator;

  struct right_iterator {
    right_iterator(node_r *n, bimap const *b) : node(n), bmp(b) {}

    right_t const &operator*() const noexcept { return node->v; }

    right_t const *operator->() const noexcept { return &node->v; }

    right_iterator &operator++() {
      if(node == nullptr)
        throw std::out_of_range("ERROR: OUT OF RANGE");
      node = bmp->spl_r.next(node);
      return *this;
    }

    right_iterator operator++(int) {
      auto it = *this;
      ++(*this);
      return it;
    }

    right_iterator &operator--() {
      if(node == bmp->begin_right().node)
        throw std::out_of_range("ERROR: OUT OF RANGE");
      if (node == nullptr) {
        node = bmp->spl_r.last();
        return *this;
      }
      node = bmp->spl_r.prev(node);
      return *this;
    }

    right_iterator operator--(int) {
      auto it = *this;
      --(*this);
      return it;
    }

    left_iterator flip() const noexcept {
      if (node == nullptr)
        return left_iterator(nullptr, bmp);
      return left_iterator(static_cast<Node_t<Left, Right> *>(node), bmp);
    }

    Node_t<Left, Right> *cast() const noexcept {
      return static_cast<Node_t<Left, Right> *>(node);
    }

    friend bool operator==(right_iterator const &a, right_iterator const &b) noexcept {
      return a.node == b.node;
    }

    friend bool operator!=(right_iterator const &a, right_iterator const &b) noexcept {
      return !(a == b);
    }

  private:
    friend class bimap;

    node_r *node;
    bimap const *bmp;
  };

  struct left_iterator {
    explicit left_iterator(node_l *n, bimap const *b) : node(n), bmp(b) {}

    // Элемент на который сейчас ссылается итератор.
    // Разыменование итератора end_left() неопределено.
    // Разыменование невалидного итератора неопределено.
    left_t const &operator*() const noexcept { return node->v; }

    left_t const *operator->() const noexcept { return &node->v; }

    // Переход к следующему по величине left'у.
    // Инкремент итератора end_left() неопределен.
    // Инкремент невалидного итератора неопределен.

    left_iterator &operator++() {
      if(node == nullptr)
        throw std::out_of_range("ERROR: OUT OF RANGE");
      node = bmp->spl_l.next(node);
      return *this;
    }

    left_iterator operator++(int) {
      auto it = *this;
      ++(*this);
      return it;
    }

    // Переход к предыдущему по величине left'у.
    // Декремент итератора begin_left() неопределен.
    // Декремент невалидного итератора неопределен.
    left_iterator &operator--() {
      if(node == bmp->begin_left().node)
        throw std::out_of_range("ERROR: OUT OF RANGE");
      if (node == nullptr) {
        node = bmp->spl_l.last();
        return *this;
      }
      node = bmp->spl_l.prev(node);
      return *this;
    }

    left_iterator operator--(int) {
      auto it = *this;
      --(*this);
      return it;
    }

    // left_iterator ссылается на левый элемент некоторой пары.
    // Эта функция возвращает итератор на правый элемент той же пары.
    // end_left().flip() возращает end_right().
    // end_right().flip() возвращает end_left().
    // flip() невалидного итератора неопределен.
    right_iterator flip() const noexcept {
      if (node == nullptr)
        return right_iterator(nullptr, bmp);
      return right_iterator(static_cast<Node_t<Left, Right> *>(node), bmp);
    }

    Node_t<Left, Right> *cast() const noexcept {
      return static_cast<Node_t<Left, Right> *>(node);
    }

    friend bool operator==(left_iterator const &a, left_iterator const &b) noexcept {
      return a.node == b.node;
    }

    friend bool operator!=(left_iterator const &a, left_iterator const &b) noexcept {
      return !(a == b);
    }

  private:
    friend class bimap;

    node_l *node;
    bimap const *bmp;
  };

  // Создает bimap не содержащий ни одной пары.
  bimap(CompareLeft cl = CompareLeft(), CompareRight cr = CompareRight())
      : compare_left(cl), compare_right(cr) {
    spl_l.set_comp(compare_left);
    spl_r.set_comp(compare_right);
  }

  // Конструкторы от других и присваивания
  bimap(bimap const &other) {
    for (auto i = other.begin_left(); i != other.end_left(); ++i) {
      node *new_node = new node(*i, *i.flip());
      spl_l.insert(new_node);
      spl_r.insert(new_node);
    }
    ssize = other.ssize;
  }

  bimap(bimap &&other) noexcept {
    std::swap(spl_l, other.spl_l);
    std::swap(spl_r, other.spl_r);
    std::swap(ssize, other.ssize);
  }

  bimap &operator=(bimap const &other) {
    *this = bimap(other);
    return *this;
  }

  bimap &operator=(bimap &&other) noexcept {
    std::swap(spl_l, other.spl_l);
    std::swap(spl_r, other.spl_r);
    std::swap(ssize, other.ssize);
    return *this;
  }

  // Деструктор. Вызывается при удалении объектов bimap.
  // Инвалидирует все итераторы ссылающиеся на элементы этого bimap
  // (включая итераторы ссылающиеся на элементы следующие за последними).
  ~bimap() { erase_left(begin_left(), end_left()); }

  // Вставка пары (left, right), возвращает итератор на left.
  // Если такой left или такой right уже присутствуют в bimap, вставка не
  // производится и возвращается end_left().

  left_iterator insert(left_t const &left, right_t const &right) {
    return insert_impl(std::forward<const left_t>(left),
                       std::forward<const right_t>(right));
  }

  left_iterator insert(left_t const &left, right_t &&right) {
    return insert_impl(std::forward<const left_t>(left),
                       std::forward<right_t>(right));
  }

  left_iterator insert(left_t &&left, right_t const &right) {
    return insert_impl(std::forward<left_t>(left),
                       std::forward<const right_t>(right));
  }

  left_iterator insert(left_t &&left, right_t &&right) noexcept {
    return insert_impl(std::forward<left_t>(left),
                       std::forward<right_t>(right));
  }

  // Удаляет элемент и соответствующий ему парный.
  // erase невалидного итератора неопределен.
  // erase(end_left()) и erase(end_right()) неопределены.
  // Пусть it ссылается на некоторый элемент e.
  // erase инвалидирует все итераторы ссылающиеся на e и на элемент парный к e.
  left_iterator erase_left(left_iterator it) noexcept {
    return erase_it_impl(it);
  }

  // Аналогично erase, но по ключу, удаляет элемент если он присутствует, иначе
  // не делает ничего Возвращает была ли пара удалена
  bool erase_left(left_t const &left) noexcept {
    return erase_impl(find_left(left));
  }

  right_iterator erase_right(right_iterator it) noexcept {
    return erase_it_impl(it);
  }

  bool erase_right(right_t const &right) noexcept {
    return erase_impl(find_right(right));
  }

  // erase от ренжа, удаляет [first, last), возвращает итератор на последний
  // элемент за удаленной последовательностью
  left_iterator erase_left(left_iterator first, left_iterator last) noexcept {
    return erase_range(first, last);
  }

  right_iterator erase_right(right_iterator first,
                             right_iterator last) noexcept {
    return erase_range(first, last);
  }

  // Возвращает итератор по элементу. Если не найден - соответствующий end()
  left_iterator find_left(left_t const &left) const noexcept {
    return left_iterator(spl_l.find(left), this);
  }

  right_iterator find_right(right_t const &right) const noexcept {
    return right_iterator(spl_r.find(right), this);
  }

  // Возвращает противоположный элемент по элементу
  // Если элемента не существует -- бросает std::out_of_range
  right_t const &at_left(left_t const &key) const {
    return at_impl(find_left(key));
  }

  left_t const &at_right(right_t const &key) const {
    return at_impl(find_right(key));
  }

  // Возвращает противоположный элемент по элементу
  // Если элемента не существует, добавляет его в bimap и на противоположную
  // сторону кладет дефолтный элемент, ссылку на который и возвращает
  // Если дефолтный элемент уже лежит в противоположной паре - должен поменять
  // соответствующий ему элемент на запрашиваемый (смотри тесты)
  template <typename T, typename = std::enable_if_t<
                            std::is_same_v<T, right_t> &&
                            std::is_default_constructible_v<left_t>>>
  right_t const &at_left_or_default(T const &key) {
    auto lit = find_left(key);
    if (lit != end_left()) {
      return *(lit.flip());
    }
    right_iterator rit = find_right(right_t());
    if (rit != end_right()) {
      spl_l.erase(rit.cast());
      auto l_node = rit.flip().node;
      l_node->change_value(key);
      spl_l.insert(rit.cast());
      return *rit;
    }
    return *(insert(key, right_t()).flip());
  }

  template <typename T, typename = std::enable_if_t<
                            std::is_same_v<T, left_t> &&
                            std::is_default_constructible_v<right_t>>>
  left_t const &at_right_or_default(T const &key) {
    auto rit = find_right(key);
    if (rit != end_right()) {
      return *(rit.flip());
    }
    auto lit = find_left(left_t());
    if (lit != end_left()) {
      spl_r.erase(lit.cast());
      auto r_node = lit.flip().node;
      r_node->change_value(key);
      spl_r.insert(lit.cast());
      return *lit;
    }
    return *insert(left_t(), key);
  }

  //    // lower и upper bound'ы по каждой стороне
  //    // Возвращают итераторы на соответствующие элементы
  //    // Смотри std::lower_bound, std::upper_bound.
  left_iterator lower_bound_left(const left_t &left) const noexcept {
    return left_iterator(spl_l.lower_bound(left), this);
  }

  left_iterator upper_bound_left(const left_t &left) const noexcept {
    return left_iterator(spl_l.upper_bound(left), this);
  }

  right_iterator lower_bound_right(const right_t &right) const noexcept {
    return right_iterator(spl_r.lower_bound(right), this);
  }

  right_iterator upper_bound_right(const right_t &right) const noexcept {
    return right_iterator(spl_r.upper_bound(right), this);
  }

  // Возващает итератор на минимальный по порядку left.
  left_iterator begin_left() const noexcept {
    return left_iterator(spl_l.begin(), this);
  }

  // Возващает итератор на следующий за последним по порядку left.
  left_iterator end_left() const noexcept {
    return left_iterator(nullptr, this);
  }

  // Возващает итератор на минимальный по порядку right.
  right_iterator begin_right() const noexcept {
    return right_iterator(spl_r.begin(), this);
  }

  // Возващает итератор на следующий за последним по порядку right.
  right_iterator end_right() const noexcept {
    return right_iterator(nullptr, this);
  }

  // Проверка на пустоту
  [[nodiscard]] bool empty() const noexcept { return ssize == 0; }

  // Возвращает размер бимапы (кол-во пар)
  [[nodiscard]] std::size_t size() const noexcept { return ssize; }

  // операторы сравнения
  friend bool operator==(bimap const &a, bimap const &b) {
    if (a.ssize != b.ssize)
      return false;
    auto ai = a.begin_left();
    for (auto bi = b.begin_left(); bi != b.end_left(); ++bi, ++ai) {
      if (a.compare_left(*ai, *bi) || a.compare_left(*bi, *ai) ||
          a.compare_right(*ai.flip(), *bi.flip()) ||
          a.compare_right(*bi.flip(), *ai.flip()))
        return false;
    }
    return true;
  }

  friend bool operator!=(bimap const &a, bimap const &b) { return !(a == b); }

private:
  template <typename T, typename K>
  left_iterator insert_impl(T &&left, K &&right) {
    if (find_left(left) == end_left() && find_right(right) == end_right()) {
      node *new_node = new node(std::forward<T>(left), std::forward<K>(right));
      spl_l.insert(new_node);
      spl_r.insert(new_node);
      ssize++;
      return left_iterator(new_node, this);
    }
    return end_left();
  }

  template <typename T>
  T erase_it_impl(T it) noexcept {
    if (it.node != nullptr) {
      T ret(it.node, this);
      ret++;
      node *Node = it.cast();
      spl_r.erase(Node);
      spl_l.erase(Node);
      delete Node;

      ssize--;
      return ret;
    }
    return it;
  }

  template <typename T>
  bool erase_impl(T it) noexcept {
    if (it.node != nullptr) {
      erase_it_impl(it);
      return true;
    }
    return false;
  }

  template <typename T>
  T erase_range(T first, T last) noexcept {
    for (; first != last;) {
      first = erase_it_impl(first);
    }
    return last;
  }

  template <typename T>
  auto const &at_impl(T it) const {
    if (it.node != nullptr) {
      return *it.flip();
    }
    throw std::out_of_range("ERROR: OUT OF RANGE");
  }
};
