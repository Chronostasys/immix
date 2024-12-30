# GC代码重构

[原论文](https://www.steveblackburn.org/pubs/papers/immix-pldi-2008.pdf)

## 目标

1. 重新实现分配器相关代码，优化分配hotpath，修复一个line只分配一个对象的问题
2. 重新实现GC触发逻辑

以下方案基于全保守回收设计，如果有好的精确回收的方案可以提出讨论

## 1. 分配器重新实现

### 1.1 Header结构重新设计

原有的[Header结构](./src/block.rs)如下：

```rust
/// |                           LINE HEADER(1 byte)                         |
/// |    7   |    6   |    5   |    4   |    3   |    2   |    1   |    0   |
/// | is head|   eva  |  evaed |        object type       | marked |  used  |
```

新Header结构如下：

```rust
/// |                           LINE HEADER(1 byte)                         |
/// |    7   |    6   |    5   |    4   |    3   |    2   |    1   |    0   |
/// | medium |   eva  |  evaed |        -----------       | marked |  used  |
```

首先，不再在分配内存的时候操作used位，这样可以避免bump allocation时对header的读写操作，
由于head永远在block开头，一个block的大小时32KB，所以如果每次分配都要访问head，
这次访问很可能导致L1 cache miss。

在每次sweep的时候设置used位，帮助在之后的分配过程中寻找hole

其次，`is head`位改为`medium`位，用于标记当前line是不是属于medium object，
对于small object（小于一个line 128B）这个位是0，这保证了我们大部分分配情况
（小对象）不需要访问header，只有在分配medium object时才需要访问header。
注意medium object的第一个line的header的medium位也是0，这样可以标记他的开始。

### 1.2 分配逻辑优化

使用bump pointer allocation，最大化内存分配的速度，cursor使用指针代替原本的usize类型，
避免掉地址转换的开销。这样分配内存在大部分情况下只需要一个指针的加法操作 + 检查是否越界即可。

在用掉当前可用的连续空间（hole）的时候，需要更新当前Block中的hole等相关数据，这个逻辑最好能延迟到
下次分配内存的时候进行，这样方便我们使用ir实现hotpath分配逻辑。

bump pointer的时候应该保证alignment为8 byte，小对象不能cross
line，medium object所占有的最后一个line应该被他完全占有，否则如果
两个medium object相邻，可能会导致我们的标记有问题。

## 2. GC触发逻辑

### 2.1 触发条件修改

在启动的时候设置一个全局的heap_threshold，即为GC初试堆大小（当然这个数字会比我们一开始mmap的内存小的多），
当分配的内存超过这个阈值时，触发GC。

可以修改现在global allocator的alloc函数，多返回一个bool，如果alloc了新的内存且超过了阈值，返回true。

### 2.2 GC堆增长逻辑

如果GC触发，后free的内存小于一定比例，则增长堆大小，否则不增长。

## 更新：精确回收实现

为了重新实现精确回收，需要给每个对象添加一个额外的object header，用于存储对象的大小和类型信息。

### 1. Header结构

```rust

```
