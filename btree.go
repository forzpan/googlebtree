package btree

import (
	"fmt"
	"io"
	"sort"
	"strings"
	"sync"
)

const (
	DefaultFreeListSize = 32
)

var (
	nilItems    = make(items, 16)    //初始化一个items，里面每个Item都是nil
	nilChildren = make(children, 16) //初始化一个children，里面每个*node都是nil
)

// 迭代中处理函数，返回false的时候，调用者应该立即结束
type ItemIterator func(i Item) bool

// btree的元素，实际存储的东西，用过接口来表示
type Item interface {
	Less(than Item) bool
}

// 一堆Item
type items []Item

// 一推*node
type children []*node

// 节点，items总比children少一个
type node struct {
	items    items
	children children
	cow      *copyOnWriteContext
}

// BTree结构，写不是并发安全的，但是读是并发安全的.
// 树中每个结点至多有2*degree个孩子.
// 除根结点和叶子结点外，其它每个结点至少有degree个孩子.
// 若根结点不是叶子结点，则至少有2个孩子.
// 所有叶子结点都出现在同一层.
type BTree struct {
	degree int                 //度
	length int                 //Item数量
	root   *node               //根节点
	cow    *copyOnWriteContext //cow上下文
}

// FreeList表示等待重用的btree nodes. 默认每个BTree拥有自己的FreeList,但是多个BTrees可以共享相同的FreeList.
type FreeList struct {
	mu       sync.Mutex //为了并发安全
	freelist []*node
}

// copyOnWriteContext 指针 决定了node的拥有关系。树和Node的copyOnWriteContext是同一个时，允许更新这个node，不匹配时，需要复制这个节点。
// 任何写操作，必须符合一个条件，当前节点的copyOnWriteContext和请求进行写的树的copyOnWriteContext是同一个.
// 当不匹配时，使用正确的copyOnWriteContext复制一个node，进行继续的操作
// 因此，访问的当前node肯定和写请求的树拥有相同的copyOnWriteContext，更新是原地更新，但是，子树不一定拥有相同的copyOnWriteContext，因此可能需要一个复制node。
type copyOnWriteContext struct {
	freelist *FreeList
}

// cow上下文创建一个Node，并且把这个上下文给这个节点，就是一个树ReplaceOrInsert出来的节点的copyOnWriteContext都是这个Btree元信息里的那个cow
func (c *copyOnWriteContext) newNode() (n *node) {
	n = c.freelist.newNode()
	n.cow = c
	return
}

type freeType int

const (
	ftFreelistFull freeType = iota // node 被释放，COW的freelist满了放不下了，这个Node可能已经被GC了
	ftStored                       // node 被存储在COW的freelist里待会重用
	ftNotOwned                     // node 和COW不是从属关系
)

// 释放一个Node，不属于该copyOnWriteContext的Node是不能够free的
func (c *copyOnWriteContext) freeNode(n *node) freeType {
	if n.cow == c {
		// 完全清空，利于GC
		n.items.truncate(0)
		n.children.truncate(0)
		n.cow = nil
		if c.freelist.freeNode(n) {
			return ftStored
		} else {
			return ftFreelistFull
		}
	} else {
		return ftNotOwned
	}
}

// 初始化一个FreeList
func NewFreeList(size int) *FreeList {
	return &FreeList{freelist: make([]*node, 0, size)}
}

// 从FreeList里拿一个Node，没有的话创建，有的话返回最后一个，改成getNode比较好
func (f *FreeList) newNode() (n *node) {
	f.mu.Lock()
	index := len(f.freelist) - 1
	if index < 0 {
		f.mu.Unlock()
		return new(node)
	}
	n = f.freelist[index]
	f.freelist[index] = nil
	f.freelist = f.freelist[:index]
	f.mu.Unlock()
	return
}

// 释放的Node往FreeList增加，成功了返回true，如果FreeList已经满了返回false，名字用putNode比较好吧
func (f *FreeList) freeNode(n *node) (out bool) {
	f.mu.Lock()
	if len(f.freelist) < cap(f.freelist) {
		f.freelist = append(f.freelist, n)
		out = true
	}
	f.mu.Unlock()
	return
}

// 初始化一个树元信息
func New(degree int) *BTree {
	return NewWithFreeList(degree, NewFreeList(DefaultFreeListSize))
}

// 利用存在的一个FreeList初始化一个树元信息
func NewWithFreeList(degree int, f *FreeList) *BTree {
	if degree <= 1 {
		panic("bad degree")
	}
	return &BTree{
		degree: degree,
		cow:    &copyOnWriteContext{freelist: f},
	}
}

// items指定位置插入一个Item
func (s *items) insertAt(index int, item Item) {
	*s = append(*s, nil) // 扩展一个位置出来
	if index < len(*s) { // 可能index==len，需要插入的位置就在最后一个
		copy((*s)[index+1:], (*s)[index:]) // 位置后面的往后挪一下
	}
	(*s)[index] = item // 覆盖指定位置的数据
}

// children指定位置插入一个node指针
func (s *children) insertAt(index int, n *node) {
	*s = append(*s, nil)
	if index < len(*s) {
		copy((*s)[index+1:], (*s)[index:])
	}
	(*s)[index] = n
}

//  items指定位置删除一个Item
func (s *items) removeAt(index int) Item {
	item := (*s)[index]
	copy((*s)[index:], (*s)[index+1:]) // 位置后面的往前挪一下
	(*s)[len(*s)-1] = nil              // 最后一个改成nil，利于GC
	*s = (*s)[:len(*s)-1]              // 最后一个位置踢出去
	return item
}

// children指定位置删除一个node指针
func (s *children) removeAt(index int) *node {
	n := (*s)[index]
	copy((*s)[index:], (*s)[index+1:])
	(*s)[len(*s)-1] = nil
	*s = (*s)[:len(*s)-1]
	return n
}

// 从items最后面踢掉一个Item
func (s *items) pop() (out Item) {
	index := len(*s) - 1
	out = (*s)[index]
	(*s)[index] = nil
	*s = (*s)[:index]
	return
}

// 从children最后面踢掉一个node指针
func (s *children) pop() (out *node) {
	index := len(*s) - 1
	out = (*s)[index]
	(*s)[index] = nil
	*s = (*s)[:index]
	return
}

// 清掉指定位置，及其之后位置的Item
func (s *items) truncate(index int) {
	var toClear items
	*s, toClear = (*s)[:index], (*s)[index:] // 区分需要清空的部分
	for len(toClear) > 0 {                   // 循环处理，设置需要清理的部分为nil，利于GC
		toClear = toClear[copy(toClear, nilItems):]
	}
}

// 清掉指定位置，及其之后位置的node指针
func (s *children) truncate(index int) {
	var toClear children
	*s, toClear = (*s)[:index], (*s)[index:]
	for len(toClear) > 0 {
		toClear = toClear[copy(toClear, nilChildren):]
	}
}

// items内查找item的应当插入的位置，如果已经存在，返回true
func (s items) find(item Item) (index int, found bool) {
	i := sort.Search(len(s), func(i int) bool { return item.Less(s[i]) }) // 二分查找
	// 到此，s[i]是第一个大于item的Item，因此看看s[i-1]是否和item相等
	if i > 0 && !s[i-1].Less(item) {
		return i - 1, true
	}
	return i, false
}

// 返回一个对于该copyOnWriteContext可更新的node
func (n *node) mutableFor(cow *copyOnWriteContext) *node {
	if n.cow == cow { // 就是同一个cow直接返回本node
		return n
	}
	// 创建一个新node，复制原node中的内容
	out := cow.newNode() //out来自cow中的freelist，可能是新建的也可能是重用的
	if cap(out.items) >= len(n.items) {
		//items的cap足够的时候，直接复制
		out.items = out.items[:len(n.items)]
	} else {
		// cap不够需要新建一个
		// TODO 这边是不是可以按照items和children的cap来分配最合适的node
		// 事实上，node是分配的开销应该很cheap，items和children的重新分配是昂贵的
		// 所以，freelist，是不是增加根据items和children的cap排序的list
		out.items = make(items, len(n.items), cap(n.items))
	}
	copy(out.items, n.items)
	//复制children
	if cap(out.children) >= len(n.children) {
		out.children = out.children[:len(n.children)]
	} else {
		out.children = make(children, len(n.children), cap(n.children))
	}
	copy(out.children, n.children)
	return out
}

// 复制children指定位置的指向的node
func (n *node) mutableChild(i int) *node {
	c := n.children[i].mutableFor(n.cow)
	n.children[i] = c
	return c
}

// split 在给定位置分裂给定的node. 当前node收缩,指定位置变成一个Item，指定位置之后的的items/children变成一个新的node，用来像上层注册
func (n *node) split(i int) (Item, *node) {
	item := n.items[i]
	next := n.cow.newNode()
	next.items = append(next.items, n.items[i+1:]...)
	n.items.truncate(i)
	if len(n.children) > 0 {
		next.children = append(next.children, n.children[i+1:]...)
		n.children.truncate(i + 1)
	}
	return item, next
}

// 检查一个子Node是否应该分裂，如果应该，就执行分裂.每次插入到的时候检查，插入之后不检查
func (n *node) maybeSplitChild(i, maxItems int) bool {
	// 检查当前节点Item数量是否到达分裂条件
	if len(n.children[i].items) < maxItems {
		return false
	}
	// 获取可写的节点
	first := n.mutableChild(i)
	// 分裂，获取item和新的node
	item, second := first.split(maxItems / 2)
	// 注册新的item
	n.items.insertAt(i, item)
	// 注册新的node
	n.children.insertAt(i+1, second)
	return true
}

// 插入一个Item到以本节点为root的子树中
func (n *node) insert(item Item, maxItems int) Item {
	// 本node查找，查找到具体位置
	i, found := n.items.find(item)
	if found {
		// 找到就用新的item替换，返回旧的item
		out := n.items[i]
		n.items[i] = item
		return out
	}
	// 如果是叶子节点，往i处插入一个item
	if len(n.children) == 0 {
		n.items.insertAt(i, item)
		return nil
	}
	// 不是叶子节点，看看i处的子Node是否需要分裂
	if n.maybeSplitChild(i, maxItems) {
		// 分裂了，导致当前node的变化，需要重新定位i
		inTree := n.items[i] // 获取新升级的item
		switch {
		case item.Less(inTree):
			// 要插入的item比分裂产生的item小，i没改变
		case inTree.Less(item):
			i++ // 要插入的item比分裂产生的item大，i++
		default:
			// 分裂升level的item和插入的item一致，替换
			out := n.items[i]
			n.items[i] = item
			return out
		}
	}
	// 不在本层，下层node递归处理
	return n.mutableChild(i).insert(item, maxItems)
}

// 查找指定的Item
func (n *node) get(key Item) Item {
	i, found := n.items.find(key)
	if found {
		// 本层发现，直接返回
		return n.items[i]
	} else if len(n.children) > 0 {
		// 下层继续递归查询
		return n.children[i].get(key)
	}
	// 未找到返回nil
	return nil
}

// 返回全树最小Item
func min(n *node) Item {
	if n == nil {
		return nil
	}
	for len(n.children) > 0 {
		n = n.children[0]
	}
	if len(n.items) == 0 {
		return nil
	}
	return n.items[0]
}

// 返回全树最大Item
func max(n *node) Item {
	if n == nil {
		return nil
	}
	for len(n.children) > 0 {
		n = n.children[len(n.children)-1]
	}
	if len(n.items) == 0 {
		return nil
	}
	return n.items[len(n.items)-1]
}

type toRemove int

const (
	removeItem toRemove = iota // 移除一个Item
	removeMin                  // 移除子树中最小的Item
	removeMax                  // 移除子树中最大的Item
)

// 从以本节点为根节点的子树中移除一个Item
func (n *node) remove(item Item, minItems int, typ toRemove) Item {
	var i int
	var found bool
	switch typ {
	case removeMax: // 移除最大一个
		if len(n.children) == 0 {
			// 叶子节点，移除最后一个item
			return n.items.pop()
		}
		i = len(n.items) // 不是叶子节点，获取对应子node的索引
	case removeMin: // 移除最小一个
		if len(n.children) == 0 {
			// 叶子节点，移除第一个item
			return n.items.removeAt(0)
		}
		i = 0 // 不是叶子节点，获取对应子node的索引
	case removeItem: // 移除一个Item
		i, found = n.items.find(item)
		if len(n.children) == 0 {
			// 叶子节点
			if found {
				// 找到了，移除
				return n.items.removeAt(i)
			}
			// 没找到，返回nil
			return nil
		}
		// 不是叶子节点，获取对应子node的索引,即i
	default:
		panic("invalid type") //无效的类型直接panic
	}
	// 处理子node
	if len(n.children[i].items) <= minItems {
		// 子node的items数量不足，应该从相邻节点偷元素或者合并处理
		return n.growChildAndRemove(i, item, minItems, typ)
	}
	child := n.mutableChild(i) // 复制i位置的node
	// 有足够的items或者做过偷元素和合并操作了.
	if found {
		// 接上面removeItem情况下,item存在于i位置,和我们可以对子node做一些预处理, 因为到这里，已经可以保证子node的items的数量肯定大于minItems
		out := n.items[i]
		// 使用一个特殊的'remove'调用对i位置的item实行一个预处理
		n.items[i] = child.remove(nil, minItems, removeMax)
		return out
	}
	// 最后递归调用.  到了这里，it不存在于这个node且child对于删除来说足够大，不会出发合并
	return child.remove(item, minItems, typ)
}

// growChildAndRemove 增长一个'i'位置的node去确保足够大于minItems，然后执行实际的移除操作
func (n *node) growChildAndRemove(i int, item Item, minItems int, typ toRemove) Item {
	if i > 0 && len(n.children[i-1].items) > minItems { //children[i]不是最左位置，children[i]都可以从他左侧children[i-1]偷一个item过来，当然children[i-1]的item要足够多
		// 从children[i-1]偷
		child := n.mutableChild(i)            // 获取可写的children[i]，它是待删除item的node
		stealFrom := n.mutableChild(i - 1)    // 获取可写的children[i-1]，作为被偷的节点
		stolenItem := stealFrom.items.pop()   // 移除children[i-1]的最后一个item，并且取得这个被移除的item
		child.items.insertAt(0, n.items[i-1]) // children[i]的items头部插入本node的items[i-1]
		n.items[i-1] = stolenItem             // 本node的items[i-1]设置成偷来的那个item
		if len(stealFrom.children) > 0 {      // 不是叶子节点还要处理一下children
			child.children.insertAt(0, stealFrom.children.pop()) // 将被偷的node的最后一个children，带处理的node的children的最前面
		}
		// 以下是i在最左位置，或者，children[i-1]的item数量不足，不能被偷了
	} else if i < len(n.items) && len(n.children[i+1].items) > minItems { //children[i]不是最右位置，children[i]都可以从他右侧children[i+1]偷一个item过来，当然children[i+1]的item要足够多
		// 从children[i+1]偷
		child := n.mutableChild(i)                    // 获取可写的children[i]，它是待删除item的node
		stealFrom := n.mutableChild(i + 1)            // 获取可写的children[i+1]，作为被偷的节点
		stolenItem := stealFrom.items.removeAt(0)     // 移除children[i+1]的第一个item，并且取得这个被移除的item
		child.items = append(child.items, n.items[i]) // children[i]的items尾部插入本node的items[i]
		n.items[i] = stolenItem                       // 本node的items[i]设置成偷来的那个item
		if len(stealFrom.children) > 0 {              // 不是叶子节点还要处理一下children
			child.children = append(child.children, stealFrom.children.removeAt(0)) // 将被偷的node的第一个children，带处理的node的children的最后面
		}
		// 以下是
		// i在最右位置，但是左侧node的item不够，不能被偷
		// i在最左位置，但是右侧node的item不够，不能被偷
		// i在中间位置，但是左右node的item都不够，不能被偷
	} else {
		if i >= len(n.items) { // 待处理的是最右一个child
			i-- // i--,因为下面处理会和右侧的node合并，原来处理的i，就变成合并后的i--了
		}
		child := n.mutableChild(i) // 获取可写的children[i],，它是合并后待删除item的node
		// 和右侧node合并
		mergeItem := n.items.removeAt(i)                                // 砍掉合并位置i处的item，这个item会被降级到合并后的node里
		mergeChild := n.children.removeAt(i + 1)                        // 砍掉合并的两个node的后一个node
		child.items = append(child.items, mergeItem)                    // 将mergeItem放回合并后node的item
		child.items = append(child.items, mergeChild.items...)          // 将后一个node的item合并进来
		child.children = append(child.children, mergeChild.children...) // 将后一个item的child合并进来
		n.cow.freeNode(mergeChild)                                      // 回收那些释放掉的节点
	}
	return n.remove(item, minItems, typ) // 执行删除处理
}

type direction int

const (
	descend = direction(-1) // 反向
	ascend  = direction(+1) // 正向
)

// debug用的，打印节点结构
func (n *node) print(w io.Writer, level int) {
	fmt.Fprintf(w, "%sNODE:%v\n", strings.Repeat("  ", level), n.items)
	for _, c := range n.children {
		c.print(w, level+1)
	}
}

// 复制树，Clone 不应该 被并发调用，但是一旦Clone完成，两个btree可以并发使用。
// 原先的btree结构被标记成只读被clone后的t和t2共享.  写t和t2都会使用copy-on-writ逻辑，每当修改原始node的时候，会创建一个新node。
// 读操作没有性能损耗.写操作最初会有点减速由于额外的内存分片和复制因为copy-on-writ逻辑, 最后会收敛于原始树的原始性能特征.
func (t *BTree) Clone() (t2 *BTree) {
	// 创建两个全新的copyOnWriteContext
	// 这个操作实际创建了3个树:
	//  原来的树
	//  新的树t
	//  新的树t2
	cow1, cow2 := *t.cow, *t.cow // 创建两个全新的copyOnWriteContext，注意他们指向的底层freelist是同一个
	out := *t                    // 复制一个btree元信息，根节点是同一个
	t.cow = &cow1                // 重置当前btree元信息的copyOnWriteContext，所以，clone之后，的btree再做修改就会因为cow的不同，会触发mutableFor
	out.cow = &cow2              // 新btree也重置btree元信息的copyOnWri，更新也会触发mutableFor
	return &out
}

// 每个节点允许的最大Item数量
func (t *BTree) maxItems() int {
	return t.degree*2 - 1
}

// 每个节点允许的最小Item数量，不包括root节点
func (t *BTree) minItems() int {
	return t.degree - 1
}

// ReplaceOrInsert 存在就替换，并返回旧的，不存在插入，返回nil
func (t *BTree) ReplaceOrInsert(item Item) Item {
	if item == nil { //这边是个bug吧，Item是个interface，
		panic("nil item being added to BTree")
	}
	if t.root == nil { // root node 不存在
		t.root = t.cow.newNode()                  // 从freelist里搞一个
		t.root.items = append(t.root.items, item) // 新增这个Item
		t.length++                                // item数量++
		return nil
	} else { // root node 存在
		t.root = t.root.mutableFor(t.cow)      // 获取本btree可以写的root node
		if len(t.root.items) >= t.maxItems() { // 如果根节点够大了，需要分裂.跟节点分裂有点特殊，根节点分裂意味着加层，其他节点分裂向上节点注册就行
			item2, second := t.root.split(t.maxItems() / 2)            //获取中间一个item:item[degree-1],和后面的一个node
			oldroot := t.root                                          // 保存旧root，实际是旧root的前半部分
			t.root = t.cow.newNode()                                   // 创建新root
			t.root.items = append(t.root.items, item2)                 // 将中间的item放到新的root中
			t.root.children = append(t.root.children, oldroot, second) // 将分裂后的两个node放到下一层
		}
	}
	out := t.root.insert(item, t.maxItems()) // 正式插入
	if out == nil {
		t.length++
	}
	return out
}

// 删除实现
func (t *BTree) deleteItem(item Item, typ toRemove) Item {
	if t.root == nil || len(t.root.items) == 0 { //没有元素直接返回
		return nil
	}
	t.root = t.root.mutableFor(t.cow)                       // 获取可写root
	out := t.root.remove(item, t.minItems(), typ)           // 从root开始查找并移除
	if len(t.root.items) == 0 && len(t.root.children) > 0 { // 删除之后，可能由于底层合并，导致root node空悬，这个时候应废弃root层
		oldroot := t.root
		t.root = t.root.children[0]
		t.cow.freeNode(oldroot)
	}
	if out != nil { //成功移除了一个，元素数量减一
		t.length--
	}
	return out
}

// 删除一个指定元素
func (t *BTree) Delete(item Item) Item {
	return t.deleteItem(item, removeItem)
}

// 删除树中最小的一个元素
func (t *BTree) DeleteMin() Item {
	return t.deleteItem(nil, removeMin)
}

// 删除树中最大的一个元素
func (t *BTree) DeleteMax() Item {
	return t.deleteItem(nil, removeMax)
}

// 迭代处理
// dir参数表示迭代方向
// start参数表示迭代处理的开始限
// stop参数表示迭代处理的结束限
// includeStart参数表示是否包含开始限
// hit参数
// iter参数表示迭代过程中的处理函数
func (n *node) iterate(dir direction, start, stop Item, includeStart bool, hit bool, iter ItemIterator) (bool, bool) {
	var ok, found bool
	var index int
	switch dir {
	case ascend: // 正序迭代
		if start != nil { // 开始Item不为nil
			index, _ = n.items.find(start) // 重新定位开始的位置 index位置的item >= start
		}
		for i := index; i < len(n.items); i++ { // 正序遍历node的items
			if len(n.children) > 0 { // 如果有children，递归调用，深度优先遍历，这里应该会到最底层最左叶子node
				if hit, ok = n.children[i].iterate(dir, start, stop, includeStart, hit, iter); !ok {
					return hit, false
				}
			}
			if !includeStart && !hit && start != nil && !start.Less(n.items[i]) {
				// start不为空(说明重定位过index，index位置的item >= start)
				// 不包括start(如果index位置的item刚好是start，显然不能调用iter,得想办法跳过start)
				// start >= i位置item时(这就上面想的办法，结合index位置的item >= start，能保证 index位置的item=start的情况下，index位置肯定符合除了hit以外的条件)
				// 我理解，hit的主要作用就是为true时，不走这段逻辑

				// 思考，start != nil && item[index]=start  && includeStart=false，情况下 设置 hit=true 跳过这个步骤，对start调用iter的意义？
				// 另外，当includeStart=true时，肯定不走这段逻辑，hit=false有何意义？
				// 下面所有调用中hit都为false，感觉这个参数失去了他的效果

				hit = true
				continue // 跳过对items[i]的iter调用
			}
			hit = true
			if stop != nil && !n.items[i].Less(stop) { // stop不为空，且，i位置的item已经不小于stop了，这个node的遍历可以结束了
				return hit, false
			}
			if !iter(n.items[i]) { // 对i位置的item调用iter处理
				return hit, false
			}
		}
		if len(n.children) > 0 { //每层的最右一个child要处理一下
			if hit, ok = n.children[len(n.children)-1].iterate(dir, start, stop, includeStart, hit, iter); !ok {
				return hit, false
			}
		}
	case descend: // 倒序迭代，注意start是大的，stop是小的
		if start != nil { // start不为空
			index, found = n.items.find(start) // 重新定位开始的位置 index位置的item >= start
			if !found {                        // 如果 index位置的item>start
				index = index - 1 // index减一，因为index是第一个大于start的位置，减一导致 index位置的item < start
			}
			// 到这里，保证 index位置的item <= start
		} else {
			index = len(n.items) - 1 // start为空，直接让index指向最右的一个位置
		}
		for i := index; i >= 0; i-- { // 倒序遍历node的items
			if start != nil && !n.items[i].Less(start) { // start不为空场合，items[i]不小于start
				if !includeStart || hit || start.Less(n.items[i]) { //不包括start的场合，判断了items[i]=start的时候，跳过iter处理
					continue
				}
			}
			if len(n.children) > 0 { // 如果有children，递归调用，深度优先遍历，这里应该会到最底层最右叶子node
				if hit, ok = n.children[i+1].iterate(dir, start, stop, includeStart, hit, iter); !ok {
					return hit, false
				}
			}
			if stop != nil && !stop.Less(n.items[i]) { // stop不为空，且，stop已经不比i位置的item小了，这个node的遍历可以结束了
				return hit, false //	continue
			}
			hit = true
			if !iter(n.items[i]) { // 对i位置的item调用iter处理
				return hit, false
			}
		}
		if len(n.children) > 0 { // //每层的最左一个child要处理一下
			if hit, ok = n.children[0].iterate(dir, start, stop, includeStart, hit, iter); !ok {
				return hit, false
			}
		}
	}
	return hit, true
}

// 正序迭代范围[greaterOrEqual, lessThan)内的所有Item直到iterator函数返回false
func (t *BTree) AscendRange(greaterOrEqual, lessThan Item, iterator ItemIterator) {
	if t.root == nil {
		return
	}
	t.root.iterate(ascend, greaterOrEqual, lessThan, true, false, iterator)
}

// 正序迭代范围[first, pivot)内的所有Item直到iterator函数返回false
func (t *BTree) AscendLessThan(pivot Item, iterator ItemIterator) {
	if t.root == nil {
		return
	}
	t.root.iterate(ascend, nil, pivot, false, false, iterator)
}

// 正序迭代范围[pivot, last]内的所有Item直到iterator函数返回false
func (t *BTree) AscendGreaterOrEqual(pivot Item, iterator ItemIterator) {
	if t.root == nil {
		return
	}
	t.root.iterate(ascend, pivot, nil, true, false, iterator)
}

// 正序迭代范围[first, last]内的所有Item直到iterator函数返回false
func (t *BTree) Ascend(iterator ItemIterator) {
	if t.root == nil {
		return
	}
	t.root.iterate(ascend, nil, nil, false, false, iterator)
}

// 反序迭代范围[lessOrEqual, greaterThan)内的所有Item直到iterator函数返回false
func (t *BTree) DescendRange(lessOrEqual, greaterThan Item, iterator ItemIterator) {
	if t.root == nil {
		return
	}
	t.root.iterate(descend, lessOrEqual, greaterThan, true, false, iterator)
}

// 反序迭代范围[pivot, first]内的所有Item直到iterator函数返回false
func (t *BTree) DescendLessOrEqual(pivot Item, iterator ItemIterator) {
	if t.root == nil {
		return
	}
	t.root.iterate(descend, pivot, nil, true, false, iterator)
}

// 反序迭代范围[last, pivot)内的所有Item直到iterator函数返回false
func (t *BTree) DescendGreaterThan(pivot Item, iterator ItemIterator) {
	if t.root == nil {
		return
	}
	t.root.iterate(descend, nil, pivot, false, false, iterator)
}

// 正序迭代范围[last, first]内的所有Item直到iterator函数返回false
func (t *BTree) Descend(iterator ItemIterator) {
	if t.root == nil {
		return
	}
	t.root.iterate(descend, nil, nil, false, false, iterator)
}

// 查找一个Item
func (t *BTree) Get(key Item) Item {
	if t.root == nil {
		return nil
	}
	return t.root.get(key)
}

// 返回全树最小Item
func (t *BTree) Min() Item {
	return min(t.root)
}

// 返回全树最大Item
func (t *BTree) Max() Item {
	return max(t.root)
}

// 判断树内是否拥有这个Item
func (t *BTree) Has(key Item) bool {
	return t.Get(key) != nil
}

// 树中的Item数量
func (t *BTree) Len() int {
	return t.length
}

// 清空整个树. 如果addNodesToFreelist是true,尝试回收Node直到freelist满了. 否则整个树解引用，正常GC
func (t *BTree) Clear(addNodesToFreelist bool) {
	if t.root != nil && addNodesToFreelist {
		t.root.reset(t.cow)
	}
	t.root, t.length = nil, 0
}

// 递归依次释放子树节点.  如果freelist满了会立即退出
func (n *node) reset(c *copyOnWriteContext) bool {
	for _, child := range n.children {
		if !child.reset(c) {
			return false
		}
	}
	return c.freeNode(n) != ftFreelistFull
}
