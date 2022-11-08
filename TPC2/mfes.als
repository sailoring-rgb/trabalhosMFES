sig Node {
	children : set Node
}
sig Leaf extends Node {}
one sig Root in Node {}

sig Red, Black in Node {}


pred Invs {
	// (1). Every node (non Leaf) is colored black or red.
	all n: Node | (n in Black or n in Red) and (n in Black implies n not in Red)

	// (2). Every inside node (non leaf) has exactly two children and one or both can be leafs.
  	// A node cannot be its own child.
  	// A node cannot be a child and a parent to another node.
  	// A node can only have one parent.
  	all n: Node-Leaf | some n1, n2: Node | all n3: Node | n1 in n.children and n2 in n.children and n1 != n2 and n3 in n.children implies (n3 = n1 or n3 = n2)
  	all n: Node | n not in n.children
  	all n1: Node | all n2: n1.children | n1 not in n2.children
  	all n1,n2,n3: Node | n3 in n1.children and n3 in n2.children implies n1 = n2
  
	// (3). If a node is red, then both of its children are colored black.
  	all n: Node | n in Red implies n.children in Black
  
	// (4). Every leaf is NIL (has no children) and is colored black.
  	// The root is not any node's child and it's always black.
  	no children.Root and Root in Black
	all l: Leaf | no l.children and l in Black
    
  	// (5). Every node is reachable from the root.
	// The path from a node (including root) to any of its descendant leafs contains the same amount of nodes colored black.
	Node-Root in Root.*(children)
  	all n: Node-Leaf | some l1,l2: Leaf | l1 in n.*(children) and l2 in n.*(children) and l1 != l2 implies some b1: *(children).l1, b2: *(children).l2 | b1 in Black and b2 in Black and b1 != b2 and #b1 = #b2
}
