sig Node {
	children : set Node
}
sig Leaf extends Node {}
one sig Root in Node {}

sig Red, Black in Node {}

// EXPLICITAR TODAS AS PROPRIEDADES QUE TORNAM UMA ÁRVORE BINÁRIA RED-BLACK VÁLIDA.

pred Inv1 {
	// (1). Every node (non Leaf) is colored black or red.
	all n: Node | (n in Black or n in Red) and (n in Black implies n not in Red)
}

pred Inv2{
	// (2).
	all n: Node-Leaf | 
		// A node (non leaf) has to have 2 children
		#n.children = 2 and 
		// Both or one of its children can be leafs
		(some n1, n2: Leaf | n1 in n.children and n2 in n.children) and 
		// If two nodes are its children then they're different
		(some n1, n2: Node | n1 in n.children and n2 in n.children and n1 != n2) and
		// A node cannot be its own parent and its parent cannot be its child
		all n3: Node | n3 in n.children implies (n3 != n and n not in n3.children) and
		// If its children are all black, then the node is black
		(all n1: n.children | n1 in Black) implies n in Black	
}

pred Inv3{
	// (3). If a node is red, then both of its children are colored black.
  	all n: Node | n in Red implies n.children in Black
}

pred Inv4{
	// (4). Every leaf is NIL (has no children) and is colored black.
  	no children.Root and Root in Black
}

pred Inv5{
  	// (5). Every node is reachable from the root.
	// The path from a node (including root) to any of its descendant leafs contains the same amount of nodes colored black.
	Node-Root in Root.*(children)
  	all n: Node-Leaf | some l1,l2: Leaf | l1 in n.*(children) and l2 in n.*(children) and l1 != l2 implies some b1: *(children).l1, b2: *(children).l2 | b1 in Black and b2 in Black and b1 != b2 and #b1 = #b2
}

pred Invs {
	Inv1 and Inv2 and Inv3 and Inv4 and Inv5
}
