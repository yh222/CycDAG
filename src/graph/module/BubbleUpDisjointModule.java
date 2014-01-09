package graph.module;

import graph.core.CommonConcepts;
import graph.core.DAGEdge;
import graph.core.DAGNode;
import graph.core.Edge;
import graph.core.Node;
import graph.core.StringNode;
import graph.inference.CommonQuery;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;

import util.Pair;

/**
 * The objective of this module is to merge low level disjoint edges to a higher
 * level disjoint edge as many as possible.
 * 
 * The module will explore existing disjoint edges with a button-up sequence.
 * Each time a disjoint edge found, for example, between node A and node B, the
 * method will see if it's possible to create a disjoint from each parent node
 * of node A to node B.
 */
public class BubbleUpDisjointModule extends DAGModule<Collection<DAGEdge>> {
	private static final long serialVersionUID = -5748776310515109216L;
	private transient RelatedEdgeModule relEdgeModule_;
	private transient TransitiveIntervalSchemaModule transitiveModule_;
	private transient QueryModule queryModule_;
	/*
	 * Assuming the maximum distance from "Thing"(depth) for every disjoint edge
	 * is less than 100
	 */
	private static int ARRAYSIZE = 100;
	// ArrayList of ArrayLists, with fixed size 100(depth<=100)
	private List<List<Pair<Node, Node>>> toExplore_ = new ArrayList<List<Pair<Node, Node>>>(
			Collections.nCopies(100, new ArrayList<Pair<Node, Node>>()));
	private HashSet<Pair<Node, Node>> exploredPairs_ = new HashSet<Pair<Node, Node>>();

	/*
	 * Node: toExplore_ and exploredPairs_ represent different set of pairs,
	 * their base sets are always disjointed.
	 * 
	 * toExplore_'s pairs come directly from each node of each d-edge, like
	 * n1->n2
	 * 
	 * exploredPairs_'s pairs come from one node of an d-edge + one parent of
	 * the other node of the d-edge, like n1->n2.p1, n1->n2.p2 etc.
	 */

	// Constructor, not used yet
	public BubbleUpDisjointModule() {
	}

	@Override
	public Collection<DAGEdge> execute(Object... arg0)
			throws IllegalArgumentException, ModuleException {
		// TODO: manually call the bubble up process
		return null;
	}

	@Override
	public boolean initialisationComplete(Collection<DAGNode> nodes,
			Collection<DAGEdge> edges, boolean forceRebuild) {

		Node creator = new StringNode("BubbleUpDisjointModule");

		// TODO: Check depth module and TransitiveIntervalSchema module have
		// done the work

		// Get all disjoint edges
		Collection<Edge> disjointEdges = relEdgeModule_.execute(
				CommonConcepts.DISJOINTWITH.getNode(dag_), 1);
		// Sort edges according to the maximum distance to THING node
		// Result of sorting will stored at toExplore_
		sortToExplore(disjointEdges);

		// Loop backwards
		for (int i = toExplore_.size(); i > 0; i--) {
			for (Pair<Node, Node> pair : toExplore_.get(i)) {
				// Find all Min parent nodes for source node
				Collection<Node> minGenls = CommonQuery.MINGENLS.runQuery(dag_,
						pair.objA_);
				// Try to establish disjoint edge from (each parent of A) to (B)
				for (Node n : minGenls) {
					bubbleParentToTarget(creator, n, pair.objB_);
				}
			}
		}

		return false;

	}

	/**
	 * Sort the pairs from disjoint edges according to the distance from source
	 * side
	 * 
	 * For each pair added, the first node will be source and second node will
	 * be target. (For source node, parent nodes will be explored in attempt to
	 * establish disjoint with target node)
	 */
	private void sortToExplore(Collection<Edge> disjointEdges) {
		int temp;

		for (Edge e : disjointEdges) {
			// Get depth of first node and add the pair (Node1->Node2) to
			// appropriate location in the array
			temp = Integer.getInteger(((DAGNode) e.getNodes()[1])
					.getProperty("depth"));
			if (temp > ARRAYSIZE) {// TODO: display error message
			} else {
				toExplore_.get(temp).add(
						new Pair<Node, Node>(e.getNodes()[1], e.getNodes()[2]));
			}
			// Second node, the pair is (Node2->Node1)
			temp = Integer.getInteger(((DAGNode) e.getNodes()[2])
					.getProperty("depth"));
			if (temp > ARRAYSIZE) {// TODO: display error message
			} else {
				toExplore_.get(temp).add(
						new Pair<Node, Node>(e.getNodes()[2], e.getNodes()[1]));
			}
		}
	}

	public void bubbleUpDisjoints(Node creator) {

	}

	/**
	 * Objective of this method is to prove disjoint between a parent node of a
	 * collection and a single target node. The method will go through each
	 * child node of the parent and check relationship with the target node. The
	 * method won't make change if any of these apply: 1, The pair of parent
	 * node and target node has been explored. 2, The parent node(or its parent)
	 * already has disjoint with the target node. 3, A child of the parent node
	 * found conjoint with target node.
	 * 
	 * collectionParent: The parent node exploredEdges: The hash set contains
	 * pairs of nodes that have been explored
	 */
	private void bubbleParentToTarget(Node creator, Node collectionParent,
			Node targetNode) {
		// If this is a sibling disjoint edge(parent of A genls B), ignore it.
		if (collectionParent.equals(targetNode))
			return;

		// If the pair of nodes has been explored before, skip
		if (exploredPairs_.contains(new Pair<Node, Node>(targetNode,
				collectionParent)))
			return;
		exploredPairs_.add(new Pair<Node, Node>(targetNode, collectionParent));
		// If the collectionParent is already disjoint with targetNode, skip it.
		if (queryModule_.prove(CommonConcepts.DISJOINTWITH.getNode(dag_),
				collectionParent, targetNode))
			return;
		// Get all highest child nodes of collectionParent
		// System.out.println("Run query at line 526");
		Collection<Node> children = CommonQuery.MAXSPECS.runQuery(dag_,
				collectionParent);
		if (children.size() == 0) {
			System.out.println("no child");
			return;
		}
		System.out.println(collectionParent.getName() + " has Children size:"
				+ children.size() + " ,target: " + targetNode.getName());

		int disjointcount = 0;
		int undefinedcount = 0;
		// TODO(not yet critical): random sampling for x times when children
		// size is very large
		for (Node child : children) {
			// if child disjoint with targetNode, count++
			// System.out.println("Run query at line 540");
			if (queryModule_.prove(CommonConcepts.DISJOINTWITH.getNode(dag_),
					targetNode, child))
				disjointcount++;
			// else, check if child conjoint with targetNode
			else {
				// if any conjoint found between the child and
				// targetNode,skip
				if (transitiveModule_.execute(true, targetNode, child) != null
						|| transitiveModule_.execute(false, targetNode, child) != null)
					return;
				else
					undefinedcount++;
			}
			// The impossibility of disjoint can be explored before loop
			// through all the child, since there is a statistic threshold
			if((undefinedcount/children.size())>0.9){
				return;
			}
		}
		// Now use the count of disjoint found between collectionParent's
		// children and targetNode, and the amount of child to decide if
		// collectionParent disjoint with
		// targetNode
		boolean isDisjointed = false;
		double p = (double) disjointcount / children.size();
		System.out.println("p=" + p);

		// TODO: Many magic numbers here, need to be reasoned
		if (children.size() <= 10) {
			System.out.println("Don't decide since children size is too small");

		} else if (children.size() > 10 && p > 0.1) {
			isDisjointed = true;
		}

		if (isDisjointed) {
			// If they are likely to be disjointed, create a new disjoint edge
			dag_.findOrCreateEdge(creator, new Node[] {
					CommonConcepts.DISJOINTWITH.getNode(dag_),
					collectionParent, targetNode }, false);
			System.out.println("Disjoint added btween:"
					+ collectionParent.getName() + " " + targetNode.getName());
		}
	}

}
