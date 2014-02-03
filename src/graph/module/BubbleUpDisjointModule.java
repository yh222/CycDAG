package graph.module;

import graph.core.CommonConcepts;
import graph.core.DAGEdge;
import graph.core.DAGNode;
import graph.core.Edge;
import graph.core.Node;
import graph.core.StringNode;
import graph.inference.CommonQuery;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Random;

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

	private Map<Integer, List<Pair<Node, Node>>> toExplore_ = new HashMap<Integer, List<Pair<Node, Node>>>();
	private HashSet<Pair<Node, Node>> exploredPairs_ = new HashSet<Pair<Node, Node>>();
	private HashSet<Node> rejectedEvidences_ = new HashSet<Node>();

	private static double THEP_ = 0.4;
	// The limitation for exploring children of each parent
	private static int MAXCHILDEXPLORATION_ = 500;
	private static int MINCHILDEXPLORATION_ = 10;
	
	private int disjointCreated_=0;

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

		initialisationComplete(dag_.getNodes(), dag_.getEdges(), false);
		return null;
	}

	@Override
	public boolean initialisationComplete(Collection<DAGNode> nodes,
			Collection<DAGEdge> edges, boolean forceRebuild) {
		System.out.print("Starting to bubble up disjoints...");
		Node creator = new StringNode("BubbleUpDisjointModule");

		relEdgeModule_ = (RelatedEdgeModule) dag_
				.getModule(RelatedEdgeModule.class);
		transitiveModule_ = (TransitiveIntervalSchemaModule) dag_
				.getModule(TransitiveIntervalSchemaModule.class);
		queryModule_ = (QueryModule) dag_.getModule(QueryModule.class);

		// TODO: Check depth module and TransitiveIntervalSchema module have
		// done the work

		// Get all disjoint edges
		Collection<Edge> disjointEdges = relEdgeModule_.execute(
				CommonConcepts.DISJOINTWITH.getNode(dag_), 1);
		// Sort edges according to the maximum distance to THING node
		// Result of sorting will stored at toExplore_
		sortToExplore(disjointEdges);
		System.out.println("Pairs sorted");

		// Retrieve and sort indexes of lists organized by depth
		List<Integer> keyset = new ArrayList<Integer>(toExplore_.keySet());
		Collections.sort(keyset);
		
		// Loop backwards, from the greatest index
		int count = 0;
		int tenPercent = (disjointEdges.size() * 2) / 10;
		for (int i = keyset.size() - 1; i > 0; i--) {
			// null proof
			if (toExplore_.get(keyset.get(i)) == null) {
				continue;
			}
			for (int j = 0; j < toExplore_.get(keyset.get(i)).size(); j++) {
				Pair<Node, Node> pair = toExplore_.get(keyset.get(i)).get(j);
				// Find all Min parent nodes for source node
				Collection<Node> minGenls = CommonQuery.MINGENLS.runQuery(dag_,
						pair.objA_);
				// Try to establish disjoint edge from (each parent of A) to (B)
				for (Node n : minGenls) {
					bubbleParentToTarget(creator, n, pair.objB_);
				}
				count++;
				if (count % tenPercent == 0) {
					System.out.println((count / tenPercent * 10) + "% done");
					System.out.println(toExplore_.get(i).size() - j
							+ " pairs left, index= " + keyset.get(i));
				}
			}
		}
		System.out.println("Bubble up disjoints done");

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

			// In the case of function, the depth of node become null
			if (((DAGNode) e.getNodes()[1]).getProperty("depth") != null) {
				temp = Integer.parseInt(((DAGNode) e.getNodes()[1])
						.getProperty("depth"));
				if (toExplore_.get(temp) == null) {
					toExplore_.put(temp, new ArrayList<Pair<Node, Node>>());
				} else {
					toExplore_.get(temp).add(
							new Pair<Node, Node>(e.getNodes()[1],
									e.getNodes()[2]));
				}
			}

			// Second node, the pair is (Node2->Node1)
			if (((DAGNode) e.getNodes()[2]).getProperty("depth") != null) {
				temp = Integer.parseInt(((DAGNode) e.getNodes()[2])
						.getProperty("depth"));
				if (toExplore_.get(temp) == null) {
					toExplore_.put(temp, new ArrayList<Pair<Node, Node>>());
				} else {
					toExplore_.get(temp).add(
							new Pair<Node, Node>(e.getNodes()[2],
									e.getNodes()[1]));
				}
			}
		}
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
		if (rejectedEvidences_.contains(collectionParent))
			return;
		// If the collectionParent is already disjoint with targetNode, skip it.
		if (queryModule_.prove(CommonConcepts.DISJOINTWITH.getNode(dag_),
				collectionParent, targetNode))
			return;
		// Get all highest child nodes of collectionParent
		List<Node> children = new ArrayList<Node>(
				CommonQuery.MAXSPECS.runQuery(dag_, collectionParent));
		// Set upper bound of children size that to be explored
		int roundedchildrensize = children.size() > MAXCHILDEXPLORATION_ ? MAXCHILDEXPLORATION_
				: children.size();
		if (roundedchildrensize == 0) {
			return;
		} else if (roundedchildrensize <= MINCHILDEXPLORATION_) {
			// Don't decide if children size is too small
			return;
		}

		// Use the count of disjoint found between collectionParent's
		// children and targetNode, and the amount of child to decide if
		// collectionParent disjoint with targetNode
		boolean isDisjointed = false;
		double p = (double) countChildrenStatDisjointed(children, targetNode,
				roundedchildrensize) / roundedchildrensize;

		// TODO: magic number here, need to be reasoned
		if (p > THEP_) {
			//

			isDisjointed = true;
		}

		// TODO: for debug
		if (p * roundedchildrensize == -2) {
			System.out.println("Evidence rejected due to lack of similarity:"
					+ collectionParent.getName());
			rejectedEvidences_.add(collectionParent);
		} else if (p * roundedchildrensize > -1
				&& p * roundedchildrensize < THEP_ * -1) {
			System.out.println("Possible child:" + targetNode.getName()
					+ " is child of " + collectionParent.getName());
		}
		if (isDisjointed) {

			System.out.println("Disjoint added btween:"
					+ collectionParent.getName() + " " + targetNode.getName()
					+ ", with p=" + p + ", Sample size=" + children.size());
			try (PrintWriter out = new PrintWriter(new BufferedWriter(
					new FileWriter("out.txt", true)))) {
				boolean tempdisjointed;

				out.println(collectionParent.getName() + " "
						+ targetNode.getName() + ", p=" + p + ", Sample size="
						+ children.size());
				out.println("Content of collection:");
				for (Node c : children) {
					tempdisjointed = (queryModule_.prove(
							CommonConcepts.DISJOINTWITH.getNode(dag_),
							targetNode, c)) ? true : false;
					out.println("--"+c.getName() + " is disjointed to: " +targetNode.getName()+": "
							+ tempdisjointed);
				}

			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			// If they are likely to be disjointed, create a new disjoint edge
			// Write record to output file as well
			dag_.findOrCreateEdge(creator, new Node[] {
					CommonConcepts.DISJOINTWITH.getNode(dag_),
					collectionParent, targetNode }, false);
			disjointCreated_++;
			System.out.println(disjointCreated_+" disjoint edges created");
		}
	}

	// Return count of disjoint children
	private int countChildrenStatDisjointed(List<Node> children,
			Node targetNode, int roundedchildrensize) {
		int disjointcount = 0;
		int undefinedcount = 0;
		int randomsamplecountdown = MAXCHILDEXPLORATION_;
		boolean isLargeCollection = children.size() > MAXCHILDEXPLORATION_;
		Map<Node, Integer> similarityparent = new HashMap<Node, Integer>();
		Map<Node, Integer> similaritytype = new HashMap<Node, Integer>();

		Random random = new Random();
		// random sampling for LIMITCHILDEXPLORATION times when children size is
		// very large
		for (int i = 0; i < roundedchildrensize; i++) {
			Node child;
			if (isLargeCollection) {
				child = children.get(random.nextInt(roundedchildrensize));
				randomsamplecountdown--;
				if (randomsamplecountdown == 0) {
					break;
				}
			} else {
				child = children.get(i);
			}
			// get all parents for this child
			Collection<Node> allparents = CommonQuery.MINGENLS.runQuery(dag_,
					child);
			Collection<Node> alltypes = CommonQuery.MINISA.runQuery(dag_,
					targetNode);

			// Count number of appearance of each parent
			int t = 0;
			for (Node parent : allparents) {
				if (similarityparent.containsKey(parent)) {
					t = similarityparent.get(parent) + 1;
					similarityparent.put(parent, t);
				} else {
					similarityparent.put(parent, 1);
				}
			}

			// Count number of appearance of each type
			t = 0;
			for (Node type : alltypes) {
				if (similaritytype.containsKey(type)) {
					t = similaritytype.get(type);
					similaritytype.put(type, t++);
				} else {
					similaritytype.put(type, 1);
				}
			}

			// if child disjoint with targetNode, count++
			if (queryModule_.prove(CommonConcepts.DISJOINTWITH.getNode(dag_),
					targetNode, child)) {
				disjointcount++;
			} else {
				// else if any conjoint found between the child and
				// targetNode,skip
				if (transitiveModule_.execute(true, targetNode, child) != null
						|| transitiveModule_.execute(false, targetNode, child) != null)
					return disjointcount * -1;
				else
					undefinedcount++;
			}
			// The impossibility of disjoint can be explored before loop
			// through all the child, since there is a statistic threshold
			// TODO: magic number
			if ((undefinedcount / roundedchildrensize) > 1 - THEP_) {
				return -1;
			}
		}
		// Get a list of frequency of parents' appearance, to determine the
		// similarity of children
		// TODO: magic number: 8
		List<Map.Entry<Node, Integer>> mostfrequentparents = getMostFrequent(
				similarityparent, 8);

		List<Map.Entry<Node, Integer>> mostfrequenttypes = getMostFrequent(
				similaritytype, 8);

		// 2 comes from 3 used above
		// If there were not enough parents or similarty is low, return
		// nagative;
		if (mostfrequentparents.size() < 3
				|| mostfrequentparents.get(2).getValue() < roundedchildrensize * 0.2) {
			// TODO: Magic number 0.7
			if (mostfrequenttypes.size() < 3
					|| mostfrequenttypes.get(2).getValue() < roundedchildrensize * 0.2)
				return -2;
		}

		if (hasSimilarity(mostfrequentparents, mostfrequenttypes, targetNode,
				0.2)) {
			return -1 * disjointcount;
		}

		return disjointcount;
	}

	// Get a list(with "quantity" as list size) of parent nodes with most
	// frequency
	private List<Map.Entry<Node, Integer>> getMostFrequent(
			Map<Node, Integer> similarity, int quantity) {
		Iterator<Map.Entry<Node, Integer>> it = similarity.entrySet()
				.iterator();
		List<Map.Entry<Node, Integer>> list = new ArrayList<Map.Entry<Node, Integer>>();
		mapEntryComparator comaprator = new mapEntryComparator();

		while (it.hasNext()) {
			Map.Entry<Node, Integer> pair = it.next();
			if (list.size() < quantity) {
				list.add(pair);
			} else if (list.get(quantity - 1).getValue() < pair.getValue()) {
				list.set(quantity - 1, pair);
				// Sort the list from large to small
				Collections.sort(list, comaprator);
			}
			it.remove(); // avoids a ConcurrentModificationException
		}
		Collections.sort(list, comaprator);
		return list;
	}

	// An utility Comparator used to sort hashMap entries
	private class mapEntryComparator implements
			Comparator<Map.Entry<Node, Integer>> {
		@Override
		public int compare(final Map.Entry<Node, Integer> object1,
				final Map.Entry<Node, Integer> object2) {
			return object2.getValue().compareTo(object1.getValue());
		}
	}

	/*
	 * 
	 * */
	private boolean hasSimilarity(
			List<Map.Entry<Node, Integer>> mostfrequentparents,
			List<Map.Entry<Node, Integer>> mostfrequenttypes, Node targetNode,
			double threshold) {
		// get all parents for targetNode
		Collection<Node> allparents = CommonQuery.MINGENLS.runQuery(dag_,
				targetNode);
		Collection<Node> alltypes = CommonQuery.MINISA.runQuery(dag_,
				targetNode);
		int similaritycount = 0;
		int magicnumber = 2;

		for (Node p : allparents) {
			for (Map.Entry<Node, Integer> m : mostfrequentparents) {
				if (m.getKey().equals(p) && m.getValue() >= threshold
						&& similaritycount++ == magicnumber) {
					return true;
				}
			}
		}

		for (Node p : alltypes) {
			for (Map.Entry<Node, Integer> m : mostfrequenttypes) {
				if (m.getKey().equals(p) && m.getValue() >= threshold
						&& similaritycount++ == magicnumber) {
					return true;
				}
			}
		}
		return false;
	}
}
