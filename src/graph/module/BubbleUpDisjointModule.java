package graph.module;

import graph.core.CommonConcepts;
import graph.core.DAGEdge;
import graph.core.DAGNode;
import graph.core.Edge;
import graph.core.Node;
import graph.core.StringNode;
import graph.inference.CommonQuery;
import graph.inference.QueryObject;
import graph.inference.Substitution;
import graph.inference.VariableNode;

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
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

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

	// TODO: magic number here, need to be reasoned
	private static double THEP_ = 0.3;
	// The limitation for exploring children of each parent
	private static int MAXCHILDEXPLORATION_ = 500;
	private static int MINCHILDEXPLORATION_ = 10;
	// Threshold for Standard Deviation
	private static int STDDEVTHRESHOLD_ = 10;
	// count of disjoint edges created
	private int disjointCreated_ = 0;

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
					List<Node> children = checkConstraintAndGetChildren(n,
							pair.objB_);
					if (children != null)
						bubbleCollectionToTarget(creator, n, pair.objB_,
								children);
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

	/*
	 * Check constraints, avoid duplicated operations and return a list of child
	 * nodes, of collectionParent.
	 */
	private List<Node> checkConstraintAndGetChildren(Node collectionParent,
			Node targetNode) {
		// If this is a sibling disjoint edge(parent of A genls B), ignore it.
		if (collectionParent.equals(targetNode))
			return null;

		// If the pair of nodes has been explored before, skip
		if (exploredPairs_.contains(new Pair<Node, Node>(targetNode,
				collectionParent)))
			return null;
		exploredPairs_.add(new Pair<Node, Node>(targetNode, collectionParent));
		if (rejectedEvidences_.contains(collectionParent))
			return null;
		// If the collectionParent is already disjoint with targetNode, skip it.
		if (queryModule_.prove(CommonConcepts.DISJOINTWITH.getNode(dag_),
				collectionParent, targetNode))
			return null;
		// Get all highest child nodes of collectionParent
		List<Node> children = new ArrayList<Node>(
				CommonQuery.MAXSPECS.runQuery(dag_, collectionParent));
		// Set upper bound of children size that to be explored

		if (children.size() <= MINCHILDEXPLORATION_) {
			// Don't decide if children size is too small
			return null;
		}
		return children;
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
	private void bubbleCollectionToTarget(Node creator, Node collectionParent,
			Node targetNode, List<Node> children) {

		int roundedchildrensize = children.size() > MAXCHILDEXPLORATION_ ? MAXCHILDEXPLORATION_
				: children.size();

		// Use the count of disjoint found between collectionParent's
		// children and targetNode, and the amount of child to decide if
		// collectionParent disjoint with targetNode

		saveAndPrintOutput(
				creator,
				collectionParent,
				targetNode,
				children,
				roundedchildrensize,
				countChildrenStatDisjointed(collectionParent, children,
						targetNode, roundedchildrensize));
	}

	// Save the disjoint(if found one) and print other stats
	private void saveAndPrintOutput(Node creator, Node collectionParent,
			Node targetNode, List<Node> children, int roundedchildrensize,
			int count) {
		// TODO: for debug
		double p = (double) count / roundedchildrensize;
		if (count == -2) {
			System.out.println("Evidence rejected due to lack of similarity:"
					+ collectionParent.getName());
			rejectedEvidences_.add(collectionParent);
		} else if (count == -4) {
			System.out
					.println("Evidence target rejected due to lack of similarity:"
							+ collectionParent.getName());
			rejectedEvidences_.add(collectionParent);
		} else if (count > -1 && count < THEP_ * -1) {
			System.out.println("Possible child:" + targetNode.getName()
					+ " is child of " + collectionParent.getName());
		} else if (p > THEP_) {
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
					out.println("--" + c.getName() + " is disjointed to: "
							+ targetNode.getName() + ": " + tempdisjointed);
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
			System.out.println(disjointCreated_ + " disjoint edges created");
		}
	}

	/*
	 * Return count of disjointed child. Return -3 if conjoint found. Return -2
	 * if the collection has high discretion. Return -1 if p's too low
	 */
	private int countChildrenStatDisjointed(Node collectionParent,
			List<Node> children, Node targetNode, int roundedchildrensize) {
		int disjointcount = 0;
		int undefinedcount = 0;

		boolean isLargeCollection = children.size() > MAXCHILDEXPLORATION_;
		Map<Node, Integer> similarityparent = new HashMap<Node, Integer>();

		Random random = new Random();
		// random sampling for LIMITCHILDEXPLORATION times when children size is
		// very large
		for (int i = 0, randomsamplecountdown = MAXCHILDEXPLORATION_; i < roundedchildrensize
				&& randomsamplecountdown > 0; i++, randomsamplecountdown--) {
			Node child;
			// Random sampling or iterate through the whole
			if (isLargeCollection) {
				child = children.get(random.nextInt(roundedchildrensize));
			} else {
				child = children.get(i);
			}

			updateSimilarityData(similarityparent, child);
			// if child disjoint with targetNode, count++
			if (queryModule_.prove(CommonConcepts.DISJOINTWITH.getNode(dag_),
					targetNode, child)
					&& isNotDirectlyDisjointed(targetNode, child)) {
				disjointcount++;
			} else {
				// else if any conjoint found between the child and
				// targetNode,skip
				if (transitiveModule_.execute(true, targetNode, child) != null
						|| transitiveModule_.execute(false, targetNode, child) != null)
					return -3;
				else
					undefinedcount++;
			}
			// The impossibility of disjoint can be explored before loop
			// through all the child, since there is a statistic threshold
			if ((undefinedcount / roundedchildrensize) > 1 - THEP_) {
				return -1;
			}
		}
		// Get a list of frequency of parents' appearance, to determine the
		// similarity of children
		// List<Map.Entry<Node, Integer>> sortedfrequentparents =
		// sortParentsByFrequency(similarityparent);

		// test if similarity is too low
		if (hasHighDiscretion(similarityparent, STDDEVTHRESHOLD_)) {
			return -2;
		}

		List<Node> targetchildren = new ArrayList<Node>(
				CommonQuery.MAXSPECS.runQuery(dag_, targetNode));
		isLargeCollection = targetchildren.size() > MAXCHILDEXPLORATION_;
		Map<Node, Integer> similaritytarget = new HashMap<Node, Integer>();
		int i = isLargeCollection ? MAXCHILDEXPLORATION_ : targetchildren
				.size();
		for (i = i - 1; i > 0; i--) {
			Node child;
			// Random sampling or iterate through the whole
			if (isLargeCollection) {
				child = targetchildren
						.get(random.nextInt(MAXCHILDEXPLORATION_));
			} else {
				child = targetchildren.get(i);
			}
			updateSimilarityData(similaritytarget, child);
		}
		if (hasHighDiscretion(similaritytarget, STDDEVTHRESHOLD_)) {
			return -4;
		}

		// if (hasSimilarityBetween(collectionParent, targetNode, 0.1)) {
		// System.out.println("rejected due to high similarity between:"
		// + targetNode.getName() + " " + collectionParent.getName());
		// return -1 * disjointcount;
		// }

		return disjointcount;
	}

	private boolean isNotDirectlyDisjointed(Node targetNode, Node child) {
		QueryObject qo = new QueryObject(
				CommonConcepts.DISJOINTWITH.getNode(dag_), targetNode, child);
		queryModule_.applyModule(
				CommonConcepts.ASSERTED_SENTENCE.getNodeName(), qo);
		if (qo.getJustification().isEmpty()) {
			return true;
		} else {
			return false;
		}
	}

	private void updateSimilarityData(Map<Node, Integer> similaritydata,
			Node node) {
		// get all parents(genls/isa) for this child
		Collection<Node> allparents = CommonQuery.ALLGENLS.runQuery(dag_, node);
		// allparents.addAll(CommonQuery.ALLISA.runQuery(dag_, child));

		// Count number of appearance of each parent
		int t = 0;
		for (Node parent : allparents) {
			if (similaritydata.containsKey(parent)) {
				t = similaritydata.get(parent) + 1;
				similaritydata.put(parent, t);
			} else {
				similaritydata.put(parent, 1);
			}
		}
	}

	// Sort and return a list of parents by their frequency
	private List<Map.Entry<Node, Integer>> sortParentsByFrequency(
			Map<Node, Integer> similarity) {
		List<Map.Entry<Node, Integer>> list = new ArrayList<Map.Entry<Node, Integer>>(
				similarity.entrySet());
		mapEntryComparator comaprator = new mapEntryComparator();
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

	// Test the discretion of the parents of the collection,return true if
	// discretion is high
	private boolean hasHighDiscretion(Map<Node, Integer> sortedfrequentparents,
			double deviationthreshold) {
		// Calculate mean
		double mean = 0;
		int colsize = sortedfrequentparents.size() - 1;
		for (Map.Entry<Node, Integer> e : sortedfrequentparents.entrySet()) {
			mean += e.getValue();
		}
		mean /= colsize;
		// Calculate variance
		double variance = 0;
		for (Map.Entry<Node, Integer> e : sortedfrequentparents.entrySet()) {
			variance += Math.pow(e.getValue() - mean, 2);
		}
		System.out.println("stdDev:" + Math.sqrt(variance / colsize));
		if (Math.sqrt(variance / colsize) > deviationthreshold
				|| Math.sqrt(variance / colsize) <= 0) {
			return true;
		}
		return false;
	}

	/*
	 * Check if the collection head has some degree of similarity with the
	 * target node
	 */
	private boolean hasSimilarityBetween(Node collectionHead, Node targetNode,
			double exploreTillPercentage) {

		int targetdepth = (int) (Integer.parseInt(((DAGNode) targetNode)
				.getProperty("depth")) * exploreTillPercentage);
		int headdepth = (int) (Integer.parseInt(((DAGNode) collectionHead)
				.getProperty("depth")) * exploreTillPercentage);
		Set<Node> explorednet = new HashSet<Node>();
		explorednet.add(targetNode);
		explorednet.add(collectionHead);
		List<Node> frontiertargetnode = new ArrayList<Node>(
				CommonQuery.MINGENLS.runQuery(dag_, targetNode));
		List<Node> frontiercollectionhead = new ArrayList<Node>(
				CommonQuery.MINGENLS.runQuery(dag_, collectionHead));
		System.out.println("targetdepth:" + targetdepth);
		System.out.println("headdepth:" + headdepth);

		while (targetdepth >= 0 || headdepth >= 0) {
			if (targetdepth-- >= 0) {
				if (!hasConjoint(explorednet, frontiertargetnode)) {
					explorednet.addAll(frontiertargetnode);
					frontiertargetnode = exploreNextFrontier(frontiertargetnode);
				} else {
					return true;
				}
			}

			if (headdepth-- >= 0) {
				if (!hasConjoint(explorednet, frontiercollectionhead)) {
					explorednet.addAll(frontiercollectionhead);
					frontiercollectionhead = exploreNextFrontier(frontiercollectionhead);
				} else {
					return true;
				}
			}
		}
		return false;
	}

	// Check if any element of the list exist in the set
	private boolean hasConjoint(Set<Node> explorednet, List<Node> frontier) {
		for (Node n : frontier) {
			if (explorednet.contains(n)) {
				System.out.println("conjoint found at:" + n.getName());
				System.out.println("explorednet:" + explorednet);
				return true;
			}
		}
		return false;
	}

	// Loop through a list of nodes and return all mingenl parents of them
	private List<Node> exploreNextFrontier(List<Node> frontier) {
		List<Node> list = new ArrayList<Node>();
		for (Node n : frontier) {
			list.addAll(CommonQuery.MINGENLS.runQuery(dag_, n));
		}
		return list;
	}

}
