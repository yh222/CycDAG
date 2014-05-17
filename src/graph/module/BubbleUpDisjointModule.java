package graph.module;

import graph.core.CommonConcepts;
import graph.core.DAGEdge;
import graph.core.DAGNode;
import graph.core.Edge;
import graph.core.Node;
import graph.core.StringNode;
import graph.inference.CommonQuery;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import org.apache.commons.collections4.CollectionUtils;

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

	private HashSet<Pair<Node, Node>> exploredPairs_ = new HashSet<Pair<Node, Node>>();
	private HashSet<Node> rejectedEvidences_ = new HashSet<Node>();
	private HashSet<Node> acceptedEvidences_ = new HashSet<Node>();

	// TODO: magic number here, need to be reasoned
	private static double THEP_ = 0.4;
	// The limitation for exploring children of each parent
	private static int MAXCHILDEXPLORATION_ = 200;
	private static int MINCHILDEXPLORATION_ = 5;

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
		initializeModules();

		Node creator = new StringNode("BubbleUpDisjoint Module");
		Map<Integer, List<Pair<Node, Node>>> pairsToExplore = new HashMap<Integer, List<Pair<Node, Node>>>();

//		// Get all disjoint edges
//		Collection<Edge> disjointEdges = getAllDisjointEdges();
//
//		// Sort edges according to the maximum distance to THING node
//		// Result of sorting will stored at pairsToExplore
//		sortPairsAndFilterEdges(disjointEdges, pairsToExplore);
//		explorePairsAndBubbleUpDisjoints(creator, pairsToExplore);
		try {
			readfileAndModify();
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		System.out.print("Bubble up disjoints done...");

		return true;

	}

	private void initializeModules() {
		relEdgeModule_ = (RelatedEdgeModule) dag_
				.getModule(RelatedEdgeModule.class);
		transitiveModule_ = (TransitiveIntervalSchemaModule) dag_
				.getModule(TransitiveIntervalSchemaModule.class);
		queryModule_ = (QueryModule) dag_.getModule(QueryModule.class);

		// TODO: Check depth module and TransitiveIntervalSchema module have
		// done the work
	}

	private void readfileAndModify() throws FileNotFoundException, IOException {

		try (BufferedReader reader = new BufferedReader(new FileReader(
				"onlyTangible200.arff"))) {
			PrintWriter out = new PrintWriter(new BufferedWriter(
					new FileWriter("new.txt", true)));

			String line = "";
			String cvsSplitBy = ",";

			while ((line = reader.readLine()) != null) {

				// use comma as separator
				String[] data = line.split(cvsSplitBy);
				if (dag_.findDAGNode(data[0]) != null) {
					Node nodeA = dag_.findDAGNode(data[0]);
					Node nodeB = dag_.findDAGNode(data[1]);

					// Random rn = new Random();
					// if (Math.random() <= 0.2) {
					// out.println(line);
					// }

					double p1=calculateP(nodeA, (List<Node>) getChildren(nodeA), nodeB);
					int count1 = _disjointcount;
					double p2=calculateP(nodeB, (List<Node>) getChildren(nodeB), nodeA);
					int count2 = _disjointcount;
					out.println(p1+","+p2+","  + count1 + "," + count2);

				}

			}

			out.close();
			System.out.println("read/write done");
		}

	}

	private Collection<Edge> getAllDisjointEdges() {
		return relEdgeModule_.execute(
				CommonConcepts.DISJOINTWITH.getNode(dag_), 1);
	}

	/**
	 * Sort the pairs from disjoint edges according to the distance from source
	 * side
	 * 
	 * For each pair added, the first node will be source and second node will
	 * be target. (For source node, parent nodes will be explored in attempt to
	 * establish disjoint with target node)
	 */
	private void sortPairsAndFilterEdges(Collection<Edge> disjointEdges,
			Map<Integer, List<Pair<Node, Node>>> pairsToExplore) {
		int temp;

		DAGNode partiallyTangible = (DAGNode) dag_.findOrCreateNode(
				"PartiallyTangible", null, true);
		DAGNode genls = CommonConcepts.GENLS.getNode(dag_);

		for (Edge e : disjointEdges) {

			if (!queryModule_.prove(genls, e.getNodes()[1], partiallyTangible)
					|| !queryModule_.prove(genls, e.getNodes()[2],
							partiallyTangible))
				continue;

			// In the case of function, the depth of node become null
			if (((DAGNode) e.getNodes()[1]).getProperty("depth") != null) {
				temp = Integer.parseInt(((DAGNode) e.getNodes()[1])
						.getProperty("depth"));
				if (pairsToExplore.get(temp) == null) {
					pairsToExplore.put(temp, new ArrayList<Pair<Node, Node>>());
				} else {
					pairsToExplore.get(temp).add(
							new Pair<Node, Node>(e.getNodes()[1],
									e.getNodes()[2]));
				}
			}

			// Second node, the pair is (Node2->Node1)
			if (((DAGNode) e.getNodes()[2]).getProperty("depth") != null) {
				temp = Integer.parseInt(((DAGNode) e.getNodes()[2])
						.getProperty("depth"));
				if (pairsToExplore.get(temp) == null) {
					pairsToExplore.put(temp, new ArrayList<Pair<Node, Node>>());
				} else {
					pairsToExplore.get(temp).add(
							new Pair<Node, Node>(e.getNodes()[2],
									e.getNodes()[1]));
				}
			}
		}
		System.out.println("Pairs sorted");
	}

	/**
	 * explorePairsAndBubbleUpDisjoints
	 */
	private void explorePairsAndBubbleUpDisjoints(Node creator,
			Map<Integer, List<Pair<Node, Node>>> pairsToExplore) {
		// Retrieve and sort indexes of lists organized by depth
		List<Integer> keyset = new ArrayList<Integer>(pairsToExplore.keySet());
		Collections.sort(keyset);

		// Loop backwards, from the greatest index
		// int count = 0;
		// int tenPercent = (pairsToExplore.size()) / 10;
		for (int i = keyset.size() - 1; i > 0; i--) {
			// null proof
			if (pairsToExplore.get(keyset.get(i)) == null) {
				continue;
			}
			for (int j = 0; j < pairsToExplore.get(keyset.get(i)).size(); j++) {
				Pair<Node, Node> pair = pairsToExplore.get(keyset.get(i))
						.get(j);
				// Find all Min parent nodes for source node
				Collection<Node> minGenls = CommonQuery.MINGENLS.runQuery(dag_,
						pair.objA_);
				// Try to establish disjoint edge from (each parent of A) to (B)
				for (Node n : minGenls) {
					List<Node> children = checkConstraintAndGetChildren(n,
							pair.objB_);
					if (children != null) {
						double p = calculateP(n, children, pair.objB_);
						saveAndPrintOutput(creator, n, pair.objB_, children, p);
					}
				}
				// count++;
				// if (count % tenPercent == 0) {
				// //Print progress info
				// System.out.println((count / tenPercent * 10) + "% done");
				// System.out.println(pairsToExplore.get(i).size() - j
				// + " pairs left, index= " + keyset.get(i));
				// }
			}
		}
		System.out.println("Bubble up disjoints done");
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
		// if (rejectedEvidences_.contains(collectionParent))
		// return null;
		// If the collectionParent is already disjoint with targetNode, skip it.
		if (isAlreadyDisjointed(collectionParent, targetNode))
			return null;
		// Get all highest child nodes of collectionParent
		List<Node> children = new ArrayList<Node>(getChildren(collectionParent));
		// Set upper bound of children size that to be explored

		if (children.size() <= MINCHILDEXPLORATION_) {
			// Don't decide if children size is too small
			return null;
		}
		return children;
	}

	// Save the disjoint(if found one) and print other stats
	private void saveAndPrintOutput(Node creator, Node collectionParent,
			Node targetNode, List<Node> children, double p) {

		try (PrintWriter out = new PrintWriter(new BufferedWriter(
				new FileWriter("out.txt", true)))) {
			if (p == -3) {
				// out.println("conjoint found bewteen " + targetNode.getName()
				// + " and " + collectionParent.getName());
			} else if (p > THEP_ && _disjointcount > 4) {
				double reverseP = calculateP(collectionParent, children,
						targetNode);
				if (reverseP > THEP_ && _disjointcount > 4) {

					boolean tempdisjointed;

					// out.println(collectionParent.getName() + " "
					// + targetNode.getName() + ", p=" + p + ", Sample size="
					// + children.size());
					// out.println("---Content of collection:");
					// for (Node c : children) {
					// tempdisjointed = (queryModule_.prove(
					// CommonConcepts.DISJOINTWITH.getNode(dag_),
					// targetNode, c)) ? true : false;
					// out.println("--" + c.getName() + " is disjointed to: "
					// + targetNode.getName() + ": " + tempdisjointed);
					// }

					// If they are likely to be disjointed, create a new
					// disjoint
					// edge
					// Write record to output file as well
					dag_.findOrCreateEdge(new Node[] {
							CommonConcepts.DISJOINTWITH.getNode(dag_),
							collectionParent, targetNode }, creator, false);
					disjointCreated_++;
					out.println(collectionParent.getName() + ","
							+ targetNode.getName());
				}
			} else if (p <= THEP_) {
				// out.println("p is too low: " + p);
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	/*
	 * Return count of disjointed child. Return -3 if conjoint found. Return -2
	 * if the collection has high discretion. Return -1 if p's too low
	 */
	private int _disjointcount;

	private double calculateP(Node collectionParent, List<Node> children,
			Node targetNode) {
		_disjointcount = 0;

		boolean isLargeCollection = children.size() > MAXCHILDEXPLORATION_;
		int roundedchildrensize = isLargeCollection ? MAXCHILDEXPLORATION_
				: children.size();
		Random random = new Random();
		// random sampling for LIMITCHILDEXPLORATION times when children size is
		// very large
		for (int i = isLargeCollection ? MAXCHILDEXPLORATION_ - 1 : children
				.size() - 1; i > 0; i--) {
			Node child;
			// Random sampling or iterate through the whole
			if (isLargeCollection) {
				child = children.get(random.nextInt(roundedchildrensize));
			} else {
				child = children.get(i);
			}

			// if child disjoint with targetNode, count++
			if (isAlreadyDisjointed(targetNode, child)) {
				_disjointcount++;
			} else if (hasConjoint(targetNode, child)) {
				// else if any conjoint found between the child and
				// targetNode,skip
				return -3;
			}
		}

		return (double) _disjointcount / roundedchildrensize;
	}

	private boolean isAlreadyDisjointed(Node targetNode, Node child) {
		return queryModule_.prove(CommonConcepts.DISJOINTWITH.getNode(dag_),
				targetNode, child);
	}

	private boolean hasConjoint(Node targetNode, Node child) {
		return transitiveModule_.execute(true, targetNode, child) != null
				|| transitiveModule_.execute(false, targetNode, child) != null;
	}

	private Collection<Node> getChildren(Node inputNode) {
		Collection<Node> children = new ArrayList<Node>(
				CommonQuery.MAXSPECS.runQuery(dag_, inputNode));
		return children;
	}

}
