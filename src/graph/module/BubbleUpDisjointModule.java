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
import java.util.HashMap;
import java.util.HashSet;
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
	private transient SemanticSimilarityModule semanticSimilarityModule_;

	private Map<Integer, List<Pair<Node, Node>>> toExplore_ = new HashMap<Integer, List<Pair<Node, Node>>>();
	private HashSet<Pair<Node, Node>> exploredPairs_ = new HashSet<Pair<Node, Node>>();
	private HashSet<Node> rejectedEvidences_ = new HashSet<Node>();
	private HashSet<Node> acceptedEvidences_ = new HashSet<Node>();

	// TODO: magic number here, need to be reasoned
	private static double THEP_ = 0.1;
	// The limitation for exploring children of each parent
	private static int MAXCHILDEXPLORATION_ = 500;
	private static int MINCHILDEXPLORATION_ = 10;
	// Threshold for Standard Deviation
	// private static int STDDEVTHRESHOLD_ = 10;
	private static double SIMILARITYTHRESHOLD = 0.6;
	private static double MEANSIMILARITYTHRESHOLD = 0.7;

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
		semanticSimilarityModule_ = (SemanticSimilarityModule) dag_
				.getModule(SemanticSimilarityModule.class);

		// TODO: Check depth module and TransitiveIntervalSchema module have
		// done the work

		// Get all disjoint edges
		Collection<Edge> disjointEdges = relEdgeModule_.execute(
				CommonConcepts.DISJOINTWITH.getNode(dag_), 1);
		// Sort edges according to the maximum distance to THING node
		// Result of sorting will stored at toExplore_
		sortAndFilterToExplore(disjointEdges);
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
	private void sortAndFilterToExplore(Collection<Edge> disjointEdges) {
		int temp;

		for (Edge e : disjointEdges) {
			// Get depth of first node and add the pair (Node1->Node2) to
			// appropriate location in the array

			// Check similarity between node A and node B
			if (hasHighSimilarityBetween((DAGNode) e.getNodes()[1],
					(DAGNode) e.getNodes()[2])) {
				continue;
			}

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

		// Use the count of disjoint found between collectionParent's
		// children and targetNode, and the amount of child to decide if
		// collectionParent disjoint with targetNode
		saveAndPrintOutput(creator, collectionParent, targetNode, children,
				calculateP(collectionParent, children, targetNode));
	}

	// Save the disjoint(if found one) and print other stats
	private void saveAndPrintOutput(Node creator, Node collectionParent,
			Node targetNode, List<Node> children, double p) {

		try (PrintWriter out = new PrintWriter(new BufferedWriter(
				new FileWriter("out.txt", true)))) {
			if (p == -2) {
				out.println("Evidence collection parent rejected due to lack of similarity:"
						+ collectionParent.getName());
			} else if (p == -3) {
				out.println("conjoint found bewteen " + targetNode.getName()
						+ " and " + collectionParent.getName());
			} else if (p == -4) {
				out.println("Evidence target rejected due to lack of similarity:"
						+ targetNode.getName());
			} else if (p == -1) {
				out.println("rejected due to high similarity between:"
						+ targetNode.getName() + " "
						+ collectionParent.getName());
			} else if (p > THEP_) {
				System.out.println("Disjoint added btween:"
						+ collectionParent.getName() + " "
						+ targetNode.getName() + ", with p=" + p
						+ ", Sample size=" + children.size());

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

				// If they are likely to be disjointed, create a new disjoint
				// edge
				// Write record to output file as well
				// dag_.findOrCreateEdge(creator, new Node[] {
				// CommonConcepts.DISJOINTWITH.getNode(dag_),
				// collectionParent, targetNode }, false);
				disjointCreated_++;
				out.println(disjointCreated_ + " disjoint edges created");
			} else if (p <= THEP_) {
				out.println("p is too low: " + p);
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	/*
	 * Return count of disjointed child. Return -3 if conjoint found. Return -2
	 * if the collection has high discretion. Return -1 if p's too low
	 */
	private double calculateP(Node collectionParent, List<Node> children,
			Node targetNode) {
		int disjointcount = 0;
		int undefinedcount = 0;

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
			if (queryModule_.prove(CommonConcepts.DISJOINTWITH.getNode(dag_),
					targetNode, child)) {
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
		if (hasHighDiscretion(collectionParent)) {
			return -2;
		}

		if (hasHighDiscretion(targetNode)) {
			return -4;
		}

		if (hasHighSimilarityBetween(collectionParent, targetNode)) {
			return -1;
		}

		return (double) disjointcount / roundedchildrensize;
	}

	// private boolean isNotDirectlyDisjointed(Node targetNode, Node child) {
	// QueryObject qo = new QueryObject(
	// CommonConcepts.DISJOINTWITH.getNode(dag_), targetNode, child);
	// queryModule_.applyModule(
	// CommonConcepts.ASSERTED_SENTENCE.getNodeName(), qo);
	// if (qo.getJustification().isEmpty()) {
	// return true;
	// } else {
	// return false;
	// }
	// }

	// // Sort and return a list of parents by their frequency
	// private List<Map.Entry<Node, Integer>> sortParentsByFrequency(
	// Map<Node, Integer> similarity) {
	// List<Map.Entry<Node, Integer>> list = new ArrayList<Map.Entry<Node,
	// Integer>>(
	// similarity.entrySet());
	// mapEntryComparator comaprator = new mapEntryComparator();
	// Collections.sort(list, comaprator);
	// return list;
	// }
	//
	// // An utility Comparator used to sort hashMap entries
	// private class mapEntryComparator implements
	// Comparator<Map.Entry<Node, Integer>> {
	// @Override
	// public int compare(final Map.Entry<Node, Integer> object1,
	// final Map.Entry<Node, Integer> object2) {
	// return object2.getValue().compareTo(object1.getValue());
	// }
	// }

	// Test the discretion of the parents of the collection,return true if
	// discretion is high
	// private boolean hasHighDiscretion(Node inputNode) {
	// Random random = new Random();
	// String depthstring = ((DAGNode) inputNode).getProperty("depth");
	// // Return true to pass this node, if the depth is not available
	// if (depthstring == null)
	// return true;
	// int inputnodedepth = (int) (Integer.parseInt(depthstring));
	//
	// Map<Node, Integer> discretiondata = new HashMap<Node, Integer>();
	// Map<Node, Integer> depthdata = new HashMap<Node, Integer>();
	//
	// List<Node> children = new ArrayList<Node>(
	// CommonQuery.MAXSPECS.runQuery(dag_, inputNode));
	// children.addAll(CommonQuery.MAXINSTANCES.runQuery(dag_, inputNode));
	// boolean isLargeCollection = children.size() > MAXCHILDEXPLORATION_;
	//
	// try (PrintWriter out = new PrintWriter(new BufferedWriter(
	// new FileWriter("out.txt", true)))) {
	// if (children.size() <= 1) {// for debug
	// out.println(inputNode.getName()
	// + " SPECS"
	// + (List<Node>) CommonQuery.DIRECTSPECS.runQuery(dag_,
	// inputNode));
	// }
	// int i = isLargeCollection ? MAXCHILDEXPLORATION_ : children.size();
	// out.println("children.size():" + children.size());
	//
	// String tempdepthstring;
	// for (i = i - 1; i > 0; i--) {
	// Node child;
	// // Random sampling or iterate through the whole
	// if (isLargeCollection) {
	// child = children.get(random.nextInt(MAXCHILDEXPLORATION_));
	// } else {
	// child = children.get(i);
	// }
	// updateDiscretionData(discretiondata, child);
	// }
	//
	// // Calculate mean
	// double mean = 0;
	// int colsize = discretiondata.size() - 1;
	// for (Map.Entry<Node, Integer> e : discretiondata.entrySet()) {
	//
	// tempdepthstring = ((DAGNode) e.getKey()).getProperty("depth");
	// // record the depth of each parent
	// if (tempdepthstring == null) {
	// continue;
	// } else {
	// depthdata.put(e.getKey(),
	// (Integer.parseInt(tempdepthstring)));
	// }
	//
	// mean += e.getValue();
	// }
	// mean /= colsize;
	// // Calculate variance
	// double variance = 0;
	// for (Map.Entry<Node, Integer> e : discretiondata.entrySet()) {
	//
	// variance += Math.pow(e.getValue() - mean, 2);
	//
	// }
	// out.println("stdDev:" + Math.sqrt(variance / colsize));
	// if (Math.sqrt(variance / colsize) > STDDEVTHRESHOLD_) {
	// return true;
	// }
	// return false;
	// } catch (IOException e) {
	// e.printStackTrace();
	// return true;
	// }
	// }

	private boolean hasHighDiscretion(Node inputNode) {
		try (PrintWriter out = new PrintWriter(new BufferedWriter(
				new FileWriter("out.txt", true)))) {
			if (rejectedEvidences_.contains(inputNode)) {
				return true;
			} else if (acceptedEvidences_.contains(inputNode)) {
				return false;
			}

			List<Node> children = new ArrayList<Node>(
					CommonQuery.MAXSPECS.runQuery(dag_, inputNode));
			if (children.isEmpty()) {
				return false;
			}

			boolean isLargeCollection = children.size() > MAXCHILDEXPLORATION_;
			Random random = new Random();
			int roundedchildrensize = isLargeCollection ? MAXCHILDEXPLORATION_
					: children.size();

			float meanSim = 0;
			for (int i = isLargeCollection ? MAXCHILDEXPLORATION_ - 1
					: children.size() - 1; i > 0; i--) {
				Node child;
				if (isLargeCollection) {
					child = children.get(random.nextInt(children.size()));
				} else {
					child = children.get(i);
				}
				for (int j = isLargeCollection ? MAXCHILDEXPLORATION_ - 1
						: children.size() - 1; j > 0; j--) {
					Node anotherchild;
					if (isLargeCollection) {
						anotherchild = children.get(random.nextInt(children.size()));
					} else {
						anotherchild = children.get(j);
					}
					if (child != anotherchild) {
						meanSim += semanticSimilarityModule_.execute(child, anotherchild);
					}
				}
			}
			meanSim /= Math.pow(roundedchildrensize - 1, 2);
			out.println(inputNode.getName() + " meanSim:" + meanSim);
			if (meanSim > MEANSIMILARITYTHRESHOLD) {
				acceptedEvidences_.add(inputNode);
				return false;
			} else {
				rejectedEvidences_.add(inputNode);
				return true;
			}
		} catch (IOException e) {
			e.printStackTrace();
			return true;
		}
	}

	// private void updateDiscretionData(Map<Node, Integer> discretiondata,
	// Node node) {
	// // get all parents(genls/isa) for this child
	// Collection<Node> allparents = CommonQuery.MINGENLS.runQuery(dag_, node);
	// allparents.addAll(CommonQuery.MINISA.runQuery(dag_, node));
	//
	// // Count number of appearance of each parent
	// int t = 0;
	// for (Node parent : allparents) {
	// if (discretiondata.containsKey(parent)) {
	// t = discretiondata.get(parent) + 1;
	// discretiondata.put(parent, t);
	// } else {
	// discretiondata.put(parent, 1);
	// }
	// }
	// }

	/*
	 * Check if the collection head has some degree of similarity with the
	 * target node
	 */
	private boolean hasHighSimilarityBetween(Node nodeA, Node nodeB) {

		// String targetdepthstring = ((DAGNode) nodeA).getProperty("depth");
		// String headdepthstring = ((DAGNode) nodeB).getProperty("depth");
		// if (targetdepthstring == null || headdepthstring == null)
		// return true;
		//
		// int targetdepth = (int) (Integer.parseInt(targetdepthstring));
		// int headdepth = (int) (Integer.parseInt(headdepthstring));
		//
		// Set<Node> explorednet = new HashSet<Node>();
		// explorednet.add(nodeA);
		// explorednet.add(nodeB);
		// List<Node> frontiertargetnode = new ArrayList<Node>(
		// CommonQuery.MINGENLS.runQuery(dag_, nodeA));
		// frontiertargetnode.addAll(CommonQuery.MINISA.runQuery(dag_, nodeA));
		// List<Node> frontiercollectionhead = new ArrayList<Node>(
		// CommonQuery.MINGENLS.runQuery(dag_, nodeB));
		// frontiercollectionhead.addAll(CommonQuery.MINISA.runQuery(dag_,
		// nodeA));
		//
		// System.out.println("targetdepth:" + targetdepth);
		// System.out.println("headdepth:" + headdepth);
		//
		// while (targetdepth >= 0 || headdepth >= 0) {
		// if (targetdepth-- >= 0) {
		// if (!hasConjoint(explorednet, frontiertargetnode)) {
		// explorednet.addAll(frontiertargetnode);
		// frontiertargetnode = exploreNextFrontier(frontiertargetnode);
		// } else {
		// return true;
		// }
		// }
		//
		// if (headdepth-- >= 0) {
		// if (!hasConjoint(explorednet, frontiercollectionhead)) {
		// explorednet.addAll(frontiercollectionhead);
		// frontiercollectionhead = exploreNextFrontier(frontiercollectionhead);
		// } else {
		// return true;
		// }
		// }
		// }

		float s = semanticSimilarityModule_.execute(nodeA, nodeB);
		try (PrintWriter out = new PrintWriter(new BufferedWriter(
				new FileWriter("out.txt", true)))) {
			if (s < SIMILARITYTHRESHOLD) {

				out.println("low similarity between:" + nodeA.getName()
						+ " and " + nodeB.getName() + " is " + s);
				System.out.println("similarity between:" + nodeA.getName()
						+ " and " + nodeB.getName() + " is " + s);
				return false;
			} else {
				out.println("too high similarity between:" + nodeA.getName()
						+ " and " + nodeB.getName() + " is " + s);
				System.out.println("similarity between:" + nodeA.getName()
						+ " and " + nodeB.getName() + " is " + s);
				return true;
			}
		} catch (IOException e) {
			return true;
		}
	}

	// // Check if any element of the list exist in the set
	// private boolean hasConjoint(Set<Node> explorednet, List<Node> frontier) {
	// for (Node n : frontier) {
	// if (explorednet.contains(n)) {
	// System.out.println("conjoint found at:" + n.getName());
	// System.out.println("explorednet:" + explorednet);
	// return true;
	// }
	// }
	// return false;
	// }
	//
	// // Loop through a list of nodes and return all mingenl parents of them
	// private List<Node> exploreNextFrontier(List<Node> frontier) {
	// List<Node> list = new ArrayList<Node>();
	// for (Node n : frontier) {
	// list.addAll(CommonQuery.MINGENLS.runQuery(dag_, n));
	// }
	// return list;
	// }

}
