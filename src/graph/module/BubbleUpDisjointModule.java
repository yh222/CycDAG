package graph.module;

import graph.core.CommonConcepts;
import graph.core.DAGEdge;
import graph.core.DAGNode;
import graph.core.Edge;
import graph.core.Node;
import graph.core.OntologyFunction;
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
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

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

	private ConcurrentHashMap<Node, Node> exploredPairs_;

	private ConcurrentHashMap<Node, Float> recordedAbstractness_;

	// TODO: magic number here, need to be reasoned
	private static float THEP_ = 0.3f;

	private static float ABSTRACTNESSTHESHOLD_ = 0.7f;
	// The limitation for exploring children of each parent
	private static int MAXCHILDEXPLORATION_ = 80;

	private static int MINMATURITY_ = 10;

	// count of disjoint edges created
	private int disjointCreated_ = 0;

	DAGNode partiallyTangible;
	DAGNode genls;
	DAGNode isa;
	DAGNode and;

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

	Node creator_ = new StringNode("BubbleUpDisjoint Module");

	@Override
	public boolean initialisationComplete(Collection<DAGNode> nodes,
			Collection<DAGEdge> edges, boolean forceRebuild) {
		System.out.print("Starting to bubble up disjoints...");
		initializeModules();

		// Get all disjoint edges
		ArrayList<Edge> disjointEdges = new ArrayList<Edge>(
				relEdgeModule_.execute(
						CommonConcepts.DISJOINTWITH.getNode(dag_), 1));

		bubbleUpDisjoints(disjointEdges);

		System.out.print("Bubble up disjoints done..." + disjointCreated_
				+ " disjoint edges created.");
		return true;

	}

	private void initializeModules() {
		relEdgeModule_ = (RelatedEdgeModule) dag_
				.getModule(RelatedEdgeModule.class);
		transitiveModule_ = (TransitiveIntervalSchemaModule) dag_
				.getModule(TransitiveIntervalSchemaModule.class);
		queryModule_ = (QueryModule) dag_.getModule(QueryModule.class);
		semanticSimilarityModule_ = (SemanticSimilarityModule) dag_
				.getModule(SemanticSimilarityModule.class);

		exploredPairs_ = new ConcurrentHashMap<Node, Node>();
		recordedAbstractness_ = new ConcurrentHashMap<Node, Float>();
		// rejectedNodes_ = new ConcurrentHashMap<Node, Float>();

		partiallyTangible = (DAGNode) dag_.findOrCreateNode(
				"PartiallyTangible", null, true);
		genls = CommonConcepts.GENLS.getNode(dag_);
		isa = CommonConcepts.ISA.getNode(dag_);
		and = CommonConcepts.AND.getNode(dag_);
	}

	/**
	 * explorePairsAndBubbleUpDisjoints
	 */
	private void bubbleUpDisjoints(ArrayList<Edge> disjointEdges) {

		// Create out put .arff header
		try (PrintWriter out = new PrintWriter(new BufferedWriter(
				new FileWriter("bubblingUpOutStat.csv", true)))) {
			out.println("@relation Nodes");
			out.println("@attribute nodeA string");
			out.println("@attribute nodeB string");
			out.println("@attribute 'similarity' numeric");
			out.println("@attribute 'abstractnessA' numeric");
			out.println("@attribute 'abstractnessB' numeric");
			out.println("@attribute 'MaxChildA' numeric");
			out.println("@attribute 'MaxChildB' numeric");
			out.println("@attribute 'AllChildA' numeric");
			out.println("@attribute 'AllChildB' numeric");
			out.println("@attribute 'AllParentA' numeric");
			out.println("@attribute 'AllParentB' numeric");
			out.println("@attribute 'pAB' numeric");
			out.println("@attribute 'pBA' numeric");
			out.println("@attribute 'depthA' numeric");
			out.println("@attribute 'depthB' numeric");
			out.println("@attribute 'disjointCountA' numeric");
			out.println("@attribute 'disjointCountB' numeric");
			out.println("@attribute 'prediction' numeric");
			out.println("@attribute 'classification' numeric");
			out.println("@data");
		} catch (IOException e) {
			e.printStackTrace();
		}

		for (int k = 0; k < 500; k++) {
			Node a = getRandomCollectionHead();
			Node b = getRandomCollectionHead();
			if (hasConjoint(a, b) || isAlreadyDisjointed(a, b)) {
				k--;
				continue;
			}
			isTooAbstract(a);
			isTooAbstract(b);
			used.add(a.getIdentifier());
			used.add(b.getIdentifier());
			tryCreateDisjointEdge(a, b);
		}

		System.out.println("Bubble up disjoints done");
	}

	HashSet<String> used=new HashSet<String>();
	private Node getRandomCollectionHead() {
		Node n = null;
		do {
			n = dag_.getRandomNode();
		} while (!isWantedNode(n));
		return n;
	}

	private boolean isWantedNode(Node n) {
		if(used.contains(n.getIdentifier()))
			return false;
		
		
		if (!isTangible(n))
			return false;

		int maxchild = getMaxChildren(n).size();
		if (maxchild > 40 || maxchild < 10)
			return false;

		isTooAbstract(n);
		float abs = recordedAbstractness_.get(n);
		if (abs <= 5)
			return false;

		
		
		return true;
	}

	private boolean isTangible(Node node) {
		return queryModule_.prove(genls, node, partiallyTangible);
	}

	private void tryCreateDisjointEdge(Node right, Node left) {

		try (PrintWriter out = new PrintWriter(new BufferedWriter(
				new FileWriter("bubblingUpOutStat.csv", true)))) {
			assert (right != null);
			assert (left != null);

			System.out.println("processing pair:" + right.getName() + ", "
					+ left.getName());

			Pair<Float, Integer> pairA = calculateP(right,
					getAllChildren(right), left);
			Pair<Float, Integer> pairB = calculateP(left, getAllChildren(left),
					right);

			float pAB = pairA.objA_;
			int countAB = pairA.objB_;
			float pBA = pairB.objA_;
			int countBA = pairB.objB_;

			float sim = getSimilarity(right, left);
			float abstRight = recordedAbstractness_.get(right);
			float abstLeft = recordedAbstractness_.get(left);

			int MaxChildA = getMaxChildren(right).size();
			int MaxChildB = getMaxChildren(left).size();

			int allChildA = getAllChildren(right).size();
			int allChildB = getAllChildren(left).size();

			int allParentA = getAllGenlsParent(right).size();
			int allParentB = getAllGenlsParent(left).size();

			int depthA = Integer.parseInt(((DAGNode) right)
					.getProperty("depth"));
			int depthB = Integer
					.parseInt(((DAGNode) left).getProperty("depth"));

			out.print(right.getName() + ",");
			out.print(left.getName() + ",");
			out.print(sim + ",");
			out.print(abstRight + ",");
			out.print(abstLeft + ",");
			out.print(MaxChildA + ",");
			out.print(MaxChildB + ",");
			out.print(allChildA + ",");
			out.print(allChildB + ",");
			out.print(allParentA + ",");
			out.print(allParentB + ",");
			out.print(pAB + ",");
			out.print(pBA + ",");
			out.print(depthA + ",");
			out.print(depthB + ",");
			out.print(countAB + ",");
			out.print(countBA + ",");

			if (pAB > THEP_ || pBA > THEP_) {
				disjointCreated_++;
				out.print(1 + ",");
			} else {
				out.print(0 + ",");
			}

			out.print("\n");

		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	private class CreateDisjointThread implements Runnable {
		Node mRight;
		Node mLeft;

		public CreateDisjointThread(Node right, Node left) {
			mRight = right;
			mLeft = left;
		}

		@Override
		public void run() {

			Pair<Float, Integer> pairA = calculateP(mRight,
					getAllChildren(mRight), mLeft);
			Pair<Float, Integer> pairB = calculateP(mLeft,
					getAllChildren(mLeft), mRight);

			float pAB = pairA.objA_;
			int countAB = pairA.objB_;
			float pBA = pairB.objA_;
			int countBA = pairB.objB_;

			float sim = getSimilarity(mRight, mLeft);
			float abstRight = recordedAbstractness_.get(mRight);
			float abstLeft = recordedAbstractness_.get(mLeft);

			int MaxChildA = getMaxChildren(mRight).size();
			int MaxChildB = getMaxChildren(mLeft).size();

			int allChildA = getAllChildren(mRight).size();
			int allChildB = getAllChildren(mLeft).size();

			int allParentA = getAllGenlsParent(mRight).size();
			int allParentB = getAllGenlsParent(mLeft).size();

			int depthA = Integer.parseInt(((DAGNode) mRight)
					.getProperty("depth"));
			int depthB = Integer.parseInt(((DAGNode) mLeft)
					.getProperty("depth"));

			printToFile(pAB, countAB, pBA, countBA, sim, abstRight, abstLeft,
					MaxChildA, MaxChildB, allChildA, allChildB, allParentA,
					allParentB, depthA, depthB);
		}

		/*
		 * out.println("@relation Nodes");
		 * out.println("@attribute nodeA string");
		 * out.println("@attribute nodeB string");
		 * out.println("@attribute 'similarity' numeric");
		 * out.println("@attribute 'abstractnessA' numeric");
		 * out.println("@attribute 'abstractnessB' numeric");
		 * out.println("@attribute 'MaxChildA' numeric");
		 * out.println("@attribute 'MaxChildB' numeric");
		 * out.println("@attribute 'AllChildA' numeric");
		 * out.println("@attribute 'AllChildB' numeric");
		 * out.println("@attribute 'AllParentA' numeric");
		 * out.println("@attribute 'AllParentB' numeric");
		 * out.println("@attribute 'pAB' numeric");
		 * out.println("@attribute 'pBA' numeric");
		 * out.println("@attribute 'depthA' numeric");
		 * out.println("@attribute 'depthB' numeric");
		 * out.println("@attribute 'disjointCountA' numeric");
		 * out.println("@attribute 'disjointCountB' numeric");
		 * out.println("@attribute 'prediction' numeric");
		 * out.println("@attribute 'classification' numeric");
		 */

		private synchronized void printToFile(float pAB, int countAB,
				float pBA, int countBA, float sim, float abstRight,
				float abstLeft, int maturityA, int maturityB, int allChildA,
				int allChildB, int allParentA, int allParentB, int depthA,
				int depthB) {
			try (PrintWriter out = new PrintWriter(new BufferedWriter(
					new FileWriter("bubblingUpOutStat.csv", true)))) {

				out.print(mRight.getName() + ",");
				out.print(mLeft.getName() + ",");
				out.print(sim + ",");
				out.print(abstRight + ",");
				out.print(abstLeft + ",");
				out.print(maturityA + ",");
				out.print(maturityB + ",");
				out.print(allChildA + ",");
				out.print(allChildB + ",");
				out.print(allParentA + ",");
				out.print(allParentB + ",");
				out.print(pAB + ",");
				out.print(pBA + ",");
				out.print(depthA + ",");
				out.print(depthB + ",");
				out.print(countAB + ",");
				out.print(countBA + ",");

				if (pAB > THEP_ || pBA > THEP_) {
					disjointCreated_++;
					out.print(1 + ",");
				} else {
					out.print(0 + ",");
				}

				out.print("\n");

			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}

	/*
	 * Return count of disjointed child. Return -3 if conjoint found. Return -2
	 * if the collection has high discretion. Return -1 if p's too low
	 */

	private Pair<Float, Integer> calculateP(Node collectionParent,
			List<Node> children, Node targetNode) {
		int disjointcount = 0;

		boolean isLargeCollection = children.size() > MAXCHILDEXPLORATION_;
		int roundedchildrensize = isLargeCollection ? MAXCHILDEXPLORATION_
				: children.size();
		Random random = new Random();
		// random sampling for MAXCHILDEXPLORATION_ times when children size is
		// very large
		for (int i = roundedchildrensize - 1; i > 0; i--) {
			Node child;
			// Random sampling or iterate through the whole
			if (isLargeCollection) {
				child = children.get(random.nextInt(children.size()));
			} else {
				child = children.get(i);
			}

			// if child disjoint with targetNode, count++
			if (isAlreadyDisjointed(targetNode, child)) {
				disjointcount++;
			}
		}
		Pair<Float, Integer> pair = new Pair<Float, Integer>(
				(float) disjointcount / roundedchildrensize, disjointcount);
		return pair;
	}

	private boolean isAlreadyDisjointed(Node targetNode, Node child) {
		return queryModule_.prove(CommonConcepts.DISJOINTWITH.getNode(dag_),
				targetNode, child);
	}

	private boolean hasConjoint(Node nodeA, Node nodeB) {
		// Check they are not Genls to each other
		if (transitiveModule_.execute(true, nodeA, nodeB) != null
				|| transitiveModule_.execute(false, nodeA, nodeB) != null)
			return true;

		// Check they do not have conjoint point
		// Node[] args = dag_.parseNodes(
		// "(and (genls ?X " + nodeA.getIdentifier() + ") (genls ?X "
		// + nodeB.getIdentifier() + "))", null, false, false);
		// // query: and (genls ?X n1) (genls ?X n2)
		// DAGNode node = new DAGNode();
		// Substitution substitution = new Substitution("?X", node);
		// boolean satisfies = queryModule_.prove(substitution
		// .applySubstitution(args));

		// Check they do not have genls conjoint point
		VariableNode x = VariableNode.DEFAULT;
		QueryObject qo = new QueryObject(and, new OntologyFunction(genls, x,
				nodeA), new OntologyFunction(genls, x, nodeB));
		Collection<Substitution> results = queryModule_.execute(qo);
		if (results.size() != 0) {
			return true;
		}
		// Check they do not have isa conjoint point
		x = VariableNode.DEFAULT;
		qo = new QueryObject(and, new OntologyFunction(isa, x, nodeA),
				new OntologyFunction(isa, x, nodeB));
		results = queryModule_.execute(qo);
		if (results.size() != 0) {
			return true;
		}

		return false;
	}

	private ArrayList<Node> getAllChildren(Node inputNode) {
		ArrayList<Node> children = new ArrayList<Node>(
				CommonQuery.SPECS.runQuery(dag_, inputNode));
		return children;
	}

	private ArrayList<Node> getMaxChildren(Node inputNode) {
		ArrayList<Node> children = new ArrayList<Node>(
				CommonQuery.MAXSPECS.runQuery(dag_, inputNode));
		return children;
	}

	private ArrayList<Node> getAllGenlsParent(Node inputNode) {
		ArrayList<Node> children = new ArrayList<Node>(
				CommonQuery.ALLGENLS.runQuery(dag_, inputNode));
		return children;
	}

	private ArrayList<Node> getMinGenlsParent(Node inputNode) {
		ArrayList<Node> children = new ArrayList<Node>(
				CommonQuery.MINGENLS.runQuery(dag_, inputNode));
		return children;
	}

	private boolean isTooAbstract(Node inputNode) {
		/*
		 * if (rejectedNodes_.containsKey(inputNode)) { return true; } else
		 */
		if (recordedAbstractness_.containsKey(inputNode)) {
			float abst = recordedAbstractness_.get(inputNode);
			if (abst >= 0 && abst <= ABSTRACTNESSTHESHOLD_) {
				return true;
			} else {
				return false;
			}
		}

		try (PrintWriter out = new PrintWriter(new BufferedWriter(
				new FileWriter("abslog.txt", true)))) {

			List<Node> children = new ArrayList<Node>(getAllChildren(inputNode));
			List<Float> similarities = new ArrayList<Float>();

			if (children.size() <= 5) {
				recordedAbstractness_.put(inputNode, 0.9f);
				return false;
			}

			boolean isLargeCollection = children.size() > MAXCHILDEXPLORATION_;
			Random random = new Random();
			float meanSim = 0;

			for (int i = isLargeCollection ? MAXCHILDEXPLORATION_ - 1
					: children.size() - 1; i > 0; i--) {
				Node child;
				if (isLargeCollection) {
					child = children.get(random.nextInt(children.size()));
				} else {
					child = children.get(i);
				}
				for (int j = i - 1; j > 0; j--) {
					Node anotherchild;
					if (isLargeCollection) {
						anotherchild = children.get(random.nextInt(children
								.size()));
					} else {
						anotherchild = children.get(j);
					}
					if (child != anotherchild) {
						float sim = getSimilarity(child, anotherchild);
						meanSim += sim;
						similarities.add(sim);
					}
				}
			}
			// Change: only average the lower 20% entries
			meanSim = 0;
			Collections.sort(similarities);
			for (int i = 0; i < similarities.size() / 5; i++) {
				meanSim += similarities.get(i);
			}
			meanSim /= (similarities.size() / 5);
			recordedAbstractness_.put(inputNode, meanSim);

			// if (meanSim >= 0)
			out.println("abstractness of " + inputNode.getName() + " is "
					+ meanSim);

			if (meanSim >= 0 && meanSim < ABSTRACTNESSTHESHOLD_) {
				return true;
			} else {
				return false;
			}

		} catch (IOException e) {
			e.printStackTrace();
			return true;
		}
	}

	private Float getSimilarity(Node nodeA, Node nodeB) {
		return semanticSimilarityModule_.taxonomicSimilarity(nodeA, nodeB);
	}

}
