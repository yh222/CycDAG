package graph.module;

import graph.core.CommonConcepts;
import graph.core.DAGEdge;
import graph.core.DAGNode;
import graph.core.DAGObject;
import graph.core.Node;
import graph.core.OntologyFunction;
import graph.core.StringNode;
import graph.inference.CommonQuery;
import graph.inference.QueryObject;
import graph.inference.Substitution;
import graph.inference.VariableNode;
import io.resources.WMIAccess;
import io.resources.WMISocket;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.net.URISyntaxException;
import java.net.UnknownHostException;
import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Map.Entry;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.commons.collections4.CollectionUtils;

import util.AliasedObject;
import util.Pair;
import util.collection.WeightedSet;

public class ConceptNetAnalyzerImporter extends DAGModule<Collection<DAGEdge>> {

	private static final long serialVersionUID = -2241818554908651866L;
	private transient TransitiveIntervalSchemaModule transitiveModule_;
	private transient QueryModule queryModule_;
	private transient NodeAliasModule aliasModule_;
	private transient SemanticSimilarityModule semanticSimilarityModule_;

	// private transient WMISocket wmiSocket_;
	private transient ConcurrentHashMap<String, int[]> relationReliabilityCount_;
	private transient ConcurrentHashMap<Pair<String, String>, Boolean> dummyDisjoints_;
	private transient ConcurrentHashMap<Pair<String, String>, Boolean> explored_;

	private ConcurrentHashMap<String, ArrayList<DAGNode>> resolvedNames_;

	private transient ConcurrentHashMap<String, ConcurrentHashMap<Node, int[]>> interRelastionReliabilityCount_;
	private transient ConcurrentHashMap<String, ConcurrentHashMap<Pair<Node, Node>, ConcurrentLinkedQueue<Node>>> unknownBackups_;

	private transient ConcurrentHashMap<String, ArrayList<DAGNode>> IsAEdges_;

	// private transient ConcurrentHashMap<String, ConcurrentHashMap<String,
	// String>> explored_;

	private DAGNode secondordercyc;
	private DAGNode partiallyTangible;
	private DAGNode genls;
	private DAGNode isa;
	private DAGNode and;

	private transient int _notFoundCount = 0;
	private transient int _transtivelyResolvedCount = 0;
	private transient int _resolvedCount = 0;

	private final double _RELIABILITYTHRESHOLD = 0.95;
	private final int _STATMIN = 100;

	private ConcurrentHashMap<Node, Float> recordedAbstractness_;

	private static float ABSTRACTNESSTHESHOLD_ = 0.4f;
	// The limitation for exploring children of each parent
	private static int MAXCHILDEXPLORATION_ = 80;

	// No longer use batch, use second order cyc collection to classify
	// private static int BATCHSIZE_ = 200;

	@Override
	public Collection<DAGEdge> execute(Object... arg0)
			throws IllegalArgumentException, ModuleException {
		initialisationComplete(dag_.getNodes(), dag_.getEdges(), false);
		return null;
	}

	@Override
	public boolean initialisationComplete(Collection<DAGNode> nodes,
			Collection<DAGEdge> edges, boolean forceRebuild) {
		transitiveModule_ = (TransitiveIntervalSchemaModule) dag_
				.getModule(TransitiveIntervalSchemaModule.class);
		queryModule_ = (QueryModule) dag_.getModule(QueryModule.class);
		semanticSimilarityModule_ = (SemanticSimilarityModule) dag_
				.getModule(SemanticSimilarityModule.class);
		dummyDisjoints_ = new ConcurrentHashMap<Pair<String, String>, Boolean>();
		explored_= new ConcurrentHashMap<Pair<String, String>, Boolean>();
		resolvedNames_ = new ConcurrentHashMap<String, ArrayList<DAGNode>>();

		// explored_ = new ConcurrentHashMap<String, ConcurrentHashMap<String,
		// String>>();

		relationReliabilityCount_ = new ConcurrentHashMap<String, int[]>();
		interRelastionReliabilityCount_ = new ConcurrentHashMap<String, ConcurrentHashMap<Node, int[]>>();
		unknownBackups_ = new ConcurrentHashMap<String, ConcurrentHashMap<Pair<Node, Node>, ConcurrentLinkedQueue<Node>>>();
		IsAEdges_ = new ConcurrentHashMap<String, ArrayList<DAGNode>>();

		recordedAbstractness_ = new ConcurrentHashMap<Node, Float>();

		secondordercyc = (DAGNode) dag_.findOrCreateNode(
				"SecondOrderCollection", null, true);
		partiallyTangible = (DAGNode) dag_.findOrCreateNode(
				"PartiallyTangible", null, true);
		genls = CommonConcepts.GENLS.getNode(dag_);
		isa = CommonConcepts.ISA.getNode(dag_);
		and = CommonConcepts.AND.getNode(dag_);

		aliasModule_ = (NodeAliasModule) dag_.getModule(NodeAliasModule.class);

		// WMIAccess wmiAcc;
		// try {
		// //wmiAcc = new WMIAccess(1, -1);
		// //wmiSocket_ = wmiAcc.requestSocket();
		// } catch (UnknownHostException e) {
		// e.printStackTrace();
		// } catch (IOException e) {
		// e.printStackTrace();
		// }
		System.out.println("start to process concepts");

		// processYagoData();
		// processNELLData();
		// sampleDisjointPrecentile();

		try {
			processConceptNetData();
		} catch (Exception e) {
			e.printStackTrace();
		}

		// dag_.saveState();
		tryToProcessReliabilityCounts();
		// sampleDisjointPrecentile();
		System.out.println("process concepts done");
		printCounts();
		return true;
	}

	private void sampleDisjointPrecentile() {
		for (int j = 0; j < 5; j++) {
			try {
				int dc = 0;
				int cc = 0;
				int uc = 0;
				for (int i = 0; i < 1000; i++) {
					Thread.sleep(20);
					Node left = getRamdonGoodnode();
					Thread.sleep(10);
					Node right = getRamdonGoodnode();
					if (isAlreadyDisjointed(left, right))
						dc++;
					else if (hasConjoint(left, right))
						cc++;
					else
						uc++;
				}
				try (PrintWriter stat = new PrintWriter(new BufferedWriter(
						new FileWriter("stat.txt", true)))) {
					stat.println("dc " + dc + ",cc " + cc + ",uc " + uc + ", "
							+ ((double) dc) / 1000.0);
				} catch (IOException e) {
					e.printStackTrace();
				}
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
	}

	private Node getRamdonGoodnode() {
		boolean found = false;
		Node n = null;
		while (!found) {
			n = dag_.getRandomNode();
			if (isTangible(n) && getAllGenlsParents(n).size() != 0)
				found = true;
		}
		return n;
	}

	private void printCounts() {
		try (PrintWriter log = new PrintWriter(new BufferedWriter(
				new FileWriter("countLog.txt", true)))) {
			for (Entry<String, int[]> e : relationReliabilityCount_.entrySet()) {
				if (e.getValue() == null) {
					log.println(e.getKey() + " has null value");
				}

				// dis,con,unk
				System.out.println(e.getKey() + "," + e.getValue()[0] + ","
						+ e.getValue()[1] + "," + e.getValue()[2]);

				String relationname = e.getKey();

				for (Entry<Node, int[]> r : interRelastionReliabilityCount_
						.get(relationname).entrySet()) {

					// dis,con,unk
					log.println(r.getKey() + "," + r.getValue()[0] + ","
							+ r.getValue()[1] + "," + r.getValue()[2] + ","
							+ (r.getValue()[0] + r.getValue()[1]) + ","
							+ relationname);
				}
			}
			log.println("_notFoundCount: " + _notFoundCount);
			log.println("_transtivelyResolvedCount: "
					+ _transtivelyResolvedCount);
			log.println("_resolvedCount: " + _resolvedCount);
		} catch (IOException e1) {
			e1.printStackTrace();
		}
	}

	private void processYagoData() {
		int linecount = 0;

		File folder = new File("C:/Users/yh222/workspace/CycDag/Yago");
		if (folder.isDirectory()) {
			System.out.println("123");
		}
		File[] files = folder.listFiles();
		try (PrintWriter log = new PrintWriter(new BufferedWriter(
				new FileWriter("importerLog.txt", true)))) {
			String line;
			for (File file : files) {
				try (BufferedReader br = new BufferedReader(
						new FileReader(file))) {
					System.out.println("processing:" + file.getName());

					while ((line = br.readLine()) != null) {
						linecount++;

						// skip if the line is not start with '<'
						if (!line.startsWith("<"))
							continue;

						// replace _ with space and remove brackets
						line = line.replace("_", " ");
						line = line.replace(" .", "");
						line = line.replaceAll("[<>]", "");
						// Split the line to 3 parts: concept,relation,concept
						String[] parts = line.split("\\t");

						String relationName = parts[1];

						// The phase in bracket () may help resolution, but
						// remove them at the moment
						parts[0] = parts[0].replaceAll(", .*", "").replaceAll(
								" \\(.*\\)", "");
						parts[2] = parts[2].replaceAll(", .*", "").replaceAll(
								" \\(.*\\)", "");

						// System.out.println(parts[0]);
						// System.out.println(parts[2]);

						String nodename1 = parts[0];
						String nodename2 = parts[2];

						ArrayList<DAGNode> n1 = resolveAmbiguity(nodename1);
						if (n1 == null) {
							continue;
						}
						ArrayList<DAGNode> n2 = resolveAmbiguity(nodename2);
						if (n2 == null) {
							continue;
						}
						checkorAddRelation(relationName);
						Collection<Node> disjointCandidates1 = getDisjointCandidates(n1);
						Collection<Node> disjointCandidates2 = getDisjointCandidates(n2);

						for (Node c1 : disjointCandidates1) {
							for (Node c2 : disjointCandidates2) {
								updateSchema(relationName, log, c1, c2,
										nodename1, nodename2);

							}
						}

					}
				} catch (Exception e) {
					e.printStackTrace();
				}
			}
		} catch (IOException e1) {
			e1.printStackTrace();
		}
		tryToProcessReliabilityCounts();
	}

	private void processNELLData() {
		File folder = new File("I:/Documents/Java/CycDAG/NELL");
		if (folder.isDirectory()) {
			System.out.println("123");
		}
		File[] files = folder.listFiles();
		try (PrintWriter log = new PrintWriter(new BufferedWriter(
				new FileWriter("importerLog.txt", true)))) {
			String line;
			for (File file : files) {
				try (BufferedReader br = new BufferedReader(
						new FileReader(file))) {
					System.out.println("processing:" + file.getName());

					// Load the first line for indexing
					HashMap<String, Integer> indexmap = parseNellIndex(br
							.readLine());
					while ((line = br.readLine()) != null) {
						// Remove quotes
						line = line.replace("\"", "");
						String[] properties = line.split("\\t");

						String relationName = properties[indexmap
								.get("Relation")];

						Pattern pattern = Pattern.compile("-(.*)");
						Matcher matcher = pattern.matcher(properties[indexmap
								.get("Action")]);
						// Skip if this action start with '-'
						if (matcher.find()) {
							continue;
						}

						// Make first letter uppercase
						String nodename1 = properties[indexmap.get("Entity")];
						String nodename2 = properties[indexmap.get("Value")];
						ArrayList<DAGNode> n1 = resolveAmbiguity(nodename1);
						if (n1 == null) {
							continue;
						}
						ArrayList<DAGNode> n2 = resolveAmbiguity(nodename2);
						if (n2 == null) {
							continue;
						}
						checkorAddRelation(relationName);
						Collection<Node> disjointCandidates1 = getDisjointCandidates(n1);
						Collection<Node> disjointCandidates2 = getDisjointCandidates(n2);

						for (Node c1 : disjointCandidates1) {
							for (Node c2 : disjointCandidates2) {
								updateSchema(relationName, log, c1, c2,
										nodename1, nodename2);
							}
						}
					}
				} catch (Exception e) {
					e.printStackTrace();
				}

			}
		} catch (IOException e1) {
			e1.printStackTrace();
		}
		tryToProcessReliabilityCounts();
	}

	// Nell's structure is not stable that the indexes of column changes
	private HashMap<String, Integer> parseNellIndex(String line) {
		HashMap<String, Integer> map = new HashMap<String, Integer>();
		String[] indexes = line.split("\\t");
		for (int i = 0; i < indexes.length; i++) {
			// remove quote
			String index = indexes[i].replace("\"", "");
			if (index.equals("Relation"))
				map.put("Relation", i);
			else if (index.equals("Entity"))
				map.put("Entity", i);
			else if (index.equals("Value"))
				map.put("Value", i);
			else if (index.equals("Action"))
				map.put("Action", i);
		}
		return map;
	}

	private void processConceptNetData() throws URISyntaxException {
		File folder = new File("I:/Documents/Java/CycDAG/ConceptNet");
		File[] files = folder.listFiles();

		try (PrintWriter log = new PrintWriter(new BufferedWriter(
				new FileWriter("importerLog.txt", true)))) {
			String line;

			// Pre process IsA
			for (File file : files) {
				try (BufferedReader br = new BufferedReader(
						new FileReader(file))) {
					System.out.println("processing:" + file.getName());
					while ((line = br.readLine()) != null) {

						Pattern pattern = Pattern.compile("\\[(.+)\\]");
						Matcher matcher = pattern.matcher(line);
						if (matcher.find()) {
							String data = matcher.group(1);

							pattern = Pattern.compile("\\/r\\/([^\\,]+?)\\/");
							matcher = pattern.matcher(data);
							if (!matcher.find()) {
								continue;
							}
							String relationName = matcher.group(1);
							if (relationName.equals("IsA")) {

								pattern = Pattern
										.compile(",\\/c\\/en\\/([^\\,]+?)\\/");
								matcher = pattern.matcher(data);
								if (matcher.find()) { // Make first letter
														// uppercase
									String nodename1 = matcher.group(1);
									if (!matcher.find()) {
										continue;
									}
									String nodename2 = matcher.group(1);
									ArrayList<DAGNode> n1 = resolveAmbiguity(nodename1);
									ArrayList<DAGNode> n2 = resolveAmbiguity(nodename2);

									if (n1 == null && n2 != null) {
										// If this node is not resolvable, add
										// isa edge as backup
										if (!IsAEdges_.containsKey(nodename1))
											IsAEdges_
													.put(nodename1,
															new ArrayList<DAGNode>());
										IsAEdges_.get(nodename1).addAll(n2);
									}
								}
							}
						}
					}
				}
			}
			ExecutorService executor = Executors.newFixedThreadPool(4);
			for (File file : files) {
				Runnable worker = new ProcessCN5Thread(file);
				executor.execute(worker);

				// try (BufferedReader br = new BufferedReader(
				// new FileReader(file))) {
				// System.out.println("processing:" + file.getName());
				// while ((line = br.readLine()) != null) {
				//
				// Pattern pattern = Pattern.compile("\\[(.+)\\]");
				// Matcher matcher = pattern.matcher(line);
				// if (matcher.find()) {
				// String data = matcher.group(1);
				//
				// pattern = Pattern.compile("\\/r\\/([^\\,]+?)\\/");
				// matcher = pattern.matcher(data);
				// if (!matcher.find()) {
				// continue;
				// }
				// String relationName = matcher.group(1);
				//
				// pattern = Pattern
				// .compile(",\\/c\\/en\\/([^\\,]+?)\\/");
				// matcher = pattern.matcher(data);
				// if (matcher.find()) { // Make first letter uppercase
				// String nodename1 = matcher.group(1);
				// if (!matcher.find()) {
				// continue;
				// }
				// String nodename2 = matcher.group(1);
				//
				// if (relationName.equals("IsA")) {
				// continue;
				// }
				//
				// ArrayList<DAGNode> n1 =
				// resolveAmbiguity(nodename1);
				// ArrayList<DAGNode> n2 =
				// resolveAmbiguity(nodename2);
				//
				// // for now skip all resolvable pairs
				// if (n2 != null && n1 != null) {
				// _resolvedCount++;
				// continue;
				// }
				//
				// if (n1 == null) {
				// n1 = IsAEdges_.get(nodename1);
				// }
				// if (n2 == null) {
				// n2 = IsAEdges_.get(nodename2);
				// }
				//
				// if (n2 == null || n1 == null) {
				// _notFoundCount++;
				// continue;
				// }
				// _transtivelyResolvedCount++;
				//
				// checkorAddRelation(relationName);
				// Collection<Node> disjointCandidatesLeft =
				// getDisjointCandidates(n1);
				// Collection<Node> disjointCandidatesRight =
				// getDisjointCandidates(n2);
				//
				// for (Node left : disjointCandidatesLeft) {
				// for (Node right : disjointCandidatesRight) {
				// updateSchema(relationName, log, left,
				// right, nodename1, nodename2);
				// }
				// }
				// }
				// }
				//
				// }
				//
				// } catch (Exception e) {
				// e.printStackTrace();
				// System.err.print(e.getMessage());
				// }
			}
			executor.shutdown();
			while (!executor.isTerminated()) {

			}

		} catch (IOException e1) {
			e1.printStackTrace();
		}
	}

	private class ProcessCN5Thread implements Runnable {
		private File mFile;

		public ProcessCN5Thread(File file) {
			mFile = file;
		}

		@Override
		public void run() {
			String line;
			try (PrintWriter log = new PrintWriter(new BufferedWriter(
					new FileWriter(mFile.getName() + "importerLog.txt", true)))) {
				try (BufferedReader br = new BufferedReader(new FileReader(
						mFile))) {
					System.out.println("processing:" + mFile.getName());
					while ((line = br.readLine()) != null) {

						Pattern pattern = Pattern.compile("\\[(.+)\\]");
						Matcher matcher = pattern.matcher(line);
						if (matcher.find()) {
							String data = matcher.group(1);

							pattern = Pattern.compile("\\/r\\/([^\\,]+?)\\/");
							matcher = pattern.matcher(data);
							if (!matcher.find()) {
								continue;
							}
							String relationName = matcher.group(1);

							pattern = Pattern
									.compile(",\\/c\\/en\\/([^\\,]+?)\\/");
							matcher = pattern.matcher(data);
							if (matcher.find()) { // Make first letter uppercase
								String nodename1 = matcher.group(1);
								if (!matcher.find()) {
									continue;
								}
								String nodename2 = matcher.group(1);

								if (relationName.equals("IsA")) {
									continue;
								}

								ArrayList<DAGNode> n1 = resolveAmbiguity(nodename1);
								ArrayList<DAGNode> n2 = resolveAmbiguity(nodename2);

								// for now skip all resolvable pairs
								if (n2 != null && n1 != null) {
									_resolvedCount++;
									continue;
								}

								if (n1 == null) {
									n1 = IsAEdges_.get(nodename1);
								}
								if (n2 == null) {
									n2 = IsAEdges_.get(nodename2);
								}

								if (n2 == null || n1 == null) {
									_notFoundCount++;
									continue;
								}
								_transtivelyResolvedCount++;

								checkorAddRelation(relationName);
								Collection<Node> disjointCandidatesLeft = getDisjointCandidates(n1);
								Collection<Node> disjointCandidatesRight = getDisjointCandidates(n2);

								for (Node left : disjointCandidatesLeft) {
									for (Node right : disjointCandidatesRight) {
										updateSchema(relationName, log, left,
												right, nodename1, nodename2);
									}
								}
							}
						}

					}

				} catch (Exception e) {
					e.printStackTrace();
					System.err.print(e.getMessage());
				}
			} catch (IOException e1) {
				e1.printStackTrace();
			}
		}

	}

	private void tryToProcessReliabilityCounts() {
		try (PrintWriter out = new PrintWriter(new BufferedWriter(
				new FileWriter("newDisjoints.txt", true)))) {
			DecimalFormat df = new DecimalFormat("#.##");
			// For each relationship
			for (Entry<String, ConcurrentHashMap<Pair<Node, Node>, ConcurrentLinkedQueue<Node>>> r : unknownBackups_
					.entrySet()) {
				String relationname = r.getKey();
				ConcurrentHashMap<Pair<Node, Node>, ConcurrentLinkedQueue<Node>> unks = r
						.getValue();
				ConcurrentHashMap<Node, int[]> intermap = interRelastionReliabilityCount_
						.get(relationname);

				if (getReliabilityScore(
						relationReliabilityCount_.get(relationname),
						this._STATMIN) >= 0.85) {
					// If it is a reliable relationship

					// For each unk node
					for (Entry<Pair<Node, Node>, ConcurrentLinkedQueue<Node>> e : unks
							.entrySet()) {

						boolean good = isReliable(e.getValue(), intermap);

						StringBuffer sb = new StringBuffer("");

						if (good)
							createDisjointEdge(out, e.getKey().objA_,
									e.getKey().objB_, relationname, sb);
					}

				}

			}

		} catch (IOException e1) {
			e1.printStackTrace();
		}
	}

	private boolean isReliable(ConcurrentLinkedQueue<Node> originallist,
			ConcurrentHashMap<Node, int[]> intermap) {

		ConcurrentLinkedQueue<Node> lowest = new ConcurrentLinkedQueue<Node>();
		for (Node entry : originallist) {
			if (isSignificant(intermap.get(entry), this._STATMIN)) {
				boolean toAdd = true;
				for (Node node : lowest) {
					// For each node already in the list,
					if (isChild(entry, node)) {
						// if entry is child of an existing node, remove the
						// node
						lowest.remove(node);
					} else if (isChild(node, entry)) {
						// if entry is parent of an existing node, dont add the
						// entry
						toAdd = false;
						break;
					}
				}
				if (toAdd)
					lowest.add(entry);
			}
		}
		// Then for each lowest entry, if one is not reliable, return false
		for (Node node : lowest) {
			if (getReliabilityScore(intermap.get(node), this._STATMIN) < this._RELIABILITYTHRESHOLD) {
				return false;
			}
		}

		return true;
	}

	private boolean isSignificant(int[] countArray, int threshold) {
		double disjointcount = countArray[0];
		double conjointcount = countArray[1];
		return disjointcount + conjointcount >= threshold;
	}

	private double getReliabilityScore(int[] countArray, int threshold) {
		double disjointcount = countArray[0];
		double conjointcount = countArray[1];
		if ( /* conjointcount>0 || */disjointcount + conjointcount < threshold)
			return -1;
		else
			return disjointcount / (disjointcount + conjointcount);

	}

	// private void putUnknownsToDisjoint(String key, Pair<String, String> pair,
	// PrintWriter out) {
	// ArrayList<Pair<String, String>> l = unknownBackups_.get(key).get(pair);
	//
	// for (Pair<String, String> p : l) {
	// createDisjointEdge(out, p.objA_, p.objB_, key, "resolved",
	// "resolved");
	// }
	// l.clear();
	// }

	private void updateSchema(String relationName, PrintWriter log, Node left,
			Node right, String nodename1, String nodename2) {
		Pair<String, String> p = left.getName().hashCode() > right.getName()
				.hashCode() ? new Pair<String, String>(left.getName(),
				right.getName()) : new Pair<String, String>(right.getName(),
				left.getName());
		
		if (explored_.containsKey(p))
			return;
		
		
		String outStr;
		if (!left.equals(right)) {
			if (isAlreadyDisjointed(left, right)) {
				updateReliabilityCount(relationName, left, right, 0);
				outStr = relationName + ": " + left.getName()
						+ " known disjoint to " + right.getName() + ": "
						+ nodename1 + "," + nodename2;
			} else if (hasConjoint(left, right)) {
				updateReliabilityCount(relationName, left, right, 1);
				outStr = relationName + ": " + left.getName()
						+ " known conjoint to " + right.getName() + ": "
						+ nodename1 + "," + nodename2;
			} else {
				updateReliabilityCount(relationName, left, right, 2);
				outStr = relationName + ": " + left.getName() + " unknown to "
						+ right.getName() + ": " + nodename1 + "," + nodename2;
			}
			System.out.println(outStr);
			log.println(outStr);
		}
		
		explored_.put(p, true);
	}

	private void updateReliabilityCount(String relationName, Node left,
			Node right, int flag) {
		relationReliabilityCount_.get(relationName)[flag]++;

		ConcurrentHashMap<Node, int[]> intermap = interRelastionReliabilityCount_
				.get(relationName);
		ConcurrentHashMap<Pair<Node, Node>, ConcurrentLinkedQueue<Node>> unkmap = unknownBackups_
				.get(relationName);

		// Double loop to create pair of second order cyc isa parent from both
		// node
		ArrayList<Node> leftIsa = getAllGenlsParents(left);
		ArrayList<Node> rightIsa = getAllGenlsParents(right);

		ArrayList<Node> commonparents = getCommomParents(leftIsa,
				rightIsa);

		for (Node node : commonparents) {
			if (!isTangible(node))
				continue;
			if (!intermap.containsKey(node)) {
				intermap.put(node, new int[] { 0, 0, 0 });
			}
			intermap.get(node)[flag]++;
			if (flag == 2) {// If it's unknown, add to unknown backups
				Pair<Node, Node> pair = new Pair<Node, Node>(left, right);
				if (unkmap.get(pair) == null)
					unkmap.put(pair, new ConcurrentLinkedQueue<Node>());
				unkmap.get(pair).add(node);
			}

		}

	}

	private ArrayList<Node> getCommomParents(
			ArrayList<Node> listA, ArrayList<Node> listB) {
		ArrayList<Node> intersect = new ArrayList<Node>(
				CollectionUtils.intersection(listA, listB));
		return intersect;
	}

	private boolean isAlreadyDisjointed(Node targetNode, Node child) {
		return queryModule_.prove(CommonConcepts.DISJOINTWITH.getNode(dag_),
				targetNode, child);
	}

	private boolean hasConjoint(Node nodeA, Node nodeB) {
		if (isAlreadyDisjointed(nodeA, nodeB))
			return false;

		// Check they are not Genls to each other
		if (transitiveModule_.execute(true, nodeA, nodeB) != null
				|| transitiveModule_.execute(false, nodeA, nodeB) != null)
			return true;

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

	private void createDisjointEdge(PrintWriter out, Node left, Node right,
			String relationName, StringBuffer sb) {

		Pair<String, String> p = left.getName().hashCode() > right.getName()
				.hashCode() ? new Pair<String, String>(left.getName(),
				right.getName()) : new Pair<String, String>(right.getName(),
				left.getName());

		// check the pair has not being added
		if (dummyDisjoints_.containsKey(p))
			return;

		// Create disjoint
		out.println(sb.toString() + left.getName() + "," + right.getName()
				+ "," + relationName);

		Node[] edge = new Node[] { CommonConcepts.DISJOINTWITH.getNode(dag_),
				left, right };
		Node creator = new StringNode("ConceptNet" + relationName);

		dag_.findOrCreateEdge(edge, creator, true);

		// if (left.hashCode() > right.hashCode())
		dummyDisjoints_.put(p, true);
		// else
		// dummyDisjoints_.put(rightKey, leftKey);
	}

	private Collection<Node> getDisjointCandidates(
			ArrayList<DAGNode> nodes) {
		ArrayList<Node> retu = new ArrayList<Node>();

		for (Node node : nodes) {
			// Check if it is an individual
			ArrayList<Node> r = (ArrayList<Node>) CommonQuery.DIRECTGENLS
					.runQuery(dag_, node);
			if (r.size() == 0) {
				r.addAll(CommonQuery.MINISA.runQuery(dag_, node));
				// r=removeAbstractCandidates(r);

			} else {
				r.clear();
				r.addAll(CommonQuery.MINISA.runQuery(dag_, node));
				r.add(node);
			}
			r = removeInferiorNodes(r);
			r = removeMaterials(r);
			// assert r.get(0) != null;
			for (Node n : r) {
				if (isTangible(n)) {
					retu.add(n);
				}
			}
		}
		return retu;
	}

	private ArrayList<Node> removeInferiorNodes(
			ArrayList<Node> candidates) {
		ArrayList<Node> r = new ArrayList<Node>();
		int tang = Integer
				.parseInt(this.partiallyTangible.getProperty("depth"));

		for (Node node : candidates) {
			if (((DAGObject) node).getProperty("depth") == null)
				continue;
			int d = Integer.parseInt(((DAGNode) node).getProperty("depth"));
			if (d > 26)
				r.add(node);
		}
		return r;
	}

	private ArrayList<Node> removeMaterials(
			ArrayList<Node> candidates) {
		Node material = (DAGNode) dag_.findOrCreateNode(
				"CommonSubstances-Material-Topic", null, true);

		ArrayList<Node> r = new ArrayList<Node>();
		for (Node node : candidates) {
			if (!queryModule_.prove(isa, node, material))
				r.add(node);
		}
		return r;
	}

	// not used atm
	private ArrayList<Node> removeAbstractCandidates(
			ArrayList<Node> candidates) {
		ArrayList<Node> r = new ArrayList<Node>();
		for (Node node : candidates) {
			if (!isTooAbstract(node))
				r.add(node);
		}
		return r;
	}

	// not used atm
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

	private ArrayList<DAGNode> resolveAmbiguity(String nodename)
			throws IOException {
		if (resolvedNames_.containsKey(nodename)) {
			return resolvedNames_.get(nodename);
		}

		Collection<DAGNode> nodes = aliasModule_
				.findNodes(nodename, true, true);
		ArrayList<DAGNode> r = (ArrayList<DAGNode>) nodes;
		if (r.size() >= 1) {
			resolvedNames_.put(nodename, r);
			// _resolvedCount++;
			return r;
		} else {
			// _notFoundCount++;
		}

		// else {
		// r = getConcentratedConcept(nodename, nodes);
		// if (r != null) {
		// resolvedNames_.put(nodename, r);
		// _resolvedCount++;
		// return r;
		// } else
		// _notFoundCount++;
		// }

		return null;
	}

	// private ArrayList<DAGNode> getConcentratedConcept(String nodename,
	// Collection<DAGNode> nodes) throws IOException {
	// WeightedSet<Integer> w = wmiSocket_.getWeightedArticles(nodename);
	// // System.out.println(w);
	// ArrayList<DAGNode> r = new ArrayList<DAGNode>();
	//
	// if (w.size() > 0) {
	// for (int i = 0; i < w.size(); i++) {
	// int key = Integer.parseInt(w.getOrdered().toArray()[i]
	// .toString());
	// if (w.getWeight(key) >= 0.2) {
	// String wikiphase = wmiSocket_.getPageTitle(key, false);
	// Collection<DAGNode> nodesfromwiki = aliasModule_.findNodes(
	// wikiphase, true, true);
	// if (nodesfromwiki.size() > 0) {
	// r.addAll(nodesfromwiki);
	// }
	// }
	// }
	// return r;
	// }
	// return null;
	// }

	// TODO: mention it in report
	// private double getRelatednessMark(DAGNode node, int originalkey)
	// throws IOException {
	// Collection<Node> allParents = CommonQuery.MINGENLS.runQuery(dag_, node);
	// allParents.addAll(CommonQuery.MINISA.runQuery(dag_, node));
	// double r = 0;
	// ArrayList<Integer> l = new ArrayList<Integer>();
	//
	// // populate the list with all articles (in form of id) that likely
	// // linked to a parent of the node
	// for (Node n : allParents) {
	// // get prettry string of each parent
	// Node[] args = dag_.parseNodes(
	// "(prettyString-Canonical " + n.getIdentifier() + " ?X)",
	// null, false, false);
	// Collection<Substitution> results = queryModule_
	// .execute(new QueryObject(args));
	//
	// for (Substitution sub : results) {
	// // System.out.println("prettystring of " + n.getName() + " is "
	// // + sub.getSubstitution("?X").getName());
	// int key = wmiSocket_.getMostLikelyArticle(sub.getSubstitution(
	// "?X").getName());
	// if (key != -1) {
	// l.add(key);
	// }
	// }
	// }
	// List<Double> relatednessList = wmiSocket_.getRelatednessList(
	// originalkey, toIntArray(l));
	//
	// for (double d : relatednessList) {
	// // System.out.println(d);
	// if (d > r)
	// r = d;
	// }
	// // System.out
	// // .println("relatedness mark of " + node.getName() + " is " + r);
	// return r;
	// }

	/*
	 * Aux method to access wmiSocket.getRelatednessList method
	 */
	private Integer[] toIntArray(List<Integer> list) {
		Integer[] ret = new Integer[list.size()];
		int i = 0;
		for (Integer e : list)
			ret[i++] = e.intValue();
		return ret;
	}

	private Node getDeepestIsAParent(DAGNode n1) {
		Collection<Node> r = CommonQuery.MINISA.runQuery(dag_, n1);
		Node deepest = null;
		int max = 0;
		int d;
		for (Node n : r) {

			if (((DAGObject) n).getProperty("depth") == null)
				continue;

			d = Integer.parseInt(((DAGNode) n).getProperty("depth"));

			if (deepest == null) {
				deepest = n;
				max = d;
			} else if (d > max) {
				deepest = n;
				max = d;
			}
		}
		System.out.println(n1.getName() + "'s deep p is " + deepest.getName());
		return deepest;
	}

	private String covertToKMNodeName(String group) {
		String[] parts = group.split("\\_");
		StringBuffer r = new StringBuffer("");
		for (String s : parts) {
			r.append(s.substring(0, 1).toUpperCase() + s.substring(1));
		}
		return r.toString();
	}

	private void checkorAddRelation(String relationName) {
		if (!relationReliabilityCount_.containsKey(relationName)) {

			relationReliabilityCount_.put(relationName, new int[] { 0, 0, 0 });
			interRelastionReliabilityCount_.put(relationName,
					new ConcurrentHashMap<Node, int[]>());

			// explored_.put(relationName, new ConcurrentHashMap<String,
			// String>());
			unknownBackups_
					.put(relationName,
							new ConcurrentHashMap<Pair<Node, Node>, ConcurrentLinkedQueue<Node>>());

		}
	}

	private ArrayList<Node> getAllGenlsParents(Node inputNode) {
		ArrayList<Node> children = new ArrayList<Node>(
				CommonQuery.ALLGENLS.runQuery(dag_, inputNode));
		return children;
	}

	private ArrayList<Node> getAllChildren(Node inputNode) {
		ArrayList<Node> children = new ArrayList<Node>(
				CommonQuery.SPECS.runQuery(dag_, inputNode));
		return children;
	}

	private Float getSimilarity(Node nodeA, Node nodeB) {
		return semanticSimilarityModule_.semanticSimilarity(nodeA, nodeB);
	}

	private boolean isTangible(Node node) {
		// exclude itself
		if (node.equals(partiallyTangible))
			return false;

		return queryModule_.prove(genls, node, partiallyTangible);
	}

	// is na a child of nb?
	private boolean isChild(Node na, Node nb) {
		return queryModule_.prove(genls, na, nb);
	}

	private boolean isSecondOrderCollection(Node node) {
		return queryModule_.prove(isa, node, secondordercyc);
	}

}