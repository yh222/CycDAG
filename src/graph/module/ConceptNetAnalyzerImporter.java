package graph.module;

import graph.core.CommonConcepts;
import graph.core.DAGEdge;
import graph.core.DAGNode;
import graph.core.DAGObject;
import graph.core.Node;
import graph.core.StringNode;
import graph.inference.CommonQuery;
import graph.inference.QueryObject;
import graph.inference.Substitution;
import graph.inference.VariableNode;
import io.resources.WMIAccess;
import io.resources.WMISocket;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.net.UnknownHostException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import util.AliasedObject;
import util.Pair;
import util.collection.WeightedSet;

public class ConceptNetAnalyzerImporter extends DAGModule<Collection<DAGEdge>> {

	private static final long serialVersionUID = -2241818554908651866L;
	private transient TransitiveIntervalSchemaModule transitiveModule_;
	private transient QueryModule queryModule_;
	private HashMap<String, int[]> relationCounts_;
	private transient WMISocket wmiSocket_;

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
		relationCounts_ = new HashMap<String, int[]>();
		WMIAccess wmiAcc;
		try {
			wmiAcc = new WMIAccess(1, -1);
			wmiSocket_ = wmiAcc.requestSocket();
		} catch (UnknownHostException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		System.out.println("start to process concepts");
		try {
			// System.out.println();
			WeightedSet<Integer> w = wmiSocket_.getWeightedArticles("cat");
			int key = Integer.parseInt(w.getMostLikely().toArray()[0]
					.toString());
			System.out.println(w.getWeight(key));

		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		processConcepts();
		System.out.println("process concepts done");
		printCounts();
		return true;
	}

	private void printCounts() {
		for (Entry<String, int[]> e : relationCounts_.entrySet()) {
			if (e.getValue() == null) {
				System.out.println(e.getKey() + " has null value");
			}

			System.out.println(e.getKey() + ": " + e.getValue()[0]
					+ " disjoints, " + e.getValue()[1] + " conjoints, "
					+ e.getValue()[2] + " unkown");
		}

	}

	private void processConcepts() {
		String line;
		String[] filenames = new String[] { "part_00.csv", "part_01.csv",
				"part_02.csv"/*
							 * , "part_03.csv", "part_04.csv", "part_05.csv",
							 * "part_06.csv", "part_07.csv", "part_08.csv",
							 * "part_09.csv", "part_10.csv", "part_11.csv",
							 * "part_12.csv", "part_13.csv", "part_14.csv",
							 * "part_15.csv", "part_16.csv", "part_17.csv",
							 * "part_18.csv", "part_19.csv"
							 */};
		NodeAliasModule aliasModule = (NodeAliasModule) dag_
				.getModule(NodeAliasModule.class);

		for (String filename : filenames) {
			try (BufferedReader br = new BufferedReader(
					new FileReader(filename))) {
				System.out.println("processing:" + filename);
				while ((line = br.readLine()) != null) {
					Pattern pattern = Pattern.compile("\\[(.+)\\]");
					Matcher matcher = pattern.matcher(line);
					if (matcher.find()) {
						String data = matcher.group(1);

						// System.out.println("data: "+data);

						pattern = Pattern.compile("\\/r\\/([^\\,]+?)\\/");
						matcher = pattern.matcher(data);
						matcher.find();
						String relationName = matcher.group(1);

						pattern = Pattern.compile(",\\/c\\/en\\/([^\\,]+?)\\/");
						matcher = pattern.matcher(data);
						if (matcher.find() /*
											 * &&
											 * relationName.equals("AtLocation")
											 */) {
							// Make first letter uppercase
							String nodename1 = covertToKMNodeName(matcher
									.group(1));

							DAGNode n1 = dag_.findDAGNode(nodename1);
							// System.out.println("Trying to find node:"
							// + nodename1);
							if (n1 == null) {
								Collection<DAGNode> nodes = aliasModule
										.findNodes(nodename1, false, true);
								// Collection<DAGNode> filteredNodes = new
								// ArrayList<>();
								// Node[] args =
								// dag_.parseNodes("(prettyString-Canonical ?X \""+
								// nodename1+"\")", null, false, false);
								//
								// for (DAGNode node : nodes) {
								// Substitution substitution = new
								// Substitution("?X", node);
								// boolean satisfies =
								// queryModule_.prove(substitution.applySubstitution(args));
								// if (satisfies) {
								// filteredNodes.add(node);
								// }
								// }

								if (nodes.size() == 1) {
									n1 = (DAGNode) nodes.toArray()[0];
									System.out.println(nodename1
											+ " is defined as " + n1.getName());
								} else if (nodes.size() > 1) {
									System.out.println(nodes);
									n1 = getConcentratedConcept(nodes.toArray());
									if (n1 == null) {
										continue;
									}
									System.out.println(nodename1
											+ " is most likely to be "
											+ n1.getName());
								} else {
									continue;
								}
							}

							matcher.find();
							String nodename2 = matcher.group(1).substring(0, 1)
									.toUpperCase()
									+ matcher.group(1).substring(1);
							nodename2.replaceAll("_", "");
							DAGNode n2 = dag_.findDAGNode(nodename2);
							// System.out.println("Trying to find node:"
							// + nodename2);
							if (n2 == null) {
								Collection<DAGNode> nodes = aliasModule
										.findNodes(nodename2, false, true);

								if (nodes.size() == 1) {
									n2 = (DAGNode) nodes.toArray()[0];
									System.out.println(nodename2
											+ " is defined as " + n2.getName());
								} else if (nodes.size() > 1) {
									n2 = getConcentratedConcept(nodes.toArray());
									if (n2 == null) {
										continue;
									}
									System.out.println(nodename2
											+ " is most likely to be "
											+ n2.getName());
								} else {
									continue;
								}
							}
							checkorAddRelation(relationName);
							Collection<Node> minGenls1 = CommonQuery.DIRECTGENLS
									.runQuery(dag_, n1);
							if (minGenls1.size() == 0) {
								minGenls1.addAll(CommonQuery.MINISA.runQuery(
										dag_, n1));
							} else {
								minGenls1.clear();
								minGenls1.add(n1);
							}

							Collection<Node> minGenls2 = CommonQuery.DIRECTGENLS
									.runQuery(dag_, n2);
							if (minGenls2.size() == 0) {
								minGenls2.addAll(CommonQuery.MINISA.runQuery(
										dag_, n2));
							} else {
								minGenls2.clear();
								minGenls2.add(n2);
							}
							// queryModule_.
							try (PrintWriter out = new PrintWriter(
									new BufferedWriter(new FileWriter(
											"newDisjoints.txt", true)))) {
								for (Node c1 : minGenls1) {
									for (Node c2 : minGenls2) {
										if (!c1.equals(c2)) {
											if (queryModule_.prove(
													CommonConcepts.DISJOINTWITH
															.getNode(dag_), c1,
													c2)) {
												System.out.println(relationName
														+ ": " + c1.getName()
														+ " disjoint to "
														+ c2.getName());
												relationCounts_
														.get(relationName)[0]++;
											} else if (transitiveModule_
													.execute(true, c1, c2) != null
													|| transitiveModule_
															.execute(false, c1,
																	c2) != null) {
												relationCounts_
														.get(relationName)[1]++;
												System.out.println(relationName
														+ ": " + c1.getName()
														+ " conjoint to "
														+ c2.getName());
											} else {
												relationCounts_
														.get(relationName)[2]++;
												// Create disjoint
												out.println(c1.getName()
														+ " disjointWith "
														+ c2.getName());
											}
										}
									}
								}
							}
						}
					}
				}

			} catch (Exception e) {
				e.printStackTrace();
				System.err.print(e.getMessage());
			}
		}

	}

	private DAGNode getConcentratedConcept(Object[] objects) throws IOException {
		for (Object n : objects) {
			WeightedSet<Integer> w = wmiSocket_
					.getWeightedArticles(((DAGNode) n).getName());
			System.out.println(w);
			if (w.getMostLikely().size() >= 1) {
				int key = Integer.parseInt(w.getMostLikely().toArray()[0]
						.toString());
				if (w.getWeight(key) >= 0.95) {
					System.out.println(((DAGNode) n).getName()+" is "+w.getWeight(key));

					return (DAGNode) n;
				}
			}

		}
		return null;
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
		if (!relationCounts_.containsKey(relationName)) {
			relationCounts_.put(relationName, new int[] { 0, 0, 0 });
		}
	}

}
