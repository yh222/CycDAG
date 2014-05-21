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
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.net.UnknownHostException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
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
	private transient NodeAliasModule aliasModule_;
	private transient WMISocket wmiSocket_;
	private HashMap<String, int[]> relationCounts_;
	private transient HashMap<String, String> dummyDisjoints_;
	private transient HashSet<String> disjointRelations_;
	private transient HashSet<String> blackListRelations_;
	private transient HashMap<String, DAGNode> resolvedNames_;
	private transient HashMap<String, ArrayList<Pair<Node, Node>>> unknownBackups_;
	private transient DAGNode genls_;
	private transient DAGNode partiallyTangible_;

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
		dummyDisjoints_ = new HashMap<String, String>();
		resolvedNames_ = new HashMap<String, DAGNode>();
		unknownBackups_ = new HashMap<String, ArrayList<Pair<Node, Node>>>();
		disjointRelations_ = new HashSet<String>();
		blackListRelations_ = new HashSet<String>();
		genls_ = CommonConcepts.GENLS.getNode(dag_);
		partiallyTangible_ = (DAGNode) dag_.findOrCreateNode(
				"PartiallyTangible", null, true);
		blackListRelations_.add("IsA");
		blackListRelations_.add("RelatedTo");
		blackListRelations_.add("Synonym");
		blackListRelations_.add("HasProperty");
		blackListRelations_.add("InstanceOf");
		blackListRelations_.add("TranslationOf");
		blackListRelations_.add("DerivedFrom");
		blackListRelations_.add("Antonym");
		blackListRelations_.add("MemberOf");

		disjointRelations_.add("AtLocation");
		disjointRelations_.add("PartOf");
		// disjointRelations_.add("CausesDesire");
		// disjointRelations_.add("SimilarTo");
		// disjointRelations_.add("Attribute");
		// disjointRelations_.add("UsedFor");
		// disjointRelations_.add("CapableOf");
		// disjointRelations_.add("HasPrerequisite");
		// disjointRelations_.add("ReceivesAction");
		// disjointRelations_.add("Desires");
		// disjointRelations_.add("Causes");
		// disjointRelations_.add("Antonym");
		// disjointRelations_.add("HasA");
		// disjointRelations_.add("wordnet");
		// disjointRelations_.add("NotHasProperty");

		aliasModule_ = (NodeAliasModule) dag_.getModule(NodeAliasModule.class);

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

		processConceptNetData();
		System.out.println("process concepts done");
		printCounts();
		dag_.saveState();
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
		for (String e : disjointRelations_) {
			System.out.println("White listed relations: " + e);
		}
		for (String e : blackListRelations_) {
			System.out.println("Black listed relations: " + e);
		}
	}

	private void processNELLData() {
		File folder = new File("/NELL");
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

						// Skip blacklisted relation
						if (blackListRelations_.contains(relationName)) {
							continue;
						}

						Pattern pattern = Pattern.compile("y(.*)");
						Matcher matcher = pattern.matcher(properties[indexmap
								.get("Action")]);
						if (!matcher.find()) {
							continue;
						}

						// Make first letter uppercase
						String nodename1 = properties[indexmap.get("Entity")];
						String nodename2 = properties[indexmap.get("Value")];
						DAGNode n1 = resolveAmbiguity(nodename1);
						if (n1 == null) {
							continue;
						}
						DAGNode n2 = resolveAmbiguity(nodename2);
						if (n2 == null) {
							continue;
						}
						// }
						checkorAddRelation(relationName);
						Collection<Node> disjointCandidates1 = getDisjointCandidates(n1);
						Collection<Node> disjointCandidates2 = getDisjointCandidates(n2);

						try (PrintWriter out = new PrintWriter(
								new BufferedWriter(new FileWriter(
										"newDisjoints.txt", true)))) {
							for (Node c1 : disjointCandidates1) {
								for (Node c2 : disjointCandidates2) {
									updateSchema(relationName, log, out, c1,
											c2, nodename1, nodename2);
								}
							}
						}
					}
				} catch (Exception e) {
					e.printStackTrace();
				}
				checkRelationshipMarks();
			}
		} catch (IOException e1) {
			e1.printStackTrace();
		}

	}

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

	private void processConceptNetData() {
		// String[] filenames = new String[] { "part_00.csv", "part_01.csv",
		// "part_02.csv", "part_03.csv", "part_04.csv", "part_05.csv",
		// "part_06.csv", "part_07.csv", "part_08.csv", "part_09.csv",
		// "part_10.csv", "part_11.csv", "part_12.csv", "part_13.csv",
		// "part_14.csv", "part_15.csv", "part_16.csv", "part_17.csv",
		// "part_18.csv", "part_19.csv" };
		File folder = new File("/ConceptNet");
		File[] files = folder.listFiles();

		try (PrintWriter log = new PrintWriter(new BufferedWriter(
				new FileWriter("importerLog.txt", true)))) {
			String line;
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
							// Skip blacklisted relation
							if (blackListRelations_.contains(relationName)) {
								continue;
							}
							pattern = Pattern
									.compile(",\\/c\\/en\\/([^\\,]+?)\\/");
							matcher = pattern.matcher(data);
							if (matcher.find()) {
								// Make first letter uppercase
								String nodename1 = matcher.group(1);
								if (!matcher.find()) {
									continue;
								}
								String nodename2 = matcher.group(1);
								DAGNode n1 = resolveAmbiguity(nodename1);
								if (n1 == null) {
									continue;
								}
								DAGNode n2 = resolveAmbiguity(nodename2);
								if (n2 == null) {
									continue;
								}
								// }
								checkorAddRelation(relationName);
								Collection<Node> disjointCandidates1 = getDisjointCandidates(n1);
								Collection<Node> disjointCandidates2 = getDisjointCandidates(n2);

								try (PrintWriter out = new PrintWriter(
										new BufferedWriter(new FileWriter(
												"newDisjoints.txt", true)))) {
									for (Node c1 : disjointCandidates1) {
										for (Node c2 : disjointCandidates2) {
											updateSchema(relationName, log,
													out, c1, c2, nodename1,
													nodename2);
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
				checkRelationshipMarks();
			}
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
	}

	private void checkRelationshipMarks() {
		for (Entry<String, int[]> r : relationCounts_.entrySet()) {
			if (!disjointRelations_.contains(r.getKey())
					&& !blackListRelations_.contains(r.getKey())) {
				double disjointcount = r.getValue()[0];
				double conjointcount = r.getValue()[1];

				if (disjointcount + conjointcount >= 150) {
					if (conjointcount / (disjointcount + conjointcount) <= 0.05) {
						disjointRelations_.add(r.getKey());
						putUnknownsToDisjoint(r.getKey());
					} else {
						blackListRelations_.add(r.getKey());
					}
				}
			}
		}

	}

	private void putUnknownsToDisjoint(String key) {
		ArrayList<Pair<Node, Node>> l = unknownBackups_.get(key);
		try (PrintWriter out = new PrintWriter(new BufferedWriter(
				new FileWriter("newDisjoints.txt", true)))) {
			for (Pair<Node, Node> p : l) {
				createDisjointEdge(out, p.objA_, p.objB_, key, "resolved",
						"resolved");
			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	private void updateSchema(String relationName, PrintWriter log,
			PrintWriter out, Node c1, Node c2, String nodename1,
			String nodename2) {

		if (!c1.equals(c2)) {
			if (queryModule_.prove(CommonConcepts.DISJOINTWITH.getNode(dag_),
					c1, c2)) {
				System.out.println(relationName + ": " + c1.getName()
						+ " known disjoint to " + c2.getName());
				// log
				log.println(relationName + ": " + c1.getName()
						+ " known disjoint to " + c2.getName());
				relationCounts_.get(relationName)[0]++;
			} else if (transitiveModule_.execute(true, c1, c2) != null
					|| transitiveModule_.execute(false, c1, c2) != null) {
				relationCounts_.get(relationName)[1]++;
				System.out.println(relationName + ": " + c1.getName()
						+ " known conjoint to " + c2.getName());
				// log
				log.println(relationName + ": " + c1.getName()
						+ " known conjoint to " + c2.getName());
			} else {
				relationCounts_.get(relationName)[2]++;
				log.println(relationName + ": " + c1.getName() + " unknown to "
						+ c2.getName());

				// Check that this relation is good to use
				if (!disjointRelations_.contains(relationName)) {
					// save this pair for future use
					unknownBackups_.get(relationName).add(
							new Pair<Node, Node>(c1, c2));
					return;
				}
				createDisjointEdge(out, c1, c2, relationName, nodename1,
						nodename2);
			}
		}
	}

	private Node creator = new StringNode("ConceptNet Analyzer");

	private void createDisjointEdge(PrintWriter out, Node c1, Node c2,
			String relationName, String nodename1, String nodename2) {
		// check the pair has not being added
		if (dummyDisjoints_.containsKey(c1.getName())
				&& dummyDisjoints_.get(c1.getName()).equals(c2.getName()))
			return;
		else if (dummyDisjoints_.containsKey(c2.getName())
				&& dummyDisjoints_.get(c2.getName()).equals(c1.getName()))
			return;
		dag_.findOrCreateEdge(
				new Node[] { CommonConcepts.DISJOINTWITH.getNode(dag_), c1, c2 },
				creator, false);
		// Create disjoint
		out.println(c1.getName() + "," + c2.getName());
		dummyDisjoints_.put(c1.getName(), c2.getName());
	}

	private Collection<Node> getDisjointCandidates(DAGNode node) {
		assert node != null;
		// Check if it is an individual
		ArrayList<Node> r = (ArrayList<Node>) CommonQuery.DIRECTGENLS.runQuery(
				dag_, node);
		if (r.size() == 0) {
			r.addAll(CommonQuery.MINISA.runQuery(dag_, node));
		} else {
			r.clear();
			r.addAll(CommonQuery.MINISA.runQuery(dag_, node));
			r.add(node);
		}
		assert r.get(0) != null;
		ArrayList<Node> retu = new ArrayList<Node>();
		for (Node n : r) {
			if (queryModule_.prove(genls_, n, partiallyTangible_)) {
				retu.add(n);
			}
		}
		return retu;
	}

	private DAGNode resolveAmbiguity(String nodename) throws IOException {

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
		if (resolvedNames_.containsKey(nodename)) {
			return resolvedNames_.get(nodename);
		}
		Collection<DAGNode> nodes = aliasModule_
				.findNodes(nodename, true, true);
		DAGNode r;
		if (nodes.size() == 1) {
			r = (DAGNode) nodes.toArray()[0];
			return r;
		} else if (nodes.size() > 1) {
			// if (nodes.size() >= 1) {
			// System.out.println(nodes);
			r = getConcentratedConcept(nodename, nodes);
			if (r != null) {
				try (PrintWriter out = new PrintWriter(new BufferedWriter(
						new FileWriter("resolutionLog.txt", true)))) {
					System.out.println(nodename + " is most likely to be "
							+ r.getName());
					out.println(nodename + " is most likely to be "
							+ r.getName());
				}
				resolvedNames_.put(nodename, r);
				return r;
			}
		}
		return null;
	}

	private DAGNode getConcentratedConcept(String nodename,
			Collection<DAGNode> nodes) throws IOException {
		WeightedSet<Integer> w = wmiSocket_.getWeightedArticles(nodename);
		// System.out.println(w);
		if (w.size() >= 1) {
			int key = Integer.parseInt(w.getMostLikely().toArray()[0]
					.toString());
			String wikiphase = wmiSocket_.getPageTitle(key, false);
			if (w.getWeight(key) >= 0.95) {
				// System.out.println(nodename + "'s wikiphase is " +
				// wikiphase);
				DAGNode r = dag_.findDAGNode(nodename);

				if (r != null) {
					return r;
				}
				boolean occured = false;
				// double mark = 0;
				// find the node with greatest relatedness mark
				for (DAGNode n : nodes) {
					Node[] args = dag_.parseNodes("(prettyString-Canonical "
							+ n.getIdentifier() + " ?X)", null, false, false);
					Collection<Substitution> results = queryModule_
							.execute(new QueryObject(args));

					for (Substitution sub : results) {
						String s = sub.getSubstitution("?X").getName();
						s = s.substring(0, 1).toUpperCase() + s.substring(1);
						// System.out.println(s+" vs wiki "+wikiphase);
						if (s.equals(wikiphase)) {
							// If two nodes has the same prettystring dont
							// decide
							if (!occured) {
								occured = true;
								r = n;
							} else {
								return null;
							}
						}
					}

					// double t = getRelatednessMark(n, key);
					// if (t > mark) {
					// r = n;
					// mark=t;
					// }
				}
				return r;
			}
		}
		return null;
	}

	private double getRelatednessMark(DAGNode node, int originalkey)
			throws IOException {
		Collection<Node> allParents = CommonQuery.MINGENLS.runQuery(dag_, node);
		allParents.addAll(CommonQuery.MINISA.runQuery(dag_, node));
		double r = 0;
		ArrayList<Integer> l = new ArrayList<Integer>();
		for (Node n : allParents) {
			// get prettry string of each parent
			Node[] args = dag_.parseNodes(
					"(prettyString-Canonical " + n.getIdentifier() + " ?X)",
					null, false, false);
			Collection<Substitution> results = queryModule_
					.execute(new QueryObject(args));

			for (Substitution sub : results) {
				// System.out.println("prettystring of " + n.getName() + " is "
				// + sub.getSubstitution("?X").getName());
				int key = wmiSocket_.getMostLikelyArticle(sub.getSubstitution(
						"?X").getName());
				if (key != -1) {
					l.add(key);
				}
			}
		}
		List<Double> relatednessList = wmiSocket_.getRelatednessList(
				originalkey, toIntArray(l));
		for (double d : relatednessList) {
			// System.out.println(d);
			if (d > r)
				r = d;
		}
		// System.out
		// .println("relatedness mark of " + node.getName() + " is " + r);
		return r;
	}

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
		if (!relationCounts_.containsKey(relationName)) {
			relationCounts_.put(relationName, new int[] { 0, 0, 0 });
			unknownBackups_
					.put(relationName, new ArrayList<Pair<Node, Node>>());
		}
	}

}
