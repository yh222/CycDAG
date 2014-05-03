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
		disjointRelations_=new HashSet<String>();
		disjointRelations_.add("AtLocation");
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
				"part_02.csv", "part_03.csv", "part_04.csv", "part_05.csv",
				"part_06.csv", "part_07.csv", "part_08.csv", "part_09.csv",
				"part_10.csv", "part_11.csv", "part_12.csv", "part_13.csv",
				"part_14.csv", "part_15.csv", "part_16.csv", "part_17.csv",
				"part_18.csv", "part_19.csv" };

		for (String filename : filenames) {
			try (BufferedReader br = new BufferedReader(
					new FileReader(filename))) {
				System.out.println("processing:" + filename);
				while ((line = br.readLine()) != null) {
					Pattern pattern = Pattern.compile("\\[(.+)\\]");
					Matcher matcher = pattern.matcher(line);
					if (matcher.find()) {
						String data = matcher.group(1);

						pattern = Pattern.compile("\\/r\\/([^\\,]+?)\\/");
						matcher = pattern.matcher(data);
						matcher.find();
						String relationName = matcher.group(1);

						pattern = Pattern.compile(",\\/c\\/en\\/([^\\,]+?)\\/");
						matcher = pattern.matcher(data);
						if (matcher.find()) {
							// Make first letter uppercase
							String nodename1 = matcher.group(1);
							matcher.find();
							String nodename2 = matcher.group(1);
							// covertToKMNodeName(matcher.group(1));

							// DAGNode n1 = dag_.findDAGNode(nodename1);
							// System.out.println("Trying to find node:"
							// + nodename1);
							// if (n1 == null) {
							DAGNode n1 = resolveAmbiguity(nodename1);
							if (n1 == null) {
								continue;
							}
							// }

							// DAGNode n2 = dag_.findDAGNode(nodename2);
							// System.out.println("Trying to find node:"
							// + nodename2);
							// if (n2 == null) {
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
										updateSchema(relationName, out, c1, c2);
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

	private void updateSchema(String relationName, PrintWriter out, Node c1,
			Node c2) {		
		
		if (!c1.equals(c2)) {
			if (queryModule_.prove(CommonConcepts.DISJOINTWITH.getNode(dag_),
					c1, c2)) {
				System.out.println(relationName + ": " + c1.getName()
						+ " known disjoint to " + c2.getName());
				relationCounts_.get(relationName)[0]++;
			} else if (transitiveModule_.execute(true, c1, c2) != null
					|| transitiveModule_.execute(false, c1, c2) != null) {
				relationCounts_.get(relationName)[1]++;
				System.out.println(relationName + ": " + c1.getName()
						+ " known conjoint to " + c2.getName());
			} else {
				relationCounts_.get(relationName)[2]++;

				//Check that this relation is good to use
				if(!disjointRelations_.contains(relationName)){
					//TODO: save this pair for future use?
					return;
				}
				
				// check the pair has not being added
				if (dummyDisjoints_.containsKey(c1.getName())
						&& dummyDisjoints_.get(c1.getName()).equals(
								c2.getName()))
					return;
				else if (dummyDisjoints_.containsKey(c2.getName())
						&& dummyDisjoints_.get(c2.getName()).equals(
								c1.getName()))
					return;

				// Create disjoint
				out.println(c1.getName() + " disjointWith " + c2.getName());
				dummyDisjoints_.put(c1.getName(), c2.getName());
			}
		}
	}

	private Collection<Node> getDisjointCandidates(DAGNode node) {
		assert node != null;
		Collection<Node> r = CommonQuery.DIRECTGENLS.runQuery(dag_, node);
		if (r.size() == 0) {
			r.addAll(CommonQuery.MINISA.runQuery(dag_, node));
		} else {
			r.clear();
			r.add(node);
		}
		return r;
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
		Collection<DAGNode> nodes = aliasModule_.findNodes(nodename, false,
				true);
		DAGNode r;
		if (nodes.size() == 1) {
			r = (DAGNode) nodes.toArray()[0];
			System.out.println(nodename + " is defined as " + r.getName());
			return r;
		} else if (nodes.size() > 1) {
			System.out.println(nodes);
			r = getConcentratedConcept(nodename, nodes);
			if (r != null) {
				System.out.println(nodename + " is most likely to be "
						+ r.getName());
				return r;
			}
		}
		return null;
	}

	private DAGNode getConcentratedConcept(String nodename,
			Collection<DAGNode> nodes) throws IOException {
		WeightedSet<Integer> w = wmiSocket_.getWeightedArticles(nodename);
		System.out.println(w);
		if (w.size() >= 1) {
			int key = Integer.parseInt(w.getMostLikely().toArray()[0]
					.toString());
			if (w.getWeight(key) >= 0.95) {
				DAGNode r=null;
				double mark=0;
				//find the node with greatest relatedness mark
				for (DAGNode n : nodes) {
					double t=getRelatednessMark(n,key);
					if(t>mark){
						r=n;
					}
				}
				return r;
			}
		}
		return null;
	}

	private double getRelatednessMark(DAGNode node, int originalkey) throws IOException {
		Collection<Node> allParents=CommonQuery.DIRECTGENLS.runQuery(dag_, node);
		allParents.addAll(CommonQuery.DIRECTISA.runQuery(dag_, node));
		double r=0;
		ArrayList<Integer> l=new ArrayList<Integer>();
		for(Node n:allParents){
			int key=wmiSocket_.getMostLikelyArticle(((DAGNode)n).getProperty("prettyString-Canonical"));
			if(key!=-1){
				l.add(key);
			}
		}
		List<Double> relatednessList=wmiSocket_.getRelatednessList(originalkey, toIntArray(l));
		for(double d:relatednessList){
			r+=d;
		}
		
		return r;
	}
	
	private Integer[] toIntArray(List<Integer> list)  {
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
		}
	}

}
