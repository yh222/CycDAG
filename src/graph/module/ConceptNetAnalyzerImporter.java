package graph.module;

import graph.core.CommonConcepts;
import graph.core.DAGEdge;
import graph.core.DAGNode;
import graph.core.Node;
import graph.inference.CommonQuery;

import java.io.BufferedReader;
import java.io.FileReader;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map.Entry;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class ConceptNetAnalyzerImporter extends DAGModule<Collection<DAGEdge>> {

	private static final long serialVersionUID = -2241818554908651866L;
	private transient TransitiveIntervalSchemaModule transitiveModule_;
	private transient QueryModule queryModule_;
	private HashMap<String, int[]> relationCounts_;

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
		processConcepts();
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
		String[] filenames = new String[] { "part_12.csv", "part_13.csv",
				"part_14.csv", "part_15.csv", "part_16.csv", "part_17.csv",
				"part_18.csv", "part_19.csv" };
		for (String filename : filenames) {
			try (BufferedReader br = new BufferedReader(
					new FileReader(filename))) {
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
						if (matcher.find()) {
							// Make first letter uppercase
							String nodename1 = covertToKMNodeName(matcher
									.group(1));

							DAGNode n1 = dag_.findDAGNode(nodename1);
							// System.out.println("Trying to find node:"
							// + nodename1);
							if (n1 == null) {
								continue;
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
								continue;
							}

							checkorAddRelation(relationName);
							Collection<Node> minGenls1 = CommonQuery.MINGENLS
									.runQuery(dag_, n1);
							minGenls1.clear();
							minGenls1.add(n1);
							Collection<Node> minGenls2 = CommonQuery.MINGENLS
									.runQuery(dag_, n2);
							minGenls2.clear();
							minGenls2.add(n2);
							for (Node c1 : minGenls1) {
								for (Node c2 : minGenls2) {
									if (!c1.equals(c2)) {
										if (queryModule_.prove(
												CommonConcepts.DISJOINTWITH
														.getNode(dag_), c1, c2)) {
											System.out.println(relationName+": "+c1.getName()
													+ " disjoint to "
													+ c2.getName());
											relationCounts_.get(relationName)[0]++;
										} else if (transitiveModule_.execute(
												true, c1, c2) != null
												|| transitiveModule_.execute(
														false, c1, c2) != null) {
											relationCounts_.get(relationName)[1]++;
											System.out.println(relationName+": "+c1.getName()
													+ " conjoint to "
													+ c2.getName());
										} else {
											relationCounts_.get(relationName)[2]++;
										}
									}
								}
							}
						}
					}
				}

			} catch (Exception e) {

			}
		}

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
