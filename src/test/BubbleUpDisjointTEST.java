package test;

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;
import graph.core.CommonConcepts;
import graph.core.CycDAG;
import graph.core.DAGEdge;
import graph.core.DAGNode;
import graph.core.Edge;
import graph.core.ErrorEdge;
import graph.core.Node;
import graph.core.OntologyFunction;
import graph.core.PrimitiveNode;
import graph.core.StringNode;
import graph.inference.CommonQuery;
import graph.inference.QueryObject;
import graph.inference.Substitution;
import graph.inference.VariableNode;
import graph.module.BubbleUpDisjointModule;
import graph.module.DateParseModule;
import graph.module.QueryModule;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import javax.naming.NamingException;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

public class BubbleUpDisjointTEST {

	private CycDAG dag_;
	private BubbleUpDisjointModule sut_;
	private QueryModule qm_;

	@Before
	public void setUp() throws Exception {
		dag_ = new CycDAG(new File("test"));
		qm_ = (QueryModule) dag_.getModule(QueryModule.class);
		assertNotNull(sut_);
		CommonConcepts.initialise((CycDAG) dag_);
	}

	@After
	public void tearDown() throws Exception {
		dag_.clear();
	}

	@Test
	public void testBubbleUpDisjoints() {
		Node creator = new StringNode("TestCreator");
		DAGNode genls = CommonConcepts.GENLS.getNode(dag_);
		DAGNode disjoint = CommonConcepts.DISJOINTWITH.getNode(dag_);
		DAGNode dog = (DAGNode) dag_.findOrCreateNode("Dog", creator, true,
				true, true);
		DAGNode cat = (DAGNode) dag_.findOrCreateNode("Cat", creator, true,
				true, true);
		DAGNode pig = (DAGNode) dag_.findOrCreateNode("Pig", creator, true,
				true, true);
		DAGNode cow = (DAGNode) dag_.findOrCreateNode("Cow", creator, true,
				true, true);
		DAGNode horse = (DAGNode) dag_.findOrCreateNode("Horse", creator, true,
				true, true);
		DAGNode bird = (DAGNode) dag_.findOrCreateNode("Bird", creator, true,
				true, true);

		DAGNode animal = (DAGNode) dag_.findOrCreateNode("Animal", creator,
				true, true, true);

		dag_.findOrCreateEdge(creator, new Node[] { genls, cat, animal }, false);
		dag_.findOrCreateEdge(creator, new Node[] { genls, dog, animal }, false);
		dag_.findOrCreateEdge(creator, new Node[] { genls, pig, animal }, false);
		dag_.findOrCreateEdge(creator, new Node[] { genls, cow, animal }, false);
		dag_.findOrCreateEdge(creator, new Node[] { genls, horse, animal },
				false);
		dag_.findOrCreateEdge(creator, new Node[] { genls, bird, animal },
				false);

		DAGNode toothbrush = (DAGNode) dag_.findOrCreateNode("Toothbrush",
				creator, true, true, true);

		dag_.findOrCreateEdge(creator,
				new Node[] { disjoint, cat, toothbrush }, false);
		dag_.findOrCreateEdge(creator,
				new Node[] { disjoint, pig, toothbrush }, false);
		dag_.findOrCreateEdge(creator,
				new Node[] { disjoint, cow, toothbrush }, false);
		dag_.findOrCreateEdge(creator,
				new Node[] { disjoint, bird, toothbrush }, false);
		dag_.findOrCreateEdge(creator,
				new Node[] { disjoint, horse, toothbrush }, false);

		// Added 5 disjoint edges out of 6 children in total, 5/6=83%
		assertTrue(qm_.prove(disjoint, toothbrush, bird));

		// Normal test to create a disjoint
		assertFalse(qm_.prove(disjoint, toothbrush, animal));
		// Check new disjoint edge added
		assertTrue(qm_.prove(disjoint, toothbrush, animal));

		// Remove the disjoint edge just added
		Edge edge = dag_.findOrCreateEdge(creator, new Node[] { disjoint,
				animal, toothbrush }, false);

		dag_.removeEdge(edge);
		assertFalse(qm_.prove(disjoint, toothbrush, animal));

		// Test conjoint in sub branch, no disjoint should be created
		DAGNode bangeDog = (DAGNode) dag_.findOrCreateNode("bangeDog", creator,
				true, true, true);
		dag_.findOrCreateEdge(creator, new Node[] { genls, bangeDog, dog },
				false);
		dag_.findOrCreateEdge(creator,
				new Node[] { genls, bangeDog, toothbrush }, false);

		assertFalse(qm_.prove(disjoint, toothbrush, animal));

	}

}
