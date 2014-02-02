package graph.module.cli;

import graph.core.CycDAG;
import graph.core.Node;
import graph.core.StringNode;
import graph.core.cli.DAGPortHandler;
import core.Command;

public class BubbleUpDisjointCommand extends Command {

	@Override
	public String helpText() {
		// TODO: Write a help text
		return "";
	}

	@Override
	public String shortDescription() {
		return "Iterate throuth existing disjoint edges, and try to merge them one level higher each time using stastical method."
				+ " As a consequence, more generic disjoint edges will be introduced at cost of potential incorrect entries.";
	}

	@Override
	protected void executeImpl() {
		Node creator = new StringNode("BubbleUpCommand");
		DAGPortHandler dagHandler = (DAGPortHandler) handler;
		CycDAG dag=(CycDAG) dagHandler.getDAG();
		//dag.bubbleUpDisjoints(creator);
	}
}