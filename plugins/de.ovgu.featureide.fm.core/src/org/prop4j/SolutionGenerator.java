/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 * 
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package org.prop4j;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map.Entry;

import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.editing.NodeCreator;

/**
 * Generates solutions of a propositional formula which have high differences between each other.
 * 
 * @author Sebastian Krieter
 */
public class SolutionGenerator {

	private final HashMap<Object, Integer> varToInt = new HashMap<Object, Integer>();
	private final ArrayList<int[]> solutionList = new ArrayList<>();

	private final Object[] vars;
	private final ISolver solver;

	private final double autoCompleteLimit;

	private boolean contradiction;

	public SolutionGenerator(Node node, double epsilon) {
		autoCompleteLimit = 1.0 - epsilon;

		node = node.toCNF();
		if (node instanceof And) {
			for (Node andChild : node.getChildren()) {
				if (andChild instanceof Or) {
					for (Node orChild : andChild.getChildren()) {
						addLiteral(orChild);
					}
				} else {
					addLiteral(andChild);
				}
			}
		} else if (node instanceof Or) {
			for (Node orChild : node.getChildren()) {
				addLiteral(orChild);
			}
		} else {
			addLiteral(node);
		}

		vars = new Object[varToInt.size()];
		for (Entry<Object, Integer> entry : varToInt.entrySet()) {
			vars[entry.getValue() - 1] = entry.getKey();
		}

		solver = SolverFactory.newDefault();
		solver.setTimeoutMs(1000);
		solver.newVar(varToInt.size());
		addClauses(node);
	}

	private void addLiteral(Node orChild) {
		final Object var = ((Literal) orChild).var;
		if (!varToInt.containsKey(var)) {
			int index = varToInt.size() + 1;
			varToInt.put(var, index);
		}
	}

	private void addClauses(Node root) {
		try {
			if (root instanceof And) {
				for (Node node : root.getChildren()) {
					addClause(node);
				}
			} else {
				addClause(root);
			}
		} catch (ContradictionException e) {
			contradiction = true;
		}
	}

	private void addClause(Node node) throws ContradictionException {
		if (node instanceof Or) {
			int[] clause = new int[node.children.length];
			int i = 0;
			for (Node child : node.getChildren()) {
				clause[i++] = getLiteralIndex(child);
			}
			solver.addClause(new VecInt(clause));
		} else {
			int literal = getLiteralIndex(node);
			solver.addClause(new VecInt(new int[] { literal }));
		}
	}

	private int getLiteralIndex(Node node) {
		final Literal l = (Literal) node;
		return l.positive ? varToInt.get(l.var) : -varToInt.get(l.var);
	}

	public void addSolution(Iterable<String> features) {
		final int[] solution = new int[varToInt.size()];
		for (int i = 0; i < solution.length; i++) {
			solution[i] = -(i + 1);
		}
		for (String feature : features) {
			final Integer featureIndex = varToInt.get(feature);
			solution[featureIndex - 1] = featureIndex;
		}
		final Integer trueIndex = varToInt.get(NodeCreator.varTrue);
		if (trueIndex != null) {
			solution[trueIndex - 1] = trueIndex;
		}

		addSolution(solution);
	}

	public void addSolution(final int[] solution) {
		final int[] inverseSolution = new int[solution.length];
		for (int i = 0; i < inverseSolution.length; i++) {
			inverseSolution[i] = -solution[i];
		}
		try {
			solver.addClause(new VecInt(inverseSolution));
		} catch (ContradictionException e) {
			contradiction = true;
		}
		solutionList.add(solution);
	}

	public List<String> getLastSolution() {
		if (!solutionList.isEmpty()) {
			final int[] lastSolution = solutionList.get(solutionList.size() - 1);
			List<String> featureList = new ArrayList<>();
			for (int i = 0; i < lastSolution.length; i++) {
				if (lastSolution[i] > 0) {
					final Object object = vars[i];
					if (object instanceof String) {
						featureList.add((String) object);
					}
				}
			}
			return featureList;
		}
		return null;
	}

	public boolean generateSolution() {
		if (contradiction) {
			return false;
		}
		final int featureCount = varToInt.size() + 1;
		final int[] freq = new int[featureCount];

		// compute frequency
		for (int[] solution : solutionList) {
			for (int i = 1; i < featureCount; i++) {
				final int variable = solution[i - 1];
				freq[Math.abs(variable)] += Math.signum(variable);
			}
		}

		// sort features (calculate rank)
		Integer[] features = new Integer[featureCount];
		for (int i = 1; i < featureCount; i++) {
			features[i] = i;
		}
		Arrays.sort(features, 1, featureCount, new Comparator<Integer>() {
			@Override
			public int compare(Integer o1, Integer o2) {
				return Math.abs(freq[o1]) - Math.abs(freq[o2]);
			}
		});

		final VecInt curSolution = new VecInt();
		for (int i = 1; (i < featureCount) && !contradiction; i++) {
			final int featureIndex = features[i];
			final double limit = autoCompleteLimit - (freq[featureIndex] / ((double) (featureCount - 1)));
			if (limit < 0) {
				break;
			}
			testFeature(curSolution, freq[featureIndex] > 0 ? -featureIndex : featureIndex);
		}

		try {
			if (!contradiction && solver.isSatisfiable(curSolution)) {
				addSolution(solver.model());
			} else {
				contradiction = true;
			}
		} catch (TimeoutException e) {
			contradiction = true;
		}
		return !contradiction;
	}

	private void testFeature(final VecInt curSolution, final int feature) {
		curSolution.push(feature);
		try {
			if (!solver.isSatisfiable(curSolution, false)) {
				curSolution.pop().push(-feature);
			}
		} catch (TimeoutException e) {
			contradiction = true;
		}
	}

}
