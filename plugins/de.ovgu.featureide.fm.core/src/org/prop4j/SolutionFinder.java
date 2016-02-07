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
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Random;

import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.minisat.core.Heap;
import org.sat4j.minisat.core.IOrder;
import org.sat4j.minisat.core.IPhaseSelectionStrategy;
import org.sat4j.minisat.core.Solver;
import org.sat4j.minisat.orders.NegativeLiteralSelectionStrategy;
import org.sat4j.minisat.orders.PositiveLiteralSelectionStrategy;
import org.sat4j.minisat.orders.VarOrderHeap;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.Feature;

/**
 * Finds certain solutions of propositional formulas.
 * 
 * @author Sebastian Krieter
 */
public class SolutionFinder {

	protected final HashMap<Object, Integer> varToInt = new HashMap<>();
	protected final HashMap<Integer, Object> intToVar = new HashMap<>();

	protected final Node root;
	protected final List<Feature> orderList;

	protected final Solver<?> solver;

	protected final int[] order;

	protected boolean contradiction = false;

	public SolutionFinder(Node root, List<Feature> orderList) {
		this.root = root;
		this.orderList = orderList;
		//		readVars(root);
		initVars(true);
		this.order = new int[varToInt.size() + 1];
		solver = initSolver(true);
	}

	public void setOrder(List<Feature> orderList) {
		int i = 0;
		for (Feature feature : orderList) {
			order[++i] = varToInt.get(feature.getName());
		}
	}

	private void initVars(boolean positive) {
		int index = 0;
		for (Feature feature : orderList) {
			index++;
			varToInt.put(feature.getName(), index);
			intToVar.put(index, feature.getName());
		}
	}

	protected Solver<?> initSolver(boolean positive) {
		final Solver<?> solver;
		solver = (Solver<?>) SolverFactory.newDefault();
		solver.setTimeoutMs(1000);
		solver.newVar(varToInt.size());

		try {
			for (Node node : root.getChildren()) {
				int[] clause = new int[node.children.length];
				final Node[] children = node.getChildren();
				for (int i = 0; i < children.length; i++) {
					Literal literal = (Literal) children[i];
					clause[i] = literal.positive ? varToInt.get(literal.var) : -varToInt.get(literal.var);
				}
				solver.addClause(new VecInt(clause));
			}
			return solver;
		} catch (ContradictionException e) {
			return null;
		}
	}

	private class VarOrderHeap2 extends VarOrderHeap {

		private static final long serialVersionUID = 1L;

		public VarOrderHeap2(IPhaseSelectionStrategy strategy) {
			super(strategy);
		}

		@Override
		public void init() {
			int nlength = this.lits.nVars() + 1;
			if (this.activity == null || this.activity.length < nlength) {
				this.activity = new double[nlength];
			}
			this.phaseStrategy.init(nlength);
			this.activity[0] = -1;
			this.heap = new Heap(this.activity);
			this.heap.setBounds(nlength);
			for (int i = 1; i < nlength; i++) {
				int x = order[i];
				this.activity[x] = 0.0;
				if (this.lits.belongsToPool(x)) {
					this.heap.insert(x);
				}
			}
		}

	}

	public List<String> getSolution(boolean positive) {
		if (solver != null) {
			final IOrder oldOrder = solver.getOrder();

			try {
				solver.setOrder(new VarOrderHeap2(positive ? new PositiveLiteralSelectionStrategy() : new NegativeLiteralSelectionStrategy()));

				int[] model = solver.findModel();
				if (model != null) {
					return convertToString(model);
				}
			} catch (Exception e) {
				FMCorePlugin.getDefault().logError(e);
			} finally {
				solver.setOrder(oldOrder);
			}

		}
		return Collections.emptyList();
	}

	private List<String> convertToString(int[] model) {
		final List<String> resultList = new ArrayList<>();
		for (int var : model) {
			final Object varObject = intToVar.get(var);
			if (varObject instanceof String) {
				resultList.add((String) varObject);
			}
		}
		return resultList;
	}

	public void findTWise() {
		final IVecInt orgBackbone = knownValues();
		final int featureCount = orderList.size();

		final int[] indexArray = new int[featureCount - orgBackbone.size()];
		final int[] indexArray2 = new int[featureCount + 1];
		int j = 0;
		for (int i = 0; i < featureCount; i++) {
			if ((i + 1) == Math.abs(orgBackbone.get(j))) {
				indexArray2[i + 1] = j;
				j++;
			} else {
				indexArray[i - j] = i + 1;
			}
			;
		}
		final int nonCoreFeatures = indexArray.length - 1;
		final byte[] combinations = new byte[nonCoreFeatures * nonCoreFeatures];

		int invalidCount = 0;
		for (Node clause : root.getChildren()) {
			final Node[] children = clause.getChildren();
			if (children.length == 2) {
				final Literal l1 = (Literal) children[0];
				final Literal l2 = (Literal) children[1];
				final int a = indexArray2[varToInt.get(l1.var)];
				final int b = indexArray2[varToInt.get(l2.var)];
				if (a != 0 && b != 0) {
					final int combinationIndex = a * nonCoreFeatures + b;
					if (!l1.positive) {
						if (!l2.positive) {
							combinations[combinationIndex] |= 1;
						} else {
							combinations[combinationIndex] |= 2;
						}
					} else {
						if (!l2.positive) {
							combinations[combinationIndex] |= 4;
						} else {
							combinations[combinationIndex] |= 8;
						}
					}
				}
				invalidCount++;
			} else if (children.length > 2) {
				for (int x = 0; x < children.length; x++) {
					final Literal l1 = (Literal) children[x];
					final Integer realA = varToInt.get(l1.var);
					final int a = indexArray2[realA];
					if (a != 0) {
						for (int y = x + 1; y < children.length; y++) {
							final Literal l2 = (Literal) children[y];
							final Integer realB = varToInt.get(l2.var);
							final int b = indexArray2[realB];
							if (b != 0) {
								orgBackbone.push(l1.positive ? -realA : realA);
								orgBackbone.push(l2.positive ? -realB : realB);
								try {
									if (!solver.isSatisfiable(orgBackbone)) {
										final int combinationIndex = a * nonCoreFeatures + b;
										if (!l1.positive) {
											if (!l2.positive) {
												combinations[combinationIndex] |= 1;
											} else {
												combinations[combinationIndex] |= 2;
											}
										} else {
											if (!l2.positive) {
												combinations[combinationIndex] |= 4;
											} else {
												combinations[combinationIndex] |= 8;
											}
										}
										invalidCount++;
									}
								} catch (TimeoutException e) {
									e.printStackTrace();
								} finally {
									orgBackbone.pop().pop();
								}
							}
						}
					}
				}
			}
		}
		System.out.println(invalidCount);

		final int findTWiseRandom = findTWiseRandom(orgBackbone, combinations, indexArray, nonCoreFeatures);
		System.out.println(findTWiseRandom);

		boolean[] featuresUsed = new boolean[featureCount + 1];
		int[] comboIndex = new int[combinations.length];
		for (int i = 0; i < comboIndex.length; i++) {
			comboIndex[i] = i;
		}

		int sumPartCount = 0;
		int count = 0;
		while (count < 100) {
			Arrays.fill(featuresUsed, false);
			for (int i = 0; i < orgBackbone.size(); i++) {
				featuresUsed[Math.abs(orgBackbone.get(i))] = true;
			}

			final VecInt backbone = new VecInt(orgBackbone.toArray().length);
			orgBackbone.copyTo(backbone);
			int[] curModel = null;
			boolean first = true;

			shuffle(comboIndex);

			for (int i = 0; i < combinations.length; i++) {
				final int index = comboIndex[i];
				final byte curCombo = combinations[index];
				final int a = indexArray[(index / nonCoreFeatures)];
				final int b = indexArray[(index % nonCoreFeatures)];
				if (a == b || featuresUsed[a] || featuresUsed[b]) {
					continue;
				}
				final int bit;
				switch (curCombo) {
				case 0:
				case 1:
				case 2:
				case 3:
				case 4:
				case 5:
				case 6:
				case 7:
					backbone.push(a);
					backbone.push(b);
					bit = 8;
					break;
				case 8:
				case 9:
				case 10:
				case 11:
					backbone.push(a);
					backbone.push(-b);
					bit = 4;
					break;
				case 12:
				case 13:
					backbone.push(-a);
					backbone.push(b);
					bit = 2;
					break;
				case 14:
					backbone.push(-a);
					backbone.push(-b);
					bit = 1;
					break;
				default:
					continue;
				}

				featuresUsed[a] = true;
				featuresUsed[b] = true;

				try {
					if (!solver.isSatisfiable(backbone)) {
						backbone.pop().pop();
						if (first) {
							combinations[index] |= bit;
						}
					} else {
						combinations[index] |= bit;

						curModel = solver.model();
						first = false;
					}
				} catch (TimeoutException e) {
					e.printStackTrace();
					backbone.pop().pop();
				}
			}

			if (curModel == null) {
				System.out.println("Unsatisfiable!");
				break;
			}

			int partCount = 0;
			for (int i = 0; i < combinations.length; i++) {
				final int a = indexArray[(i / nonCoreFeatures)];
				final int b = indexArray[(i % nonCoreFeatures)];
				if (a == b) {
					continue;
				}
				if (curModel[a] < 0) {
					if (curModel[b] < 0) {
						combinations[i] |= 1;
					} else {
						combinations[i] |= 2;
					}
				} else {
					if (curModel[b] < 0) {
						combinations[i] |= 4;
					} else {
						combinations[i] |= 8;
					}
				}

				final byte c = combinations[i];
				partCount += c % 2;
				partCount += (c >> 1) % 2;
				partCount += (c >> 2) % 2;
				partCount += (c >> 3) % 2;
			}

			final int maxCombinations = ((combinations.length - nonCoreFeatures) << 2) - invalidCount;
			System.out.println(count++ + ": " + (partCount - sumPartCount) + " " + (maxCombinations - (partCount)));
			sumPartCount = partCount;
			if (partCount == maxCombinations) {
				break;
			}
		}
	}

	private void shuffle(int[] array) {
		final Random random = new Random();
		for (int i = array.length - 1; i > 0; i--) {
			final int j = random.nextInt(i + 1);
			final int swap = array[j];
			array[j] = array[i];
			array[i] = swap;
		}
	}

	public int findTWiseRandom(IVecInt orgBackbone, byte[] combinations, int[] indexArray, int nonCoreFeatures) {
		final IOrder oldOrder = solver.getOrder();
		final int[] model1;
		final int[] model2;
		try {
			solver.setOrder(new VarOrderHeap2(new PositiveLiteralSelectionStrategy()));
			model1 = solver.findModel(orgBackbone);
			solver.setOrder(new VarOrderHeap2(new NegativeLiteralSelectionStrategy()));
			model2 = solver.findModel(orgBackbone);
		} catch (Exception e) {
			FMCorePlugin.getDefault().logError(e);
			return 0;
		} finally {
			solver.setOrder(oldOrder);
		}

		int count = 0;
		for (int i = 0; i < combinations.length; i++) {
			final int a = indexArray[(i / nonCoreFeatures)];
			final int b = indexArray[(i % nonCoreFeatures)];
			if (a == b) {
				continue;
			}
			if (model1[a] < 0) {
				if (model1[b] < 0) {
					combinations[i] |= 1;
				} else {
					combinations[i] |= 2;
				}
			} else {
				if (model1[b] < 0) {
					combinations[i] |= 4;
				} else {
					combinations[i] |= 8;
				}
			}

			if (model2[a] < 0) {
				if (model2[b] < 0) {
					count += (combinations[i] == 1) ? 1 : 2;
					combinations[i] |= 1;
				} else {
					count += (combinations[i] == 2) ? 1 : 2;
					combinations[i] |= 2;
				}
			} else {
				if (model2[b] < 0) {
					count += (combinations[i] == 4) ? 1 : 2;
					combinations[i] |= 4;
				} else {
					count += (combinations[i] == 8) ? 1 : 2;
					combinations[i] |= 8;
				}
			}
		}
		return count;
	}

	public List<String> deadCore() {
		return convertToString(knownValues().toArray());
	}

	public IVecInt knownValues() {
		final IVecInt backbone = new VecInt();
		final IOrder oldOrder = solver.getOrder();

		final int[] model1;
		final int[] model2;
		try {
			solver.setOrder(new VarOrderHeap2(new PositiveLiteralSelectionStrategy()));
			model1 = solver.findModel();
			solver.setOrder(new VarOrderHeap2(new NegativeLiteralSelectionStrategy()));
			model2 = solver.findModel();
		} catch (Exception e) {
			FMCorePlugin.getDefault().logError(e);
			contradiction = true;
			return null;
		} finally {
			solver.setOrder(oldOrder);
		}

		if (model1 != null) {
			for (int i = 0; i < model1.length; i++) {
				final int x = model1[i];
				final int y = model2[i];

				if (x == y) {
					// do not calculate dead feature
					if (x < 0) {
						continue;
					}
					try {
						backbone.push(-x);
						if (solver.isSatisfiable(backbone)) {
							backbone.pop();
						} else {
							backbone.pop().push(x);
						}
					} catch (TimeoutException e) {
						FMCorePlugin.getDefault().logError(e);
						backbone.pop();
					}
				}
			}
		}

		return backbone;
	}

}
