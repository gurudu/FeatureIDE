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
package de.ovgu.featureide.fm.core.conf.worker;

import java.util.Arrays;

import de.ovgu.featureide.fm.core.conf.AFeatureGraph;
import de.ovgu.featureide.fm.core.conf.MatrixFeatureGraph;
import de.ovgu.featureide.fm.core.conf.worker.base.AWorkerThread;
import de.ovgu.featureide.fm.core.job.WorkMonitor;

public class DFSThread extends AWorkerThread<String> {

	private static class SharedObjects {
		private final MatrixFeatureGraph featureGraph;
		private final boolean[] complete;

		public SharedObjects(MatrixFeatureGraph featureGraph) {
			this.featureGraph = featureGraph;
			this.complete = new boolean[featureGraph.getFeatureArray().length];
		}
	}

	private final byte[] visited;
	private final SharedObjects sharedObjects;

	public DFSThread(MatrixFeatureGraph featureGraph, WorkMonitor workMonitor) {
		super(workMonitor);
		sharedObjects = new SharedObjects(featureGraph);
		visited = new byte[featureGraph.getFeatureArray().length];
	}

	private DFSThread(DFSThread oldThread) {
		super(oldThread);
		this.sharedObjects = oldThread.sharedObjects;
		visited = new byte[oldThread.sharedObjects.featureGraph.getFeatureArray().length];
	}

	@Override
	protected void work(String object) {
		final int featureIndex = sharedObjects.featureGraph.getFeatureIndex(object);
//		if (featureIndex == 952) {
//			System.out.println();
//		}
			
		Arrays.fill(visited, (byte) 0);
		dfs(visited, sharedObjects.complete, featureIndex, true);
		Arrays.fill(visited, (byte) 0);
		dfs(visited, sharedObjects.complete, featureIndex, false);
		sharedObjects.complete[featureIndex] = true;
	}

	@Override
	protected DFSThread newThread() {
		return new DFSThread(this);
	}

	// visited: 0 not visited, 1 visited (unknown status), 2 visited (known status)
	private void dfs(byte[] visited, boolean[] complete, int curFeature, boolean selected) {
		//	System.out.println(featureArray[curFeature] + " " + selected);
		visited[curFeature] = 5;

		for (int j = 0; j < visited.length; j++) {
			final byte visit = visited[j];
			if (visit < 5) {
				final byte childSelected;
//				if (sharedObjects.featureGraph.getValue(curFeature, j, selected) > 0) {
//					System.out.println();
//				}
				switch (sharedObjects.featureGraph.getValue(curFeature, j, selected)) {
				case AFeatureGraph.VALUE_0Q:
					if (visit == 2) {
						continue;
					}
					if (visit == 3) {
						visited[j] = 4;
						childSelected = 2; // correct ???
//						childSelected = 4; // correct ???
					} else {
						visited[j] = 2;
						childSelected = 2;
					}
//					visited[j] = 4;
//					childSelected = 4;
					break;
				case AFeatureGraph.VALUE_1Q:
					if (visit == 3) {
						continue;
					}
					if (visit == 2) {
						visited[j] = 4;
						childSelected = 3; // correct ???
//						childSelected = 4; // correct ???
					} else {
						visited[j] = 3;
						childSelected = 3;
					}
//					visited[j] = 4;
//					childSelected = 4;
					break;
				case AFeatureGraph.VALUE_10Q:
					if (visit == 4) {
						continue;
					}
					visited[j] = 4;
					
					if (visit == 2) {
						childSelected = 3; // correct ???
					} else if (visit == 3) {
						childSelected = 2; // correct ???
					} else  {
						childSelected = 4;
					}
//					childSelected = 4;
					break;
				case AFeatureGraph.VALUE_0:
					// don't select child
					childSelected = 0;
					visited[j] = 5;
					break;
				case AFeatureGraph.VALUE_1:
					// select child
					childSelected = 1;
					visited[j] = 5;
					break;
				case AFeatureGraph.VALUE_NONE:
				default:
					continue;
				}

				dfs_rec(visited, complete, j, curFeature, childSelected, selected);
			}
		}
	}

	private void dfs_rec(byte[] visited, boolean[] complete, int curFeature, int parentFeature, byte selected, boolean parentSelected) {
		final boolean incomplete = !complete[curFeature];
		for (int j = 0; j < visited.length; j++) {
			final byte visit = visited[j];
			byte childSelected = -1;
//			final byte edge = sharedObjects.featureGraph.getEdge(curFeature, j);
//			if (sharedObjects.featureGraph.getEdge(curFeature, j) > 0) {
//				System.out.println();
//			}
			if (visit == 0) {
				switch (selected) {
				case 0:
					switch (sharedObjects.featureGraph.getValue(curFeature, j, false)) {
					case AFeatureGraph.VALUE_0Q:
						visited[j] = 2;
						childSelected = 2;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						break;
					case AFeatureGraph.VALUE_1Q:
						visited[j] = 3;
						childSelected = 3;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					case AFeatureGraph.VALUE_0:
						// don't select child
						childSelected = 0;
						visited[j] = 5;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10 : AFeatureGraph.EDGE_00);
						break;
					case AFeatureGraph.VALUE_1:
						// select child
						childSelected = 1;
						visited[j] = 5;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11 : AFeatureGraph.EDGE_01);
						break;
					default:
						continue;
					}
					break;
				case 1:
					switch (sharedObjects.featureGraph.getValue(curFeature, j, true)) {
					case AFeatureGraph.VALUE_0Q:
						visited[j] = 2;
						childSelected = 2;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						break;
					case AFeatureGraph.VALUE_1Q:
						visited[j] = 3;
						childSelected = 3;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					case AFeatureGraph.VALUE_0:
						// don't select child
						childSelected = 0;
						visited[j] = 5;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10 : AFeatureGraph.EDGE_00);
						break;
					case AFeatureGraph.VALUE_1:
						// select child
						childSelected = 1;
						visited[j] = 5;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11 : AFeatureGraph.EDGE_01);
						break;
					default:
						continue;
					}
					break;
				case 2:
					switch (sharedObjects.featureGraph.getValue(curFeature, j, false)) {
					case AFeatureGraph.VALUE_0Q:
						visited[j] = 2;
						childSelected = 2;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						break;
					case AFeatureGraph.VALUE_1Q:
						visited[j] = 3;
						childSelected = 3;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					case AFeatureGraph.VALUE_0:
						// don't select child
						childSelected = 2;
						visited[j] = 2;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						break;
					case AFeatureGraph.VALUE_1:
						// select child
						childSelected = 3;
						visited[j] = 3;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					default:
						continue;
					}
					break;
				case 3:
					switch (sharedObjects.featureGraph.getValue(curFeature, j, true)) {
					case AFeatureGraph.VALUE_0Q:
						visited[j] = 2;
						childSelected = 2;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						break;
					case AFeatureGraph.VALUE_1Q:
						visited[j] = 3;
						childSelected = 3;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					case AFeatureGraph.VALUE_0:
						// don't select child
						childSelected = 2;
						visited[j] = 2;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						break;
					case AFeatureGraph.VALUE_1:
						// select child
						childSelected = 3;
						visited[j] = 3;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					default:
						continue;
					}
					break;
				case 4:
					switch (sharedObjects.featureGraph.getValue(curFeature, j, false)) {
					case AFeatureGraph.VALUE_0Q:
						visited[j] = 2;
						childSelected = 2;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						break;
					case AFeatureGraph.VALUE_1Q:
						visited[j] = 3;
						childSelected = 3;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					case AFeatureGraph.VALUE_0:
						// don't select child
						childSelected = 2;
						visited[j] = 2;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						break;
					case AFeatureGraph.VALUE_1:
						// select child
						childSelected = 3;
						visited[j] = 3;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					default:
						break;
					}
					switch (sharedObjects.featureGraph.getValue(curFeature, j, true)) {
					case AFeatureGraph.VALUE_0Q:
						visited[j] = (byte) ((visited[j] == 3) ? 4 : 2);
						childSelected = (byte) ((childSelected == 3) ? 4 : 2);
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						break;
					case AFeatureGraph.VALUE_1Q:
						visited[j] = (byte) ((visited[j] == 2) ? 4 : 3);
						childSelected = (byte) ((childSelected == 2) ? 4 : 3);
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					case AFeatureGraph.VALUE_0:
						// don't select child
						childSelected = (byte) ((childSelected == 3) ? 4 : 2);
						visited[j] = (byte) ((visited[j] == 3) ? 4 : 2);
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						break;
					case AFeatureGraph.VALUE_1:
						// select child
						childSelected = (byte) ((childSelected == 2) ? 4 : 3);
						visited[j] = (byte) ((visited[j] == 2) ? 4 : 3);
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					default:
						break;
					}
					break;
				}
			} else if (visit == 2) {
				switch (selected) {
				case 0:
					switch (sharedObjects.featureGraph.getValue(curFeature, j, false)) {
					case AFeatureGraph.VALUE_1Q:
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
//						//TODO added
//						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						break;
					case AFeatureGraph.VALUE_0:
						// don't select child
						childSelected = 0;
						visited[j] = 5;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10 : AFeatureGraph.EDGE_00);
						break;
					case AFeatureGraph.VALUE_1:
						// select child
						childSelected = 1;
						visited[j] = 5;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11 : AFeatureGraph.EDGE_01);
						break;
					default:
						continue;
					}
					break;
				case 1:
					switch (sharedObjects.featureGraph.getValue(curFeature, j, true)) {
					case AFeatureGraph.VALUE_1Q:
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
//						//TODO added
//						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						break;
					case AFeatureGraph.VALUE_0:
						// don't select child
						childSelected = 0;
						visited[j] = 5;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10 : AFeatureGraph.EDGE_00);
						break;
					case AFeatureGraph.VALUE_1:
						// select child
						childSelected = 1;
						visited[j] = 5;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11 : AFeatureGraph.EDGE_01);
						break;
					default:
						continue;
					}
					break;
				case 2:
					switch (sharedObjects.featureGraph.getValue(curFeature, j, false)) {
					case AFeatureGraph.VALUE_1:
					case AFeatureGraph.VALUE_1Q:
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
//						//TODO added
//						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						break;
					default:
						continue;
					}
					break;
				case 3:
					switch (sharedObjects.featureGraph.getValue(curFeature, j, true)) {
					case AFeatureGraph.VALUE_1:
					case AFeatureGraph.VALUE_1Q:
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
//						//TODO added
//						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						break;
					default:
						continue;
					}
					break;
				case 4:
					switch (sharedObjects.featureGraph.getValue(curFeature, j, false)) {
					case AFeatureGraph.VALUE_1:
					case AFeatureGraph.VALUE_1Q:
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
//						//TODO added
//						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						break;
					default:
						break;
					}
					switch (sharedObjects.featureGraph.getValue(curFeature, j, true)) {
					case AFeatureGraph.VALUE_1:
					case AFeatureGraph.VALUE_1Q:
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
//						//TODO added
//						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						break;
					default:
						break;
					}
					break;
				}
			} else if (visit == 3) {
				switch (selected) {
				case 0:
					switch (sharedObjects.featureGraph.getValue(curFeature, j, false)) {
					case AFeatureGraph.VALUE_0Q:
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
//						//TODO added
//						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					case AFeatureGraph.VALUE_0:
						// don't select child
						childSelected = 0;
						visited[j] = 5;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10 : AFeatureGraph.EDGE_00);
						break;
					case AFeatureGraph.VALUE_1:
						// select child
						childSelected = 1;
						visited[j] = 5;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11 : AFeatureGraph.EDGE_01);
						break;
					default:
						continue;
					}
					break;
				case 1:
					switch (sharedObjects.featureGraph.getValue(curFeature, j, true)) {
					case AFeatureGraph.VALUE_0Q:
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
//						//TODO added
//						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					case AFeatureGraph.VALUE_0:
						// don't select child
						childSelected = 0;
						visited[j] = 5;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10 : AFeatureGraph.EDGE_00);
						break;
					case AFeatureGraph.VALUE_1:
						// select child
						childSelected = 1;
						visited[j] = 5;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11 : AFeatureGraph.EDGE_01);
						break;
					default:
						continue;
					}
					break;
				case 2:
					switch (sharedObjects.featureGraph.getValue(curFeature, j, false)) {
					case AFeatureGraph.VALUE_0:
					case AFeatureGraph.VALUE_0Q:
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
//						//TODO added
//						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					default:
						continue;
					}
					break;
				case 3:
					switch (sharedObjects.featureGraph.getValue(curFeature, j, true)) {
					case AFeatureGraph.VALUE_0:
					case AFeatureGraph.VALUE_0Q:
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
//						//TODO added
//						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					default:
						continue;
					}
					break;
				case 4:
					switch (sharedObjects.featureGraph.getValue(curFeature, j, false)) {
					case AFeatureGraph.VALUE_0:
					case AFeatureGraph.VALUE_0Q:
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
//						//TODO added
//						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					default:
						break;
					}
					switch (sharedObjects.featureGraph.getValue(curFeature, j, true)) {
					case AFeatureGraph.VALUE_0:
					case AFeatureGraph.VALUE_0Q:
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
//						//TODO added
//						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					default:
						break;
					}
					break;
				}
			} else if (visit == 4) {
				switch (selected) {
				case 0:
					switch (sharedObjects.featureGraph.getValue(curFeature, j, false)) {
					case AFeatureGraph.VALUE_0:
						// don't select child
						childSelected = 0;
						visited[j] = 5;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10 : AFeatureGraph.EDGE_00);
						break;
					case AFeatureGraph.VALUE_1:
						// select child
						childSelected = 1;
						visited[j] = 5;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11 : AFeatureGraph.EDGE_01);
						break;
					default:
						continue;
					}
					break;
				case 1:
					switch (sharedObjects.featureGraph.getValue(curFeature, j, true)) {
					case AFeatureGraph.VALUE_0:
						// don't select child
						childSelected = 0;
						visited[j] = 5;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10 : AFeatureGraph.EDGE_00);
						break;
					case AFeatureGraph.VALUE_1:
						// select child
						childSelected = 1;
						visited[j] = 5;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11 : AFeatureGraph.EDGE_01);
						break;
					default:
						continue;
					}
					break;
				default:
					break;
				}
			}
					

			if (incomplete) {
				if (childSelected == 4) {
					dfs_rec(visited, complete, j, parentFeature, childSelected, parentSelected);
//					dfs_rec(visited, complete, j, parentFeature, childSelected, parentSelected);
				} else if (childSelected >= 0) {
					dfs_rec(visited, complete, j, parentFeature, childSelected, parentSelected);
				}
			}
//			if (incomplete && childSelected >= 0) {
//				dfs_rec(visited, complete, j, parentFeature, childSelected, parentSelected);
//			}
//					
//					
//					
//					
//					
//					
//					
//					
//					switch (edge & AFeatureGraph.MASK_0_00110000) {
//					// visit = 0, not selected, implies not selected
//					case AFeatureGraph.EDGE_00:
//						visited[j] = 2;
//						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10 : AFeatureGraph.EDGE_00);
//						childSelected = 0;
//						break;
//					// visit = 0, not selected, implies selected
//					case AFeatureGraph.EDGE_01:
//						visited[j] = 2;
//						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11 : AFeatureGraph.EDGE_01);
//						childSelected = 1;
//						break;
//					// visit = 0, not selected, implies ?
//					case AFeatureGraph.EDGE_0Q:
//						visited[j] = 1;
//						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_1Q : AFeatureGraph.EDGE_0Q);
//						childSelected = 2;
//						break;
//					}
//					break;
//				case 1:
//					switch (edge & AFeatureGraph.MASK_1_00001100) {
//					// visit = 0, selected, implies not selected
//					case AFeatureGraph.EDGE_10:
//						visited[j] = 2;
//						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10 : AFeatureGraph.EDGE_00);
//						childSelected = 0;
//						break;
//					// visit = 0, selected, implies selected
//					case AFeatureGraph.EDGE_11:
//						visited[j] = 2;
//						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11 : AFeatureGraph.EDGE_01);
//						childSelected = 1;
//						break;
//					// visit = 0, selected, implies ?
//					case AFeatureGraph.EDGE_1Q:
//						visited[j] = 1;
//						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_1Q : AFeatureGraph.EDGE_0Q);
//						childSelected = 2;
//						break;
//					}
//					break;
//				case 2:
//					if (edge > 0) {
//						visited[j] = 1;
//						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_1Q : AFeatureGraph.EDGE_0Q);
//						childSelected = 2;
//					}
//					break;
//				}
//			} else if (visit == 1) {
//				final byte edge = sharedObjects.featureGraph.getEdge(curFeature, j);
//				switch (selected) {
//				case 0:
//					switch (edge & AFeatureGraph.MASK_0_00110000) {
//					// visit = 1, not selected, implies not selected
//					case AFeatureGraph.EDGE_00:
//						visited[j] = 2;
//						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10 : AFeatureGraph.EDGE_00);
//						childSelected = 0;
//						break;
//					// visit = 1, not selected, implies selected
//					case AFeatureGraph.EDGE_01:
//						visited[j] = 2;
//						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11 : AFeatureGraph.EDGE_01);
//						childSelected = 1;
//						break;
//					}
//					break;
//				case 1:
//					switch (edge & AFeatureGraph.MASK_1_00001100) {
//					// visit = 1, selected, implies not selected
//					case AFeatureGraph.EDGE_10:
//						visited[j] = 2;
//						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10 : AFeatureGraph.EDGE_00);
//						childSelected = 0;
//						break;
//					// visit = 1, selected, implies selected
//					case AFeatureGraph.EDGE_11:
//						visited[j] = 2;
//						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11 : AFeatureGraph.EDGE_01);
//						childSelected = 1;
//						break;
//					}
//					break;
//				}
//			}
		}
	}

}
