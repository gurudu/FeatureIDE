/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors.featuremodel.layouts;

import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;


/**
 * Layouts the features at the feature diagram using a depth first search.
 * 
 * @author Thomas Thuem
 */
public class DepthFirstLayout extends FeatureDiagramLayoutManager {
	
	int yoffset;
	
	@Override
	public void layoutFeatureModel(FeatureModel featureModel) {
		yoffset = 0;
		depthFirstLayout(featureModel.getRoot(), 0, LAYOUT_MARGIN_X);
		yoffset=yoffset+FEATURE_SPACE_X;
		layout(yoffset, featureModel.getConstraints());
		layoutHidden(featureModel);
	}

	private int depthFirstLayout(Feature feature, int level, int x) {
		if(!isHidden(feature)){
			FeatureUIHelper.setLocation(feature,new Point(x, LAYOUT_MARGIN_Y + level*FEATURE_SPACE_Y));
			int newX = x;
			if(yoffset< LAYOUT_MARGIN_Y + level*FEATURE_SPACE_Y)
				yoffset=LAYOUT_MARGIN_Y + level*FEATURE_SPACE_Y;
			for (Feature child : feature.getChildren()) {
				newX = depthFirstLayout(child, level + 1, newX);			
			}
			return Math.max(newX, x + FeatureUIHelper.getSize(feature).width + FEATURE_SPACE_X);
		} else {
			return x;
		}

	}

}
