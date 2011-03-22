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
package de.ovgu.featureide.core.fstmodel.preprocessor;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.Collection;
import java.util.HashMap;
import java.util.Scanner;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTClass;

/**
 * Build the FSTModel for preprocessor projects.
 * 
 * @author Jens Meinicke
 */
public class PPModelBuilder {

	private FSTModel model;
	private IFeatureProject featureProject;
	private Collection<String> features;
	
	public PPModelBuilder(IFeatureProject featureProject) {
		FSTModel oldModel = featureProject.getFSTModel();
		if (oldModel != null)
			oldModel.markObsolete();

		model = new FSTModel(featureProject.getProjectName());
		featureProject.setFSTModel(model);
		this.featureProject = featureProject;
	}
	
	public void buildModel() {
		model.classesMap = new HashMap<IFile, FSTClass>();
		model.classes = new HashMap<String, FSTClass>();
		model.features = new HashMap<String, FSTFeature>();
		
		features = featureProject.getFeatureModel().getLayerNames();
		for (String feature : features) {
			FSTFeature f = new FSTFeature(feature);
			model.features.put(feature, f);
		}
		try {
			buildModel(featureProject.getSourceFolder());
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * @param folder
	 * @throws CoreException 
	 */
	private void buildModel(IFolder folder) throws CoreException {
		for (IResource res : folder.members()) {
			if (res instanceof IFolder) {
				buildModel((IFolder)res);
			} else if (res instanceof IFile) {
				String text = getText((IFile)res);
				FSTClass currentClass = new FSTClass(res.getName());
				addClass(res.getName(), res.getFullPath().toOSString());
				model.classes.put(res.getName(), currentClass);
				for (String feature : features) {
					if (containsFeature(text, feature)) {
						FSTFeature currentFeature = model.features.get(feature);
						currentFeature.classes.put(res.getName(), currentClass);
					}
				}
			}
		}
	}

	/**
	 * This method should be implemented by preprocessor plug-ins.
	 * Return true if the file contains the feature.
	 * @param text
	 * 			The file text.
	 * @param feature 
	 * 			The current feature.
	 */
	protected boolean containsFeature(String text, String feature) {
		return text.contains(feature);
	}
	
	/**
	 * @param iFile
	 */
	private String getText(IFile iFile) {
		Scanner scanner = null;
		try {
			File file = iFile.getRawLocation().toFile();
			StringBuffer fileText = new StringBuffer();
			scanner = new Scanner(file);
			while (scanner.hasNext()) {
				fileText.append(scanner.nextLine());
				fileText.append("\r\n");
			}
			return fileText.toString();
		} catch (FileNotFoundException e) {
			CorePlugin.getDefault().logError(e);
		} finally{
			if(scanner!=null)
				scanner.close();
		}
		return "";
	}
	
	/**
	 * Adds a class to the java project model
	 * 
	 */
	private void addClass(String className, String source) {
		FSTClass currentClass = null;
		
		if (model.classes.containsKey(className)) {
			currentClass = model.classes.get(className);
		} else {
			currentClass = new FSTClass(className);
			model.classes.put(className, currentClass);
		}
		if (!model.classesMap.containsKey(source)) {
			
			model.classesMap.put(null, currentClass);
		}
	}
}