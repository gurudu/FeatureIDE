/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.core.internal;

import static de.ovgu.featureide.fm.core.localization.StringTable.CALCULATE_CORE_AND_DEAD_FEATURES;
import static de.ovgu.featureide.fm.core.localization.StringTable.CHECKING_CONFIGURATIONS;
import static de.ovgu.featureide.fm.core.localization.StringTable.CHECKING_CONFIGURATIONS_FOR_UNUSED_FEATURES;
import static de.ovgu.featureide.fm.core.localization.StringTable.CHECK_VALIDITY_OF;
import static de.ovgu.featureide.fm.core.localization.StringTable.CONFIGURATION_;
import static de.ovgu.featureide.fm.core.localization.StringTable.DELETE_CONFIGURATION_MARKERS;
import static de.ovgu.featureide.fm.core.localization.StringTable.ERROR_WHILE_LOADING_FEATURE_MODEL_FROM;
import static de.ovgu.featureide.fm.core.localization.StringTable.GET_FALSE_OPTIONAL_FEATURES;
import static de.ovgu.featureide.fm.core.localization.StringTable.GET_SELECTION_MATRIX;
import static de.ovgu.featureide.fm.core.localization.StringTable.GET_UNUSED_FEATURES;
import static de.ovgu.featureide.fm.core.localization.StringTable.IS_INVALID;
import static de.ovgu.featureide.fm.core.localization.StringTable.LOAD_MODEL;
import static de.ovgu.featureide.fm.core.localization.StringTable.NO_COMPOSER_COULD_BE_CREATED_FOR_ID;
import static de.ovgu.featureide.fm.core.localization.StringTable.PERFORMING_FULL_BUILD;
import static de.ovgu.featureide.fm.core.localization.StringTable.REFESH_CONFIGURATION_FOLER;
import static de.ovgu.featureide.fm.core.localization.StringTable.REFRESH_COLLABORATION_VIEW;
import static de.ovgu.featureide.fm.core.localization.StringTable.SYNCHRONIZE_FEATURE_MODEL_AND_FEATURE_MODULES;
import static de.ovgu.featureide.fm.core.localization.StringTable.THE_FEATURE_MODULE_IS_EMPTY__YOU_EITHER_SHOULD_IMPLEMENT_IT_COMMA__MARK_THE_FEATURE_AS_ABSTRACT_COMMA__OR_REMOVE_THE_FEATURE_FROM_THE_FEATURE_MODEL_;

import java.io.File;
import java.io.FileNotFoundException;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Scanner;

import javax.annotation.CheckForNull;

import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceVisitor;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.resources.ProjectScope;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.IJobManager;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.osgi.service.prefs.BackingStoreException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.ComposerExtensionClass;
import de.ovgu.featureide.core.builder.ComposerExtensionManager;
import de.ovgu.featureide.core.builder.ExtensibleFeatureProjectBuilder;
import de.ovgu.featureide.core.builder.FeatureProjectNature;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.job.ModelScheduleRule;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.fm.core.FMComposerManager;
import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.ModelMarkerHandler;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.core.base.impl.ExtendedFeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.FeatureIDEFormat;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.io.FeatureOrderFormat;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;
import de.ovgu.featureide.fm.core.job.LongRunningJob;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Class that encapsulates any data and method related to FeatureIDE projects.
 * 
 * @author Marcus Leich
 * @author Thomas Thuem
 * @author Tom Brosch
 * @author Marcus Pinnecke (Feature Interface)
 */
public class FeatureProject extends BuilderMarkerHandler implements IFeatureProject, IResourceChangeListener {

	private static final CorePlugin LOGGER = CorePlugin.getDefault();

	private static final String FEATURE_MODULE_MARKER = "de.ovgu.featureide.core.featureModuleMarker";

	public class FeatureModelChangeListner implements IEventListener {
		/**
		 * listens to changed feature names
		 */
		public void propertyChange(FeatureIDEEvent evt) {

			if (EventType.FEATURE_NAME_CHANGED == evt.getEventType()) {
				String oldName = (String) evt.getOldValue();
				String newName = (String) evt.getNewValue();
				FeatureProject.this.renameFeature((IFeatureModel) evt.getSource(), oldName, newName);
			}
		}
	}

	/**
	 * the model representation of the model file
	 */
	private final FeatureModelManager featureModelManager;

	private FSTModel fstModel;

	/**
	 * a folder for the generated files (only needed if the Prject has only the
	 * FeatureIDE Nature)
	 */
	private IFolder binFolder;

	/**
	 * a folder for jar files
	 */
	private final IFolder libFolder;

	/**
	 * a folder for temporary generated files
	 */
	private final IFolder buildFolder;

	/**
	 * a folder containing all configuration files
	 */
	private final IFolder configFolder;

	/**
	 * a folder for source files
	 */
	private final IFolder sourceFolder;

	private final IProject project;

	private final ModelMarkerHandler<IFile> modelFile;

	private IComposerExtensionClass composerExtension = null;

	//TODO: Implement possibility to change this path
	private final String featureStubPath = "featurestub";

	private boolean configurationUpdate = false;

	public String getFeaturestubPath() {
		return featureStubPath;
	}

	/**
	 * If <code>true</code> there is something changed that is relevant for
	 * composition.<br>
	 * Usually the the folders of the selected features and the actual
	 * configuration file.
	 */
	private boolean buildRelevantChanges = false;

	private IFile currentConfiguration = null;

	private final LongRunningJob<Boolean> syncModulesJob = new LongRunningJob<>(SYNCHRONIZE_FEATURE_MODEL_AND_FEATURE_MODULES,
			new LongRunningMethod<Boolean>() {
				@Override
				public Boolean execute(IMonitor workMonitor) throws Exception {
					try {
						final IFolder folder = sourceFolder;
						final IFeatureModel model = featureModelManager.getObject();
						// prevent warnings, if the user has just created a project
						// without any source files
						// TODO This could be removed because the user could use the
						// modeling extension instead
						if (allFeatureModulesEmpty(folder)) {
							folder.deleteMarkers(FEATURE_MODULE_MARKER, true, IResource.DEPTH_ONE);
							return true;
						}
						// set marker for each folder
						if (folder.exists()) {
							workMonitor.setRemainingWork(folder.members().length);
							for (IResource res : folder.members()) {
								if (res.exists() && res instanceof IFolder) {
									setFeatureModuleMarker(model, (IFolder) res);
								}
								workMonitor.step();
							}
						}
					} catch (CoreException e) {
						LOGGER.logError(e);
					}
					return true;
				}
			});

	private final LongRunningJob<Boolean> configurationChecker = new LongRunningJob<>(CHECKING_CONFIGURATIONS_FOR_UNUSED_FEATURES,
			new LongRunningMethod<Boolean>() {
				@Override
				public Boolean execute(IMonitor workMonitor) throws Exception {
					final IFolder folder = configFolder;
					deleteConfigurationMarkers(folder, IResource.DEPTH_ZERO);
					workMonitor.setRemainingWork(7);
					next(CALCULATE_CORE_AND_DEAD_FEATURES, workMonitor);
					List<String> concreteFeatures = (List<String>) getOptionalConcreteFeatures();
					next(GET_SELECTION_MATRIX, workMonitor);
					final boolean[][] selectionMatrix = getSelectionMatrix(concreteFeatures);
					next(GET_FALSE_OPTIONAL_FEATURES, workMonitor);
					final Collection<String> falseOptionalFeatures = getFalseOptionalConfigurationFeatures(selectionMatrix, concreteFeatures);
					next(GET_UNUSED_FEATURES, workMonitor);
					workMonitor.checkCancel();
					final Collection<String> deadFeatures = getUnusedConfigurationFeatures(selectionMatrix, concreteFeatures);
					next("create marker: dead features", workMonitor);
					if (!deadFeatures.isEmpty()) {
						createConfigurationMarker(folder, MARKER_UNUSED + deadFeatures.size() + (deadFeatures.size() > 1 ? " features are " : " feature is ")
								+ "not used: " + createShortMessage(deadFeatures), -1, IMarker.SEVERITY_INFO);
					}
					next("create marker: false optional features", workMonitor);
					if (!falseOptionalFeatures.isEmpty()) {
						createConfigurationMarker(folder,
								MARKER_FALSE_OPTIONAL + falseOptionalFeatures.size() + (falseOptionalFeatures.size() > 1 ? " features are " : " feature is ")
										+ "optional but used in all configurations: " + createShortMessage(falseOptionalFeatures),
								-1, IMarker.SEVERITY_INFO);
					}
					next(REFESH_CONFIGURATION_FOLER, workMonitor);
					workMonitor.done();
					return true;
				}

				private void next(String subTaskName, IMonitor workMonitor) {
					workMonitor.step();
					workMonitor.setTaskName(subTaskName);
				}

				private String createShortMessage(Collection<String> features) {
					StringBuilder message = new StringBuilder();
					int addedFeatures = 0;
					for (String feature : features) {
						message.append(feature);
						message.append(", ");
						if (addedFeatures++ >= 10) {
							message.append("...");
							break;
						}
					}

					return message.toString();
				}
			});

	/**
	 * Creating a new ProjectData includes creating folders if they don't exist,
	 * registering workspace listeners and initialization of the wrapper object.
	 * 
	 * @param aProject
	 *            the FeatureIDE project
	 */
	public FeatureProject(IProject aProject) {
		super(aProject);
		project = aProject;

		try {
			project.refreshLocal(IResource.DEPTH_ONE, null);
		} catch (CoreException e) {
			LOGGER.logError(e);
		}

		if (project.getFile("mpl.velvet").exists()) {
			modelFile = new ModelMarkerHandler<>(project.getFile("mpl.velvet"));
		} else {
			modelFile = new ModelMarkerHandler<>(project.getFile("model.xml"));
		}

		featureModelManager = FeatureModelManager.getInstance(Paths.get(modelFile.getModelFile().getLocationURI()));
		featureModelManager.addListener(new FeatureModelChangeListner());

		// initialize project structure
		try {
			// workaround needed for project imports
			project.refreshLocal(IResource.DEPTH_INFINITE, null);
		} catch (CoreException e) {
			LOGGER.logError(e);
		}

		String projectBuildPath = getProjectBuildPath();

		try {

			// just create the bin folder if project hat only the FeatureIDE
			// Nature
			if (project.getDescription().getNatureIds().length == 1 && project.hasNature(FeatureProjectNature.NATURE_ID)) {
				if (!(projectBuildPath.isEmpty() && getProjectSourcePath().isEmpty())) {
					binFolder = CorePlugin.createFolder(project, "bin");
				}
			}
		} catch (CoreException e) {
			LOGGER.logError(e);
		}
		libFolder = project.getFolder("lib");
		buildFolder = CorePlugin.createFolder(project, projectBuildPath);
		configFolder = CorePlugin.createFolder(project, getProjectConfigurationPath());
		sourceFolder = CorePlugin.createFolder(project, getProjectSourcePath());
		fstModel = null;
		// loading model data and listen to changes in the model file
		addModelListener();
		Job job = new Job(LOAD_MODEL) {
			protected IStatus run(IProgressMonitor monitor) {
				if (loadModel()) {
					return Status.OK_STATUS;
				}
				return Status.CANCEL_STATUS;
			}
		};
		job.setPriority(Job.INTERACTIVE);
		job.schedule();

		// make the composer ID a builder argument
		setComposerID(getComposerID());
		setPaths(getProjectSourcePath(), projectBuildPath, getProjectConfigurationPath());

		// adds the compiler to the feature project if it is an older project
		IComposerExtensionClass composer = getComposer();
		if (composer != null) {
			if (sourceFolder != null) {
				composer.addCompiler(getProject(), sourceFolder.getProjectRelativePath().toOSString(), configFolder.getProjectRelativePath().toOSString(),
						buildFolder.getProjectRelativePath().toOSString());
			}
		}

		// XXX MPL: hack for importing mpl projects
		if (getFeatureModel() instanceof ExtendedFeatureModel) {
			try {
				modelFile.getModelFile().touch(null);
			} catch (CoreException e) {
				LOGGER.logError(e);
			}
		}
	}

	public void dispose() {
		removeModelListener();
	}

	/**
	 * Loads the model again from the file. Attend that all local changes in the
	 * model get lost.<br>
	 * 
	 * Before loading, all error markers will be deleted and afterwards new ones
	 * might be created if some errors occur.
	 */
	synchronized private boolean loadModel() {
		guidslToXML();

		try {
			//			modelReader.readFromFile(modelFile.getModelFile());
			getComposer();
			if (composerExtension != null && composerExtension.createFolderForFeatures()) {
				createAndDeleteFeatureFolders();
				setAllFeatureModuleMarkers();
			}
			readFeatureOrder();
			return true;
			//		} catch (FileNotFoundException e) {
			//			modelFile.createModelMarker(e.getMessage(), IMarker.SEVERITY_ERROR, 0);
			//		} catch (UnsupportedModelException e) {
			//			modelFile.createModelMarker(e.getMessage(), IMarker.SEVERITY_ERROR, e.lineNumber);
		} catch (CoreException e) {
			LOGGER.logError(ERROR_WHILE_LOADING_FEATURE_MODEL_FROM + modelFile.getModelFile(), e);
		}
		return false;
	}

	/**
	 * Reads the feature order from the deprecated order file if it still exists
	 * 
	 * @throws CoreException
	 * 
	 */
	private void readFeatureOrder() throws CoreException {
		IFile orderFile = project.getFile(".order");
		final IFeatureModel featureModel = featureModelManager.getObject();
		if (featureModel.getFeatureOrderList().isEmpty() && !featureModel.getProperty().isFeatureOrderInXML() && orderFile.exists()) {

			FileHandler.load(Paths.get(orderFile.getLocationURI()), featureModel, new FeatureOrderFormat());
			// write feature order to model
			// XmlFeatureModelWriter modelWriter = new
			// XmlFeatureModelWriter(featureModel);
			FeatureModelManager.writeToFile(featureModel, Paths.get(modelFile.getModelFile().getLocationURI()));
		}
		/*
		 * TODO delete .order file in 2013 delete
		 * de.ovgu.featureide.fm.ui.editors
		 * .FeatureOrderEditor#writeToOrderFile() and corresponding call see
		 * TODOs
		 */
		// if (file.exists()){
		// file.delete();
		// project.refreshLocal(IResource.DEPTH_ONE, null);
		// }
	}

	/**
	 * If the project contains only an old model in guidsl format it will be
	 * converted into a .xml
	 */
	private void guidslToXML() {
		if (project.getFile("model.m").exists() && !project.getFile("model.xml").exists()) {
			FeatureModelManager.convert(Paths.get(project.getFile("model.m").getLocationURI()), Paths.get(project.getFile("model.xml").getLocationURI()));
			// TODO GUIDSL Annotations, should be handled in guidsl format #write
			//				if (!guidslReader.getAnnLine().isEmpty()) {
			//					ModelMarkerHandler<IFile> modelFile = new ModelMarkerHandler<>(project.getFile("model.m"));
			//					for (int i = 0; i < guidslReader.getAnnLine().size(); i++)
			//						modelFile.createModelMarker(THIS_ANNOTATION_IS_NOT_SUPPORTED_YET___MOVED_TO_THE_COMMENT_SECTION_, IMarker.SEVERITY_WARNING,
			//								guidslReader.getAnnLine().get(i));
			//				}
		}
	}

	private void createAndDeleteFeatureFolders() throws CoreException {
		sourceFolder.refreshLocal(IResource.DEPTH_ONE, null);
		final IFeatureModel featureModel = featureModelManager.getObject();
		// create folders for all layers
		if (featureModel instanceof ExtendedFeatureModel) {
			for (IFeature feature : featureModel.getFeatures()) {
				if (feature.getStructure().isConcrete() && feature instanceof ExtendedFeature && !((ExtendedFeature) feature).isFromExtern()) {
					createFeatureFolder(feature.getName());
				}
			}
		} else {
			for (IFeature feature : featureModel.getFeatures()) {
				if (feature.getStructure().isConcrete()) {
					createFeatureFolder(feature.getName());
				}
			}
		}
		// delete all empty folders which do not anymore belong to layers
		for (IResource res : sourceFolder.members())
			if (res instanceof IFolder && res.exists()) {
				IFolder folder = (IFolder) res;
				IFeature feature = featureModel.getFeature(folder.getName());
				if (feature == null || !feature.getStructure().isConcrete()) {
					folder.refreshLocal(IResource.DEPTH_ONE, null);
					if (folder.members().length == 0)
						folder.delete(false, null);
				}
			}
	}

	private void addModelListener() {
		ResourcesPlugin.getWorkspace().addResourceChangeListener(this, IResourceChangeEvent.POST_CHANGE);
	}

	private void removeModelListener() {
		ResourcesPlugin.getWorkspace().removeResourceChangeListener(this);
	}

	private void createFeatureFolder(String name) {
		try {
			IFolder folder = sourceFolder.getFolder(name);
			if (!folder.exists() && composerExtension.hasFeatureFolder() && composerExtension.createFolderForFeatures()) {
				folder.create(false, true, null);
				LOGGER.fireFeatureFolderChanged(folder);
			}
		} catch (CoreException e) {
			modelFile.createModelMarker(e.getMessage(), IMarker.SEVERITY_WARNING, 0);
		}
	}

	private void renameFeature(final IFeatureModel model, String oldName, String newName) {
		final IComposerExtensionClass composer = getComposer();
		boolean renamePerformed = false;
		IJobManager manager = Job.getJobManager();
		try {
			manager.beginRule(ModelScheduleRule.RULE, null);
			renamePerformed = FMComposerManager.getFMComposerExtension(getProject()).performRenaming(oldName, newName, project);
		} finally {
			manager.endRule(ModelScheduleRule.RULE);
		}
		if (!renamePerformed && composer.hasFeatureFolder()) {
			try {
				sourceFolder.refreshLocal(IResource.DEPTH_ONE, null);
				IFolder folder = sourceFolder.getFolder(oldName);
				if (folder.isAccessible()) {
					IPath newPath = sourceFolder.getFolder(newName).getFullPath();
					folder.move(newPath, true, null);
					folder.refreshLocal(IResource.DEPTH_ZERO, null);
					LOGGER.fireFeatureFolderChanged(folder);
				}
			} catch (CoreException e) {
				LOGGER.logError(e);
				modelFile.createModelMarker(e.getMessage(), IMarker.SEVERITY_WARNING, 0);
			}
		}
		if (configFolder != null) {
			if (configFolder.isAccessible()) {
				try {
					configFolder.refreshLocal(IResource.DEPTH_ONE, null);
					configurationUpdate = true;
					configFolder.accept(new IResourceVisitor() {
						private final String suffix = "." + composer.getConfigurationExtension();
						private final Configuration config = new Configuration(model, Configuration.PARAM_LAZY);
						private final FileHandler<Configuration> handler = new FileHandler<>(config);

						@Override
						public boolean visit(IResource resource) throws CoreException {
							final String name = resource.getName();
							if (resource instanceof IFile && name.endsWith(suffix)) {
								final IPersistentFormat<Configuration> format = ConfigurationManager.getFormat(resource.getName());
								final java.nio.file.Path path = Paths.get(resource.getLocationURI());
								handler.setFormat(format);
								handler.setPath(path);
								handler.read();
								handler.write();
							}
							return true;
						}
					}, IResource.DEPTH_ONE, IResource.NONE);
					configFolder.refreshLocal(IResource.DEPTH_ONE, null);
				} catch (CoreException e) {
					LOGGER.logError(e);
				} finally {
					configurationUpdate = false;
				}
			}
		}
	}

	public String getProjectName() {
		return project.getName();
	}

	public IFile getCurrentConfiguration() {
		if (currentConfiguration != null && currentConfiguration.exists())
			return currentConfiguration;

		if (getConfigFolder() == null)
			return null;

		String configuration = null;
		try {
			if (project.exists() && project.isOpen()) {
				configuration = project.getPersistentProperty(configConfigID);
			}
		} catch (CoreException e) {
			LOGGER.logError(e);
		}

		if (configuration != null) {
			IFile file = configFolder.getFile(configuration);
			if (file.exists())
				return file;
		}

		// no valid configuration found
		if (!getConfigFolder().exists())
			return null;

		List<IFile> configs = getAllConfigurations();
		if (configs.isEmpty())
			return null;

		// select the first configuration
		IFile config = configs.get(0);
		setCurrentConfiguration(config);
		return config;
	}

	public void setCurrentConfiguration(IFile file) {
		final boolean performBuild = currentConfiguration != null;
		currentConfiguration = file;

		int offset = getConfigFolder().getProjectRelativePath().toString().length();
		String configPath = file.getProjectRelativePath().toString().substring(offset);
		try {
			project.setPersistentProperty(configConfigID, configPath);
			LOGGER.fireCurrentConfigurationChanged(this);
		} catch (CoreException e) {
			LOGGER.logError(e);
		}

		// We need to call the builder here, because for the new configuration,
		// there are possibly no resource build yet or they are not up-to-date.
		// Eclipse calls builders, if a resource as changed, but in this case
		// actually no resource in the file system changes.
		if (performBuild) {
			LongRunningMethod<Boolean> job = new LongRunningMethod<Boolean>() {
				@Override
				public Boolean execute(IMonitor workMonitor) throws Exception {
					buildRelevantChanges = true;
					try {
						project.build(IncrementalProjectBuilder.FULL_BUILD, null);
					} catch (CoreException e) {
						LOGGER.logError(e);
					}
					return true;
				}
			};
			LongRunningWrapper.getRunner(job, PERFORMING_FULL_BUILD).schedule();
		}
	}

	@CheckForNull
	public String getBuildPath() {
		return buildFolder != null ? buildFolder.getRawLocation().toOSString() : null;
	}

	public IFolder getBinFolder() {
		return binFolder;
	}

	public IFolder getLibFolder() {
		return libFolder;
	}

	public IFolder getBuildFolder() {
		return buildFolder;
	}

	public IFolder getConfigFolder() {
		return configFolder;
	}

	public IFolder getSourceFolder() {
		if (composerExtension.hasSourceFolder()) {
			return sourceFolder;
		} else {
			return buildFolder;
		}
	}

	public String getBinPath() {
		return binFolder.getRawLocation().toOSString();
	}

	public String getConfigPath() {
		return configFolder.getRawLocation().toOSString();
	}

	public String getSourcePath() {
		return sourceFolder == null ? null : sourceFolder.getRawLocation().toOSString();
	}

	public String getFeatureName(IResource resource) {
		return getFolderName(resource, sourceFolder);
	}

	public String getConfigName(IResource resource) {
		return getFolderName(resource, buildFolder);
	}

	public String getFolderName(IResource resource, IFolder folder) {
		// check whether resource belongs to this project
		if (resource.getProject() != project)
			return null;
		IPath path = resource.getFullPath();
		String segment = path.segment(1);
		if (segment != null && segment.equals(folder.getName())) {
			return path.segment(2);
		}
		return null;
	}

	public IProject getProject() {
		return project;
	}

	public ProjectSignatures getProjectSignatures() {
		if (fstModel != null) {
			return fstModel.getProjectSignatures();
		}
		return null;
	}

	public FSTModel getFSTModel() {
		return fstModel;
	}

	public IFeatureModel getFeatureModel() {
		return featureModelManager.getObject();
	}

	public IFile getModelFile() {
		return modelFile.getModelFile();
	}

	public String[] getJavaClassPath() {
		ArrayList<String> cp = new ArrayList<String>();
		cp.add(".");
		cp.add(binFolder.getRawLocation().toOSString());
		if (libFolder.exists()) { // delete lib folder implementation
			cp.add(libFolder.getRawLocation().toOSString());
			try {
				for (IResource res : libFolder.members())
					if (res instanceof IFile && ((IFile) res).getName().endsWith(".jar"))
						cp.add(res.getRawLocation().toOSString());
			} catch (CoreException e) {
				LOGGER.logError(e);
			}
		}

		String[] paths = getAdditionalJavaClassPath();
		for (String path : paths)
			cp.add(path);

		return cp.toArray(new String[cp.size()]);
	}

	public String[] getAdditionalJavaClassPath() {
		ArrayList<String> cp = new ArrayList<String>();
		String classPath = null;
		try {
			classPath = project.getPersistentProperty(javaClassPathID);
		} catch (CoreException e) {
			LOGGER.logError(e);
		}
		if (classPath != null) {
			String[] paths = classPath.split(";");
			for (String path : paths)
				cp.add(path);
		}
		return cp.toArray(new String[cp.size()]);
	}

	/**
	 * refreshes Feature Module Markers for all folders in the source folder
	 * 
	 * @param featureModel
	 * @param sourceFolder
	 */
	/*
	 * The first job is waiting for the synchronization job to finish and sets
	 * the variable waiting, so the job will finish early. Than a new job is
	 * started.
	 * 
	 * If <syncJob.join()> is called outside of a job the workspace is blocked,
	 * because the method has a higher priority than the synchronization job.
	 * 
	 * The goal of this is that a synchronization can't be executed
	 * unnecessarily multiple times.
	 */
	// TODO this should not be called if only markers are changed
	private synchronized void setAllFeatureModuleMarkers() {
		syncModulesJob.schedule();
	}

	/**
	 * creates (or deletes) Feature Module Marker for the specified folder
	 * representing a feature module includes markers for: empty folders for
	 * concrete features, non-empty folders for abstract features, folders
	 * without corresponding feature.
	 * 
	 * @param featureModel
	 * @param folder
	 *            the folder
	 */
	private void setFeatureModuleMarker(final IFeatureModel featureModel, IFolder folder) {
		IFeature feature = featureModel.getFeature(folder.getName());
		try {
			folder.deleteMarkers(FEATURE_MODULE_MARKER, true, IResource.DEPTH_ZERO);
		} catch (CoreException e) {
			LOGGER.logError(e);
		}

		String message = null;
		int severity = IMarker.SEVERITY_WARNING;
		if (feature == null) {
			severity = IMarker.SEVERITY_ERROR;
			message = "The feature module \"" + folder.getName() + "\" has no corresponding feature at the feature model.";
		} else {
			try {
				final int memberCount = folder.members().length;
				if (feature.getStructure().isConcrete() && memberCount == 0) {
					message = THE_FEATURE_MODULE_IS_EMPTY__YOU_EITHER_SHOULD_IMPLEMENT_IT_COMMA__MARK_THE_FEATURE_AS_ABSTRACT_COMMA__OR_REMOVE_THE_FEATURE_FROM_THE_FEATURE_MODEL_;
				} else if (feature.getStructure().isAbstract() && memberCount > 0) {
					message = "This feature module is ignored as \"" + feature.getName() + "\" is marked as abstract.";
				}
			} catch (CoreException e) {
				LOGGER.logError(e);
			}
		}
		if (message != null) {
			try {
				if (folder.findMarkers(FEATURE_MODULE_MARKER, false, IResource.DEPTH_ZERO).length == 0 && folder.exists()) {
					IMarker marker = folder.createMarker(FEATURE_MODULE_MARKER);
					marker.setAttribute(IMarker.MESSAGE, message);
					marker.setAttribute(IMarker.SEVERITY, severity);
				}
			} catch (CoreException e) {
				LOGGER.logError(e);
			}
		}
	}

	protected boolean allFeatureModulesEmpty(IFolder sourceFolder) throws CoreException {
		if (!sourceFolder.exists()) {
			return false;
		}
		for (IResource res : sourceFolder.members())
			if (res instanceof IFolder && ((IFolder) res).members().length > 0)
				return false;
		return true;
	}

	public void resourceChanged(IResourceChangeEvent event) {
		// if something in source folder changed
		if (sourceFolder != null && event.getDelta().findMember(sourceFolder.getFullPath()) != null) {

			// set markers, only if event is not fired from changes to markers
			if (event.findMarkerDeltas(FEATURE_MODULE_MARKER, false).length == 0 && composerExtension != null && composerExtension.createFolderForFeatures()) {
				setAllFeatureModuleMarkers();
			}
		}

		IPath modelPath = modelFile.getModelFile().getFullPath();
		if (checkModelChange(event.getDelta().findMember(modelPath)))
			return;

		try {
			List<IFile> configs = getAllConfigurations();
			List<IFile> changedConfigs = new ArrayList<IFile>();
			IFile currentConfig = getCurrentConfiguration();
			for (IFile config : configs) {
				IResourceDelta delta = event.getDelta().findMember(config.getFullPath());
				if (delta != null) {
					checkFeatureCoverage();
					break;
				}
			}

			for (IFile config : configs) {
				IResourceDelta delta = event.getDelta().findMember(config.getFullPath());
				if (delta != null && (delta.getFlags() & IResourceDelta.CONTENT) != 0) {
					changedConfigs.add(config);
					if (config.equals(currentConfig)) {
						buildRelevantChanges = true;
					}
				}
			}
			if (!configurationUpdate && !changedConfigs.isEmpty()) {
				LOGGER.fireConfigurationChanged(this);
				checkConfigurations(changedConfigs);
			}

			if (!buildRelevantChanges && sourceFolder != null && sourceFolder.isAccessible()) {
				if (currentConfig != null && composerExtension != null && composerExtension.hasFeatureFolder()) {
					// ignore changes in unselected feature folders
					List<String> selectedFeatures = readFeaturesfromConfigurationFile(currentConfig.getRawLocation().toFile());
					for (IResource res : sourceFolder.members()) {
						if (res instanceof IFolder) {
							if (selectedFeatures.contains(res.getName())) {
								checkSourceFolder((IFolder) res, event);
							}
						}
					}
				} else {
					checkSourceFolder(sourceFolder, event);
				}
			}

			if (composerExtension != null && buildFolder != null && buildFolder.isAccessible()) {
				checkBuildFolder(buildFolder, event);
			}

		} catch (CoreException e) {
			LOGGER.logError(e);
		}
	}

	/**
	 * checks if something at source folder has been changed, except of marker
	 * changes
	 * 
	 */
	private void checkSourceFolder(IFolder folder, IResourceChangeEvent event) throws CoreException {
		if (!buildRelevantChanges) {
			IResourceDelta delta = event.getDelta().findMember(folder.getFullPath());
			if (delta != null) {
				if (delta.getKind() != IResourceDelta.NO_CHANGE) {
					if (checkSourceFolderChanges(folder, event)) {
						buildRelevantChanges = true;
					}
				}
			}
		}
	}

	private boolean checkSourceFolderChanges(IFolder folder, IResourceChangeEvent event) throws CoreException {
		IResourceDelta d = event.getDelta().findMember(folder.getFullPath());
		if (d != null && (d.getFlags() & IResourceDelta.MARKERS) != 0) {
			return false;
		}

		for (IResource res : folder.members()) {
			if (res instanceof IFolder) {
				IResourceDelta d2 = event.getDelta().findMember(res.getFullPath());
				if (d2 != null) {
					if (d2.getKind() != IResourceDelta.NO_CHANGE) {
						return checkSourceFolderChanges((IFolder) res, event);
					}
				}
			} else {
				IResourceDelta delta = event.getDelta().findMember(res.getFullPath());
				if (delta != null) {
					if ((delta.getFlags() & IResourceDelta.CONTENT) != 0 || delta.getKind() == IResourceDelta.ADDED) {
						return true;
					} else {
						return false;
					}
				}
			}
		}
		return true;
	}

	private void checkBuildFolder(final IFolder folder, final IResourceChangeEvent event) {
		LongRunningWrapper.getRunner(new LongRunningMethod<Boolean>() {
			@Override
			public Boolean execute(IMonitor workMonitor) throws Exception {
				checkBuildFolder(folder);
				return true;
			}

			private void checkBuildFolder(final IFolder folder) throws CoreException {
				if (folder.isAccessible()) {
					for (IResource res : folder.members()) {
						if (res instanceof IFolder) {
							checkBuildFolder((IFolder) res);
						} else if (res instanceof IFile) {
							final IResourceDelta delta = event.getDelta().findMember(res.getFullPath());
							if (delta != null) {
								composerExtension.postCompile(delta, (IFile) res);
							}
						}
					}
				}
			}
		}, REFRESH_COLLABORATION_VIEW).schedule();
	}

	public List<IFile> getAllConfigurations() {
		List<IFile> configs = new ArrayList<IFile>();
		if (!configFolder.isAccessible())
			return configs;
		try {
			for (IResource res : configFolder.members()) {
				if (!(res instanceof IFile))
					continue;
				if (LOGGER.getConfigurationExtensions().contains(res.getFileExtension()))
					configs.add((IFile) res);
			}
		} catch (CoreException e) {
			LOGGER.logError(e);
		}
		return configs;
	}

	private boolean checkModelChange(IResourceDelta delta) {
		if (delta == null || (delta.getFlags() & IResourceDelta.CONTENT) == 0)
			return false;

		Job job = new Job(LOAD_MODEL) {
			protected IStatus run(IProgressMonitor monitor) {
				if (loadModel()) {
					final IComposerExtensionClass composerExtension = getComposer();
					if (composerExtension.isInitialized()) {
						composerExtension.postModelChanged();
						if (!configurationUpdate) {
							checkConfigurations(getAllConfigurations());
						}
						checkFeatureCoverage();
						return Status.OK_STATUS;
					}
				}
				return Status.CANCEL_STATUS;
			}
		};
		job.setPriority(Job.INTERACTIVE);
		job.schedule();
		return true;
	}

	private void checkConfigurations(final List<IFile> files) {
		if (files == null || files.isEmpty()) {
			return;
		}

		LongRunningMethod<Boolean> job = new LongRunningMethod<Boolean>() {
			@Override
			public Boolean execute(IMonitor workMonitor) throws Exception {
				workMonitor.setRemainingWork(2);
				final Configuration config = new Configuration(featureModelManager.getObject(), false, false);
				final FileHandler<Configuration> reader = new FileHandler<>(config);
				try {
					IMonitor subTask = workMonitor.subTask(1);
					subTask.setTaskName(DELETE_CONFIGURATION_MARKERS);
					subTask.setRemainingWork(files.size());
					for (IFile file : files) {
						deleteConfigurationMarkers(file, IResource.DEPTH_ZERO);
						subTask.step();
					}
					subTask.done();
					subTask = workMonitor.subTask(1);
					subTask.setRemainingWork(files.size());
					// check validity
					for (IFile file : files) {
						subTask.setTaskName(CHECK_VALIDITY_OF + " - " + file.getName());
						reader.read(Paths.get(file.getLocationURI()), ConfigurationManager.getFormat(file.getName()));
						if (!config.isValid()) {
							String name = file.getName();
							name = name.substring(0, name.lastIndexOf('.'));
							String message = CONFIGURATION_ + name + IS_INVALID;
							createConfigurationMarker(file, message, 0, IMarker.SEVERITY_ERROR);

						}
						// create warnings (e.g., for features that are not available anymore)
						for (Problem warning : reader.getLastProblems()) {
							createConfigurationMarker(file, warning.getMessage(), warning.getLine(), IMarker.SEVERITY_WARNING);
						}
						subTask.step();
					}
					subTask.done();
				} catch (OutOfMemoryError e) {
					LOGGER.logError(e);
					return false;
				} finally {
					workMonitor.done();
				}
				return true;
			}
		};
		LongRunningWrapper.getRunner(job, CHECKING_CONFIGURATIONS).schedule();
	}

	/**
	 * Checks if any concrete feature is used in at least one configuration.
	 */
	// should also be called if a configuration file was removed
	private void checkFeatureCoverage() {
		configurationChecker.cancel();
		configurationChecker.schedule();
	}

	public Collection<String> getFalseOptionalConfigurationFeatures() {
		return getFalseOptionalConfigurationFeatures(getSelectionMatrix(), (List<String>) getOptionalConcreteFeatures());
	}

	public Collection<String> getFalseOptionalConfigurationFeatures(boolean[][] selections, final List<String> concreteFeatures) {
		return checkValidSelections(selections, false, concreteFeatures);
	}

	public Collection<String> getUnusedConfigurationFeatures() {
		return getUnusedConfigurationFeatures(getSelectionMatrix(), (List<String>) getOptionalConcreteFeatures());
	}

	public Collection<String> getUnusedConfigurationFeatures(boolean[][] selections, final List<String> concreteFeatures) {
		return checkValidSelections(selections, true, concreteFeatures);
	}

	private List<String> checkValidSelections(boolean[][] selections, boolean selectionState, final List<String> concreteFeatures) {
		if (selections.length == 0) {
			return Collections.emptyList();
		}
		final List<String> falseOptionalFeatures = new LinkedList<String>();
		for (int column = 0; column < concreteFeatures.size(); column++) {
			boolean invalid = true;
			for (int conf = 0; conf < selections.length; conf++) {
				if (selections[conf][column] == selectionState) {
					invalid = false;
					break;
				}
			}
			if (invalid) {
				falseOptionalFeatures.add(concreteFeatures.get(column));
			}
		}
		return falseOptionalFeatures;
	}

	private boolean[][] getSelectionMatrix() {
		return getSelectionMatrix(getOptionalConcreteFeatures());
	}

	private boolean[][] getSelectionMatrix(final Collection<String> concreteFeatures) {
		final List<IFile> configurations = getAllConfigurations();

		final boolean[][] selections = new boolean[configurations.size()][concreteFeatures.size()];
		final Configuration configuration = new Configuration(featureModelManager.getObject(), Configuration.PARAM_IGNOREABSTRACT);
		final FileHandler<Configuration> reader = new FileHandler<>(configuration);

		int row = 0;
		for (IFile file : configurations) {
			final boolean[] currentRow = selections[row++];
			try {
				reader.read(Paths.get(file.getLocationURI()), ConfigurationManager.getFormat(file.getName()));
			} catch (Exception e) {
				FMCorePlugin.getDefault().logError(e);
			}

			int column = 0;
			for (String feature : concreteFeatures) {
				final SelectableFeature selectablefeature = configuration.getSelectablefeature(feature);
				if (selectablefeature != null) {
					currentRow[column] = selectablefeature.getSelection() == Selection.SELECTED;
				}
				column++;
			}
		}
		return selections;
	}

	private Collection<String> getOptionalConcreteFeatures() {
		final IFeatureModel featureModel = featureModelManager.getObject();
		final Collection<String> concreteFeatures = FeatureUtils.extractConcreteFeaturesAsStringList(featureModel);
		List<List<IFeature>> deadCoreList = featureModel.getAnalyser().analyzeFeatures();
		for (final IFeature feature : deadCoreList.get(0)) {
			concreteFeatures.remove(feature.getName());
		}
		for (final IFeature feature : deadCoreList.get(1)) {
			concreteFeatures.remove(feature.getName());
		}
		return concreteFeatures;
	}

	public IComposerExtensionClass getComposer() {
		if (composerExtension == null) {
			String compositionToolID = getComposerID();
			if (compositionToolID == null)
				return null;

			final ComposerExtensionManager composerManagerInstance = ComposerExtensionManager.getInstance();
			composerExtension = composerManagerInstance.getComposerById(this, compositionToolID);
			if (composerExtension != null) {
				((ComposerExtensionClass) composerExtension).initialize(this);
			} else {
				CorePlugin.getDefault().logError(new Exception(NO_COMPOSER_COULD_BE_CREATED_FOR_ID + compositionToolID));
			}
		}
		return composerExtension;
	}

	public String getProjectConfigurationPath() {
		try {
			String path = project.getPersistentProperty(configFolderConfigID);
			if (path != null && !path.isEmpty())
				return path;

			path = getPath(CONFIGS_ARGUMENT);
			if (path != null && !path.isEmpty())
				return path;
		} catch (Exception e) {
			LOGGER.logError(e);
		}
		return DEFAULT_CONFIGS_PATH;
	}

	public String getProjectBuildPath() {
		try {
			String path = project.getPersistentProperty(buildFolderConfigID);
			if (path != null && !path.isEmpty())
				return path;

			path = getPath(BUILD_ARGUMENT);
			if (path != null && !path.isEmpty())
				return path;
		} catch (Exception e) {
			LOGGER.logError(e);
		}
		return DEFAULT_BUILD_PATH;
	}

	public String getProjectSourcePath() {
		try {
			String path = project.getPersistentProperty(sourceFolderConfigID);
			if (path != null && !path.isEmpty())
				return path;

			path = getPath(SOURCE_ARGUMENT);
			if (path != null && !path.isEmpty())
				return path;
		} catch (Exception e) {
			LOGGER.logError(e);
		}
		return DEFAULT_SOURCE_PATH;
	}

	private String getPath(String argument) {
		try {
			for (ICommand command : project.getDescription().getBuildSpec()) {
				if (isFIDEBuilder(command)) {
					return command.getArguments().get(argument);
				}
			}
		} catch (CoreException e) {
			LOGGER.logError(e);
		}
		return null;
	}

	private boolean isFIDEBuilder(ICommand command) {
		return command.getBuilderName().equals(ExtensibleFeatureProjectBuilder.BUILDER_ID)
				|| command.getBuilderName().equals("de.ovgu.featureide.core.mpl.MSPLBuilder");
	}

	public String getComposerID() {
		try {
			String id = project.getPersistentProperty(composerConfigID);
			if (id != null) {
				return id;
			}

			for (ICommand command : project.getDescription().getBuildSpec()) {
				if (isFIDEBuilder(command)) {
					id = command.getArguments().get(ExtensibleFeatureProjectBuilder.COMPOSER_KEY);
					if (id != null) {
						return id;
					}
				}
			}

		} catch (CoreException e) {
			LOGGER.logError(e);
		}
		return null;
	}

	public void setPaths(String feature, String src, String configuration) {
		try {
			IProjectDescription description = project.getDescription();

			ICommand[] commands = description.getBuildSpec();
			for (ICommand command : commands) {
				if (isFIDEBuilder(command) || command.getBuilderName().equals("org.eclipse.ui.externaltools.ExternalToolBuilder")) {
					Map<String, String> args = command.getArguments();
					args.put(SOURCE_ARGUMENT, feature);
					args.put(BUILD_ARGUMENT, src);
					args.put(CONFIGS_ARGUMENT, configuration);
					project.setPersistentProperty(IFeatureProject.buildFolderConfigID, src);
					project.setPersistentProperty(IFeatureProject.configFolderConfigID, configuration);
					project.setPersistentProperty(IFeatureProject.sourceFolderConfigID, feature);
					command.setArguments(args);
				}
			}
			description.setBuildSpec(commands);
			project.setDescription(description, null);
		} catch (CoreException e) {
			LOGGER.logError(e);
		}
	}

	public void setComposerID(String composerID) {
		try {
			project.setPersistentProperty(composerConfigID, composerID);
			IProjectDescription description = project.getDescription();

			LinkedList<ICommand> newCommandList = new LinkedList<ICommand>();
			boolean added = false;
			for (ICommand command : description.getBuildSpec()) {
				if (isFIDEBuilder(command)) {
					if (!added) {
						Map<String, String> args = command.getArguments();
						args.put(ExtensibleFeatureProjectBuilder.COMPOSER_KEY, composerID);
						command.setArguments(args);
						// Composer must be the first command
						newCommandList.addFirst(command);
						added = true;
					}
				} else {
					newCommandList.add(command);
				}
			}
			ICommand[] newCommandArray = new ICommand[newCommandList.size()];
			int i = 0;
			for (ICommand c : newCommandList) {
				newCommandArray[i] = c;
				i++;
			}
			description.setBuildSpec(newCommandArray);
			project.setDescription(description, null);
		} catch (CoreException ex) {
		}
	}

	public void setAdditionalJavaClassPath(String[] paths) {
		StringBuilder builder = new StringBuilder();
		if (paths.length > 0)
			builder.append(paths[0]);
		for (int i = 1; i < paths.length; ++i) {
			builder.append(';');
			builder.append(paths[i]);
		}
		try {
			project.setPersistentProperty(javaClassPathID, builder.toString());
		} catch (CoreException ex) {
		}
	}

	public void setFSTModel(FSTModel model) {
		fstModel = model;
	}

	public boolean buildRelevantChanges() {
		return buildRelevantChanges;
	}

	public void built() {
		buildRelevantChanges = false;
	}

	// TODO move to configuration reader
	public List<String> readFeaturesfromConfigurationFile(File file) {
		if (!file.exists()) {
			return new ArrayList<String>();
		}
		Scanner scanner = null;
		try {
			ArrayList<String> list;
			scanner = new Scanner(file, "UTF-8");
			if (scanner.hasNext()) {
				list = new ArrayList<String>();
				while (scanner.hasNext()) {
					list.add(scanner.next());
				}
				return list;
			} else {
				return new ArrayList<String>();
			}
		} catch (FileNotFoundException e) {
			LOGGER.logError(e);
		} finally {
			if (scanner != null) {
				scanner.close();
			}
		}
		return new ArrayList<String>();
	}

	public String getContractComposition() {
		String contractComposition = null;
		ProjectScope ps = new ProjectScope(project);
		IEclipsePreferences prefs = ps.getNode("de.ovgu.featureide.core");
		contractComposition = prefs.get("contract", DEFAULT_CONTRACT_COMPOSITION);
		return contractComposition;
	}

	public void setContractComposition(String contractComposition) {
		try {
			ProjectScope ps = new ProjectScope(project);
			IEclipsePreferences prefs = ps.getNode("de.ovgu.featureide.core");
			prefs.put("contract", contractComposition);
			prefs.flush();
		} catch (BackingStoreException e) {
			LOGGER.logError(e);
		}
	}

	private static final QualifiedName META_PRODUCT_GENERATION = new QualifiedName(FeatureProject.class.getName() + "#MetaProductGeneration",
			FeatureProject.class.getName() + "#MetaProductGeneration");

	public String getMetaProductGeneration() {
		String metaProductGeneration = null;
		try {
			metaProductGeneration = project.getPersistentProperty(META_PRODUCT_GENERATION);
		} catch (CoreException e) {
			LOGGER.logError(e);
		}
		if (metaProductGeneration == null) {
			return META_THEOREM_PROVING;
		}
		return metaProductGeneration;
	}

	public void setMetaProductGeneration(String metaProductGeneration) {
		try {
			project.setPersistentProperty(META_PRODUCT_GENERATION, metaProductGeneration);
		} catch (CoreException e) {
			LOGGER.logError(e);
		}
	}

	@Override
	public String toString() {
		return project.getName();
	}

	public String getCompositionMechanism() {
		String compositionMechanism = null;
		try {
			compositionMechanism = project.getPersistentProperty(compositionMechanismConfigID);
		} catch (CoreException e) {
			LOGGER.logError(e);
		}
		if (compositionMechanism == null) {
			if (getComposer().getCompositionMechanisms().length != 0) {
				compositionMechanism = getComposer().getCompositionMechanisms()[0];
			} else {
				compositionMechanism = "";
			}
		}
		return compositionMechanism;
	}

	public void setCompositionMechanism(String compositionMechanism) {
		try {
			project.setPersistentProperty(compositionMechanismConfigID, compositionMechanism);
		} catch (CoreException e) {
			LOGGER.logError(e);
		}
	}

	@Override
	public IFile getInternalConfigurationFile() {
		return getInternalConfigurationFile(currentConfiguration);
	}

	@Override
	public IFile getInternalConfigurationFile(IFile configurationFile) {
		String fileName = configurationFile.getName();

		final String extension = configurationFile.getFileExtension();
		if (extension != null) {
			fileName = "." + fileName.substring(0, fileName.length() - (extension.length())) + FeatureIDEFormat.EXTENSION;
		} else {
			fileName = "." + fileName + "." + FeatureIDEFormat.EXTENSION;
		}
		IFile internalFile = configurationFile.getParent().getFile(Path.fromOSString(fileName));

		return (internalFile.isAccessible()) ? internalFile : null;
	}

	@Override
	public FeatureModelManager getFeatureModelManager() {
		return featureModelManager;
	}
}
