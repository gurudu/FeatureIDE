package de.ovgu.featureide.ui.actions;

import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.internal.ui.packageview.PackageFragmentRootContainer;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.ContributionItem;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITreeSelection;
import org.eclipse.jface.viewers.TreePath;
import org.eclipse.jface.viewers.TreeSelection;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.ui.ISelectionService;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.internal.Workbench;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.ColorschemeTable;
import de.ovgu.featureide.fm.core.FeatureModel;

public class DynamicProfileMenu extends ContributionItem {
	private AddProfileColorSchemeAction addProfileSchemeAction;
	private RenameProfileColorSchemeAction renameProfileSchemeAction;
	private DeleteProfileColorSchemeAction deleteProfileSchemeAction;
	private IFeatureProject myFeatureProject = getCurrentFeatureProject();
	private FeatureModel myFeatureModel = myFeatureProject.getFeatureModel();
	private boolean multipleSelected = isMultipleSelection();

	public DynamicProfileMenu() {

	}

	public DynamicProfileMenu(String id) {
		super(id);
	}

	@Override
	public void fill(Menu menu, int index) {

		//		final IFeatureProject res = (IFeatureProject) SelectionWrapper.init((IStructuredSelection)PlatformUI.getWorkbench().getActiveWorkbenchWindow().getSelectionService().getSelection(), IResource.class);
		//			myFeatureModel = res.getFeatureModel();
		//			myFeatureProject = res;
		//

		MenuManager man = new MenuManager("Profile", PlatformUI.getWorkbench().getSharedImages().getImageDescriptor(ISharedImages.IMG_OBJ_ADD), "");
		man.addMenuListener(new IMenuListener() {
			public void menuAboutToShow(IMenuManager m) {

				fillContextMenu(m);
			}
		});

		if (multipleSelected == false) {
			man.fill(menu, index);
		}

		man.setVisible(true);
		createActions();

	}

	private void fillContextMenu(IMenuManager menuMgr) {
		//SetProfileColorSchemeAction setCSAction;
		FeatureModel fm = myFeatureModel;
		ColorschemeTable colorschemeTable = fm.getColorschemeTable();
		List<String> csNames = colorschemeTable.getColorschemeNames();

		int count = 0;
		for (String name : csNames) {
			//SetProfileColorSchemeAction 
			SetProfileColorSchemeAction setCSAction = new SetProfileColorSchemeAction(name, ++count, Action.AS_CHECK_BOX, myFeatureModel);
			if (count == colorschemeTable.getSelectedColorscheme()) {
				setCSAction.setChecked(true);
			}
			menuMgr.add(setCSAction);

		}
		menuMgr.add(new Separator());
		menuMgr.add(addProfileSchemeAction);
		menuMgr.add(renameProfileSchemeAction);
		menuMgr.add(deleteProfileSchemeAction);

		if (colorschemeTable.getSelectedColorschemeName().equals("Default Colorscheme")) {
			renameProfileSchemeAction.setEnabled(false);
			deleteProfileSchemeAction.setEnabled(false);
		}

		menuMgr.setRemoveAllWhenShown(true);
	}

	// create Actions

	private void createActions() {
		addProfileSchemeAction = new AddProfileColorSchemeAction("Add Colorscheme", myFeatureModel, myFeatureProject);
		renameProfileSchemeAction = new RenameProfileColorSchemeAction("Change Name", myFeatureModel, myFeatureProject);
		deleteProfileSchemeAction = new DeleteProfileColorSchemeAction("Delete Colorscheme", myFeatureModel, myFeatureProject);

	}

	private static IStructuredSelection getIStructuredCurrentSelection() {
		ISelectionService selectionService = Workbench.getInstance().getActiveWorkbenchWindow().getSelectionService();

		ISelection selection = selectionService.getSelection();
		return (IStructuredSelection) selection;

	}

	// Mehrfachselektion ausgew�hlt?
	private static boolean isMultipleSelection() {
		boolean multipleSelected = false;
		IStructuredSelection myselection = getIStructuredCurrentSelection();

		if (myselection instanceof ITreeSelection) {
			TreeSelection treeSelection = (TreeSelection) myselection;
			TreePath[] treePaths = treeSelection.getPaths();
			if (treePaths.length > 1) {
				multipleSelected = true;
				return multipleSelected;
			}
		}
		return multipleSelected;

	}

	//	Eclipse get current project selected
	private static IProject getCurrentProject() {
		Object element = getIStructuredCurrentSelection().getFirstElement();

		IProject project = null;

		if (element instanceof IResource) {
			project = ((IResource) element).getProject();
		} else if (element instanceof PackageFragmentRootContainer) {
			IJavaProject jProject = ((PackageFragmentRootContainer) element).getJavaProject();
			project = jProject.getProject();
		} else if (element instanceof IJavaElement) {
			IJavaProject jProject = ((IJavaElement) element).getJavaProject();
			project = jProject.getProject();
		}

		return project;
	}

	public static IFeatureProject getCurrentFeatureProject() {
		IProject project = getCurrentProject();
		IFeatureProject myproject = CorePlugin.getFeatureProject(project);
		return myproject;
	}
}
