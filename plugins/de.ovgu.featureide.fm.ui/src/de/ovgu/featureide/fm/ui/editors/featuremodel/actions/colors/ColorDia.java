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
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions.colors;

import static de.ovgu.featureide.fm.core.localization.StringTable.CYAN;
import static de.ovgu.featureide.fm.core.localization.StringTable.DARKGREEN;
import static de.ovgu.featureide.fm.core.localization.StringTable.LIGHTGREEN;
import static de.ovgu.featureide.fm.core.localization.StringTable.LIGHTGREY;
import static de.ovgu.featureide.fm.core.localization.StringTable.MAGENTA;
import static de.ovgu.featureide.fm.core.localization.StringTable.ORANGE;
import static de.ovgu.featureide.fm.core.localization.StringTable.PINK;
import static de.ovgu.featureide.fm.core.localization.StringTable.PURPLE;
import static de.ovgu.featureide.fm.core.localization.StringTable.RED;
import static de.ovgu.featureide.fm.core.localization.StringTable.SELECTED_FEATURE;
import static de.ovgu.featureide.fm.core.localization.StringTable.SELECTED_FEATURE_ALL_CHILDREN;
import static de.ovgu.featureide.fm.core.localization.StringTable.SELECTED_FEATURE_DIRECT_CHILDREN;
import static de.ovgu.featureide.fm.core.localization.StringTable.SELECTED_FEATURE_SIBLINGS;
import static de.ovgu.featureide.fm.core.localization.StringTable.YELLOW;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableItem;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.ProfileManager;
import de.ovgu.featureide.fm.core.ProfileManager.Project.Profile;
import de.ovgu.featureide.fm.core.annotation.ColorPalette;
import de.ovgu.featureide.fm.ui.PlugInProfileSerializer;

public class ColorDia extends Dialog {

	protected List<Feature> featurelist;
	protected ArrayList<Feature> featurelistbuffer = new ArrayList<Feature>();
	protected int colorID = -1;
	private boolean actionChecked = false;
	private boolean colorChecked = false;

	/**
	 * @param parentShell
	 * @param featurelist
	 */
	protected ColorDia(Shell parentShell, List<Feature> featurelist) {
		super(parentShell);
		this.featurelist = featurelist;
		setShellStyle(SWT.DIALOG_TRIM | SWT.MIN | SWT.RESIZE);

	}

	protected void configureShell(Shell newShell) {
		newShell.setMinimumSize(new Point(500, 500));
		super.configureShell(newShell);
		newShell.setText("Color Dialog");
	}

	protected Point getInitialSize() {
		return new Point(500, 500);
	}

	protected Control createDialogArea(Composite parent) {

		final Composite container = (Composite) super.createDialogArea(parent);
		container.setBackground(new Color(parent.getDisplay(), 255, 255, 255));
		GridLayout gridLayout = (GridLayout) container.getLayout();
		gridLayout.numColumns = 2;

		GridData gridData = new GridData();
		gridData.verticalAlignment = GridData.BEGINNING;
		gridData.horizontalAlignment = GridData.FILL;

		Label actionLabel = new Label(container, SWT.NONE);
		actionLabel.setLayoutData(gridData);
		actionLabel.setBackground(new Color(null, 255, 255, 255));
		actionLabel.setText("Choose action: ");

		final Combo actionDropDownMenu = new Combo(container, SWT.DROP_DOWN | SWT.READ_ONLY);
		final String[] actionDropDownItems = { SELECTED_FEATURE, SELECTED_FEATURE_DIRECT_CHILDREN, SELECTED_FEATURE_ALL_CHILDREN, SELECTED_FEATURE_SIBLINGS };
		actionDropDownMenu.setLayoutData(gridData);
		actionDropDownMenu.setItems(actionDropDownItems);

		Label chooseColorLabel = new Label(container, SWT.NONE);
		chooseColorLabel.setLayoutData(gridData);
		chooseColorLabel.setBackground(new Color(null, 255, 255, 255));
		chooseColorLabel.setText("Choose color: ");

		final Combo colorDropDownMenu = new Combo(container, SWT.DROP_DOWN | SWT.READ_ONLY);
		final String[] colorDropDownItems = { RED, ORANGE, YELLOW, DARKGREEN, LIGHTGREEN, CYAN, LIGHTGREY, PURPLE, MAGENTA, PINK };
		colorDropDownMenu.setLayoutData(gridData);
		colorDropDownMenu.setItems(colorDropDownItems);

		Label featureLabel = new Label(container, SWT.NONE);
		featureLabel.setLayoutData(gridData);
		featureLabel.setBackground(new Color(null, 255, 255, 255));
		featureLabel.setText("Features: ");

		gridData = new GridData();
		gridData.verticalAlignment = GridData.FILL;
		gridData.horizontalAlignment = GridData.FILL;
		gridData.grabExcessHorizontalSpace = true;
		gridData.grabExcessVerticalSpace = true;

		final Table featureTable = new Table(container, SWT.BORDER | SWT.NO_FOCUS | SWT.HIDE_SELECTION);
		featureTable.setLayoutData(gridData);

		SelectionListener colorSelectionListener = new SelectionListener() {
			public void widgetSelected(SelectionEvent event) {
				Combo colorListener = ((Combo) event.widget);

				for (int i = 0; i < colorDropDownItems.length; i++) {
					if (colorListener.getText().equals(colorDropDownItems[i])) {
						colorChecked = true;
						colorID = i;
						for (int j = 0; j < featurelistbuffer.size(); j++) {
							featureTable.getItem(j).setBackground(new Color(null, ColorPalette.getRGB(colorID, 0.4f)));
						}
					}
				}
				if (actionChecked && colorChecked) {
					ColorDia.this.getButton(OK).setEnabled(true);
				}
			}

			public void widgetDefaultSelected(SelectionEvent e) {
			};
		};
		colorDropDownMenu.addSelectionListener(colorSelectionListener);

		SelectionListener actionSelectionListener = new SelectionListener() {
			public void widgetSelected(SelectionEvent event) {
				Combo actionListener = ((Combo) event.widget);

				// Selected
				if (actionListener.getText().equals(actionDropDownItems[0])) {
					featurelistbuffer.clear();
					for (int i = 0; i < featurelist.size(); i++) {
						featurelistbuffer.add(featurelist.get(i));
					}

					actionChecked = true;
					featureTable.redraw();
					featureTable.removeAll();

					for (int i = 0; i < featurelistbuffer.size(); i++) {
						TableItem item = new TableItem(featureTable, SWT.NONE);
						item.setText(featurelistbuffer.get(i).getName());

						final Feature feature = featurelistbuffer.get(i);
						Profile profile = ProfileManager.getProject(feature.getFeatureModel().xxxGetEclipseProjectPath(),
								PlugInProfileSerializer.FEATURE_PROJECT_SERIALIZER).getActiveProfile();
						if (profile.hasFeatureColor(feature.getName()))
							item.setBackground(new Color(null, ColorPalette.getRGB(ProfileManager.toColorIndex(profile.getColor(feature.getName())), 0.4f)));
					}

				}

				// Selected + direct Children
				if (actionListener.getText().equals(actionDropDownItems[1])) {
					featurelistbuffer.clear();

					for (int i = 0; i < featurelist.size(); i++) {
						featurelistbuffer.add(featurelist.get(i));
					}

					for (int j = 0; j < featurelist.size(); j++) {
						for (int k = 0; k < featurelistbuffer.get(j).getChildren().size(); k++) {
							if (!featurelistbuffer.contains(featurelistbuffer.get(j).getChildren().get(k)))
								featurelistbuffer.add(featurelistbuffer.get(j).getChildren().get(k));
						}
					}

					actionChecked = true;
					featureTable.redraw();
					featureTable.removeAll();

					for (int i = 0; i < featurelistbuffer.size(); i++) {
						TableItem item = new TableItem(featureTable, SWT.NONE);
						item.setText(featurelistbuffer.get(i).getName());

						final Feature feature = featurelistbuffer.get(i);
						Profile profile = ProfileManager.getProject(feature.getFeatureModel().xxxGetEclipseProjectPath(),
								PlugInProfileSerializer.FEATURE_PROJECT_SERIALIZER).getActiveProfile();
						if (profile.hasFeatureColor(feature.getName()))
							item.setBackground(new Color(null, ColorPalette.getRGB(ProfileManager.toColorIndex(profile.getColor(feature.getName())), 0.4f)));
					}
				}

				// Selected + all Children
				if (actionListener.getText().equals(actionDropDownItems[2])) {
					featurelistbuffer.clear();

					for (int i = 0; i < featurelist.size(); i++) {
						featurelistbuffer.add(featurelist.get(i));
					}

					for (int j = 0; j < featurelistbuffer.size(); j++) {
						for (int k = 0; k < featurelistbuffer.get(j).getChildren().size(); k++) {
							if (!featurelistbuffer.contains(featurelistbuffer.get(j).getChildren().get(k)))
								featurelistbuffer.add(featurelistbuffer.get(j).getChildren().get(k));
						}
					}

					actionChecked = true;
					featureTable.redraw();
					featureTable.removeAll();

					for (int i = 0; i < featurelistbuffer.size(); i++) {
						TableItem item = new TableItem(featureTable, SWT.NONE);
						item.setText(featurelistbuffer.get(i).getName());

						final Feature feature = featurelistbuffer.get(i);
						Profile profile = ProfileManager.getProject(feature.getFeatureModel().xxxGetEclipseProjectPath(),
								PlugInProfileSerializer.FEATURE_PROJECT_SERIALIZER).getActiveProfile();
						if (profile.hasFeatureColor(feature.getName()))
							item.setBackground(new Color(null, ColorPalette.getRGB(ProfileManager.toColorIndex(profile.getColor(feature.getName())), 0.4f)));
					}
				}

				// Selected + Siblings
				if (actionListener.getText().equals(actionDropDownItems[3])) {
					featurelistbuffer.clear();

					for (int i = 0; i < featurelist.size(); i++) {
						featurelistbuffer.add(featurelist.get(i));
					}

					for (int j = 0; j < featurelistbuffer.size(); j++) {
						if (!featurelistbuffer.get(j).isRoot()) {
							for (int k = 0; k < featurelistbuffer.get(j).getParent().getChildren().size(); k++) {
								if (!featurelistbuffer.contains(featurelistbuffer.get(j).getParent().getChildren().get(k)))
									featurelistbuffer.add(featurelistbuffer.get(j).getParent().getChildren().get(k));
							}
						}
					}

					actionChecked = true;
					featureTable.redraw();
					featureTable.removeAll();

					for (int i = 0; i < featurelistbuffer.size(); i++) {
						TableItem item = new TableItem(featureTable, SWT.NONE);
						item.setText(featurelistbuffer.get(i).getName());

						final Feature feature = featurelistbuffer.get(i);
						Profile profile = ProfileManager.getProject(feature.getFeatureModel().xxxGetEclipseProjectPath(),
								PlugInProfileSerializer.FEATURE_PROJECT_SERIALIZER).getActiveProfile();
						if (profile.hasFeatureColor(feature.getName()))
							item.setBackground(new Color(null, ColorPalette.getRGB(ProfileManager.toColorIndex(profile.getColor(feature.getName())), 0.4f)));
					}
				}
				if (actionChecked && colorChecked) {
					ColorDia.this.getButton(OK).setEnabled(true);
				}
			}

			public void widgetDefaultSelected(SelectionEvent e) {
			};
		};

		actionDropDownMenu.addSelectionListener(actionSelectionListener);

		return parent;

	}

	protected Control createContents(Composite parent) {
		super.createContents(parent);

		getButton(IDialogConstants.OK_ID).setEnabled(false);

		return parent;

	}

	protected void buttonPressed(int buttonId) {

		if (IDialogConstants.OK_ID == buttonId) {

			for (int i = 0; i < featurelistbuffer.size(); i++) {

				// Marcus Fix
				final Feature feature = featurelistbuffer.get(i);
				final FeatureModel model = feature.getFeatureModel();
				ProfileManager.Project project = ProfileManager
						.getProject(model.xxxGetEclipseProjectPath(), PlugInProfileSerializer.FEATURE_PROJECT_SERIALIZER);
				ProfileManager.Project.Profile activeProfile = project.getActiveProfile();
				activeProfile.setFeatureColor(feature.getName(), ProfileManager.getColorFromID(colorID));
				// End Marcus Fix
			}
			okPressed();

		} else if (IDialogConstants.CANCEL_ID == buttonId) {
			cancelPressed();
		}
	}

	protected void okPressed() {
		super.okPressed();
	}

	protected void cancelPressed() {
		super.cancelPressed();
	}
}
