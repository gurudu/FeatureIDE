package de.ovgu.featureide.visualisation;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.util.ArrayList;
import java.util.List;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.swt.SWT;
import org.eclipse.swt.SWTError;
import org.eclipse.swt.browser.Browser;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.FeatureDependencies;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.ui.handlers.base.ASelectionHandler;

/**
 * Show Feature Relations Graph
 * 
 * @author Hari Kumar Gurudu
 */
public class ShowFeatureRelationsGraphCommandHandler extends ASelectionHandler {
	public static int fpgInteractions = 0;
	 static Thread thread;
	public static String featureC = "";
	public static IFeatureProject fProject;
	@Override
	protected void singleAction(Object element) {
		IProject project = null;
		 
		if (!(element instanceof IProject)) {
			if (element instanceof IAdaptable) {
				project = ((IAdaptable) element).getAdapter(IProject.class);
			}
		} else {
			project = (IProject) element;
		}
		final IFeatureProject featureProject = CorePlugin.getFeatureProject(project);
		
		Shell shell = new Shell(Display.findDisplay(ShowFeatureRelationsGraphCommandHandler.thread));
		shell.setText("Select feature");
		shell.setSize(400, 200);
		shell.setLayout(new FillLayout(SWT.VERTICAL));
		final org.eclipse.swt.widgets.List list = new org.eclipse.swt.widgets.List(shell, SWT.BORDER | SWT.V_SCROLL);

		List<String> featureList = ConfigAnalysisUtils.computeWidgetFeatures(featureProject);
		for (String f : featureList) {
			list.add(f);
		}
        
		list.addSelectionListener(new SelectionListener() {
			
			public void widgetSelected(SelectionEvent event) {
				int count = 0;
				int[] selections = list.getSelectionIndices();
				try {
					 count = showFrog(featureProject, list.getItem(selections[0]));
					
					 PrintWriter writer = new PrintWriter("FPGInteractions.txt", "UTF-8");
					 writer.println(count);
					 writer.close();
					 System.out.println(" Number of Feature properties graph interactions = "+count);
				} catch (CoreException e) {
					e.printStackTrace();
				} catch (FileNotFoundException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				} catch (UnsupportedEncodingException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}

			public void widgetDefaultSelected(SelectionEvent event) {

			}
		});
		
		shell.open();
        
	}

	/**
	 * Show frog
	 * 
	 * @param featureProject
	 * @param featureCenter
	 * @return 
	 * @throws CoreException 
	 */
	
	public static int showFrog(IFeatureProject featureProject, String featureCenter) throws CoreException {

		 //count interactions
		fpgInteractions++;
		 featureC = featureCenter;
		fProject = featureProject;
		//NonFunctionalPropertyGraphCommandHandler.showNFPGraph(featureProject, featureCenter);
		Object[] FeaturePredicts = ConfigAnalysisUtils.computeFeaturePredictions(featureProject,featureCenter);
		
		List<String> relatedFeatures = (List<String>)FeaturePredicts[0];
		List<String> relatedFeatureValues = (List<String>)FeaturePredicts[1];
		List<String> formalizedRequires = (List<String>)FeaturePredicts[2];
		List<String> formalizedExcludes = (List<String>)FeaturePredicts[3];
		
		Object[] NFPCenter = NFProps.computeNFP(featureProject,featureCenter);
		List<String> NFP = (List<String>)NFPCenter[0];
		List<String> NFP_VALUES = (List<String>)NFPCenter[1];
		int quantityCount = (int) NFPCenter[2];		
		NFProps.computeQuantity(featureProject);
		// Here we create the text with the data to be inserted in the html page (sample data)
	    //CENTRAL_FEATURE = "t13";
		//quantityCount = "1";
		//FEATURE_NAMES = ["World","test"];
		// PREDICTIONS = ["0.6","0.1"];
		// FORMALIZED_REQUIRES = ["HelloWorld","Hello","test22"];
		// FORMALIZED_EXCLUDES = ["t15","t16","test"];
		// NFP = ["cost","security"];
		// NFP_VALUES = ["0.425","0.5"];
	
		StringBuffer data = new StringBuffer(" CENTRAL_FEATURE = \"");
		data.append(featureCenter);
		data.append("\";\n quantityCount = \"");
		data.append(quantityCount);
		data.append("\";\n FEATURE_NAMES = [");
		 if(relatedFeatures.size()>0){
			for (String f : relatedFeatures) {
					data.append("\"");
					data.append(f);
					data.append("\",");
				
			}
			data.setLength(data.length() - 1); // remove last comma
		 }
		data.append("];\n NFP = [");
		 if(NFP.size()>0){
				for (String f : NFP) {
					data.append("\"");
					data.append(f);
					data.append("\",");
				}
	    data.setLength(data.length() - 1); // remove last comma
		}
	   data.append("];\n NFP_VALUES = [");
	    if(NFP_VALUES.size()>0){	
			for (String f : NFP_VALUES) {
					data.append("\"");
					data.append(f);
					data.append("\",");			
			}
			data.setLength(data.length() - 1); // remove last comma	 
	    }
	   data.append("];\n PREDICTIONS = [");
	    if(relatedFeatureValues.size()>0){
			for (String f : relatedFeatureValues) {
				    data.append("\"");
					data.append(f);
					data.append("\",");
			}
	      data.setLength(data.length() - 1); // remove last comma
	    }
		boolean atLeastOne = false;
		data.append("];\n FORMALIZED_REQUIRES = [");
		for (String f : formalizedRequires) {
			data.append("\"");
			data.append(f);
			data.append("\",");
			atLeastOne = true;
		}
		if (atLeastOne) {
			data.setLength(data.length() - 1); // remove last comma
		}
		atLeastOne = false;
		data.append("];\n FORMALIZED_EXCLUDES = [");
		for (String f : formalizedExcludes) {
			data.append("\"");
			data.append(f);
			data.append("\",");
			atLeastOne = true;
		}
		if (atLeastOne) {
			data.setLength(data.length() - 1); // remove last comma
		}
		atLeastOne = false;
		data.append("];\n");
		File fi = Utils.getFileFromPlugin("de.ovgu.featureide.visualisation", "template/featureRelations/page.html");
		String html = Utils.getStringOfFile(fi);
		html = html.replaceFirst("// DATA_HERE", data.toString());
       System.out.println("data id "+data.toString());
		// Open the browser
      
		Shell shell = new Shell(Display.getCurrent());
		shell.setLayout(new FillLayout());
		shell.setSize(1300, 1200);
		shell.setText("Feature relations graph: " + featureCenter);
		Browser browser;
		try {
			browser = new Browser(shell, SWT.NONE);
		} catch (SWTError e) {
			System.out.println("Could not instantiate Browser: " + e.getMessage());
			return fpgInteractions;
		}
		browser.setText(html);
		shell.open();
	
		return fpgInteractions;
	}

}
