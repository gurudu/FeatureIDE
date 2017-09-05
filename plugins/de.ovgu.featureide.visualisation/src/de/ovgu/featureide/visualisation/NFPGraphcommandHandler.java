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
import de.ovgu.featureide.fm.ui.handlers.base.ASelectionHandler;

public class NonFunctionalPropertyGraphCommandHandler extends ASelectionHandler {
	
	public static int NFPInteractions = 0;
	//static Thread thread;
	public static Thread thread;
	public static String featureCenter =  ShowFeatureRelationsGraphCommandHandler.featureC;;
	public IFeatureProject featureProject = ShowFeatureRelationsGraphCommandHandler.fProject;
	
	@Override
	public void singleAction(Object element) {
	    //if(featureProject != null){
		Shell shell22 = new Shell(Display.findDisplay(NonFunctionalPropertyGraphCommandHandler.thread));
	   
		shell22.setText("Select a NFP");
		shell22.setSize(400, 200);
		shell22.setLayout(new FillLayout(SWT.VERTICAL));
	   
		final org.eclipse.swt.widgets.List list11 = new org.eclipse.swt.widgets.List(shell22, SWT.BORDER | SWT.V_SCROLL);
	   
		List<String> featureList = new ArrayList<>();
		for(String s : NFProps.names){
			featureList.add(s);
		}
		System.out.println("Feature list is "+featureList);
		for (String f : featureList) {
			list11.add(f);
		}
		
		list11.addSelectionListener(new SelectionListener() {
			
			public void widgetSelected(SelectionEvent event) {
				int count = 0;
				int[] selections = list11.getSelectionIndices();
				try {
					count = NonFunctionalPropertyGraphCommandHandler.showNFPGraph(featureProject,list11.getItem(selections[0]));
					 PrintWriter writer = new PrintWriter("FPGInteractions.txt", "UTF-8");
					 writer.println(count);
					 writer.close();
					 System.out.println(" Number of Non-Functional property's graph interactions = "+count);
				} catch (FileNotFoundException e) {
					e.printStackTrace();
				} catch (UnsupportedEncodingException e) {
					e.printStackTrace();
				} catch (CoreException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}

			public void widgetDefaultSelected(SelectionEvent event) {

			}
		});

		shell22.open();
	   //}	
	}
	
	public static int showNFPGraph(IFeatureProject featureProject,String nfpCenter) throws CoreException {
	
		NFPInteractions++;
		try{
		List<Double> featuresNFPValues11 = NFProps.NFPGraphFeatures(featureProject,featureCenter,nfpCenter);
		List<String> featuresNFPValues = new ArrayList<String>();
		for (Double d : featuresNFPValues11) {
		    // Apply formatting to the string if necessary
			featuresNFPValues.add(d.toString());
		}
		
		Object[] featurePredicts = ConfigAnalysisUtils.computeFeaturePredictions(featureProject,featureCenter);
		List<String> relatedFeatures = (List<String>)featurePredicts[0];
		relatedFeatures.add(featureCenter);
		//String featureCenter = "time";
		StringBuffer data = new StringBuffer(" CENTRAL_NFP = \"");
		data.append(nfpCenter);
		data.append("\";\n FEATURE_NAMES11 = [");
		 if(relatedFeatures.size()>0){
			for (String f : relatedFeatures) {
					data.append("\"");
					data.append(f);
					data.append("\",");
				
			}
			data.setLength(data.length() - 1); // remove last comma
		 }
		 data.append("];\n PREDICTIONS11 = [");
		    if(featuresNFPValues.size()>0){
				for (String f : featuresNFPValues) {
					    data.append("\"");
						data.append(f);
						data.append("\",");
				}
		      data.setLength(data.length() - 1); // remove last comma
		    }
		    data.append("];\n");
		
		File fi = Utils.getFileFromPlugin("de.ovgu.featureide.visualisation", "template/NFP/NFP.html");
		String html = Utils.getStringOfFile(fi);
		html = html.replaceFirst("// DATA_HERE", data.toString());
	// Open the browser
		System.out.println("nfp data is"+data);
		Shell shell = new Shell(Display.getCurrent());
		shell.setLayout(new FillLayout());
		shell.setSize(900, 800);
		
		shell.setText("Non-functional property's graph: " + featureCenter );
		Browser browser;
		try {
			browser = new Browser(shell, SWT.NONE);
		} catch (SWTError e) {
			System.out.println("Could not instantiate Browser: " + e.getMessage());
			return NFPInteractions;
		}
		browser.setText(html);
		shell.open();
		}catch(NullPointerException npe){
			npe.printStackTrace();
		}
	
		return NFPInteractions;
	}
}
