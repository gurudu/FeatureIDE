package de.ovgu.featureide.visualisation;

import java.io.IOException;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.ConcurrentModificationException;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Random;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.FeatureDependencies;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.DefaultFormat;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;

/**
 * Configurations Analysis utils
 * 
 * @author Hari Kumar Gurudu
 */
public class ConfigAnalysisUtils {

	public static Object[] computeFeaturePredictions(IFeatureProject featureProject, String featureCenter) throws CoreException{
		
		List<String> PREDICTIONS = new ArrayList<String>();
		List<String> FeatureProps = new ArrayList<String>();
		List<String> FeatureValues = new ArrayList<String>();
		List<String> relatedFeatureValues = new ArrayList<String>();
		Collection<IFile> predicts = new ArrayList<IFile>();
	    IFolder configsFolder = featureProject.getConfigFolder();
	    
		IFeatureModel featureModel = featureProject.getFeatureModel();
		//IFeature fc = featureModel.getFeature(featureCenter);
	    Configuration configuration = new Configuration(featureModel);
		FileHandler.load(Paths.get(featureProject.getCurrentConfiguration().getLocationURI()), configuration, new DefaultFormat());
		Object[] relatedF = getRelatedFeatures(featureProject,featureCenter);
		
		List<String> relatedFeatures = (List<String>) relatedF[0];
		List<String> formalizedRequires = (List<String>) relatedF[1];
		List<String> formalizedExcludes = (List<String>) relatedF[2];
	
		for (IResource res : configsFolder.members()) {
			if (res instanceof IFile) {
				if (((IFile) res).getName().endsWith(".txt")) {
					predicts.add((IFile) res);
				}
			}
		}	
		for (IFile predict : predicts) {
        	try {
				java.io.InputStream is=predict.getContents();
				byte[] b=new byte[is.available()];
				is.read(b);
				is.close();
				String fulltext = new String(b);
				String[] a = fulltext.split("\\r?\\n");
		
				for (String t : a) {
					String[] s1 = t.split(":");
					for (String p : s1) {
						PREDICTIONS.add(p);
					}
				}
				for(int i=0;i<PREDICTIONS.size();i++){
					String b1 = PREDICTIONS.get(i);
					if(i%2==0){
						FeatureProps.add(b1);
					}else{	
						FeatureValues.add(b1);
					}
				}			
			} catch (IOException e) {
				e.printStackTrace();
			} 
        }
	  for(String f: relatedFeatures){	
		for(int i=0; i< FeatureProps.size(); i++){
			if(FeatureProps.get(i).equals(f)){
				relatedFeatureValues.add(FeatureValues.get(i));
			}
		}
	  }
	  return new Object[]{ relatedFeatures,relatedFeatureValues,formalizedRequires,formalizedExcludes };
		
	}
	
	@SuppressWarnings("unchecked")
	public static Object[] getRelatedFeatures(IFeatureProject featureProject,String featureCenter) {
		
		IFeatureModel featureModel = featureProject.getFeatureModel();
		IFeature fc = featureModel.getFeature(featureCenter);
	    Configuration configuration = new Configuration(featureModel);
	    FileHandler.load(Paths.get(featureProject.getCurrentConfiguration().getLocationURI()), configuration, new DefaultFormat());
		
	        // Get formalized constraints, implies and excludes
	 		List<String> formalizedRequires = new ArrayList<String>();
	 		List<String> formalizedExcludes = new ArrayList<String>();
	 		FeatureDependencies fd = new FeatureDependencies(featureModel);
	 		for (IFeature f : fd.always(fc)) {
	 			formalizedRequires.add(f.getName());
	 		}
	 		for (IFeature f : fd.never(fc)) {
	 			formalizedExcludes.add(f.getName());
	 		}
	 	
		List<String> relatedFeatures = computeWidgetFeatures(featureProject);
	    List<IFeature> childF = new ArrayList<>();
		List<IFeature> HiddenF = configuration.getUnSelectedFeatures();
		List<IFeature> coreF = FeatureUtils.getAnalyser(featureModel).getCoreFeatures();
		
			Iterable<IFeature> j = (Iterable<IFeature>) FeatureUtils.getChildren(fc).iterator();
			if(FeatureUtils.hasChildren(fc)){	
				for (; ((Iterator<IFeature>) j).hasNext();)
		        {
					Object next = ((Iterator<IFeature>) j).next();
					childF.add((IFeature) next);	
		        }
			}
	  
		for(String s : formalizedRequires){
			if(!relatedFeatures.contains(s)){
				relatedFeatures.add(s);
			}
			
		}
		for(String s : formalizedExcludes){
			if(!relatedFeatures.contains(s)){
				relatedFeatures.add(s);
			}
			
		}
		
		for(IFeature f : childF){
			relatedFeatures.add(f.getName());
		}
		
		relatedFeatures.remove(fc.getName());
		relatedFeatures.remove(FeatureUtils.getRoot(featureModel).getName());
		for(IFeature f:HiddenF){
			relatedFeatures.remove(f.getName());
		}
		
		for(IFeature f:coreF){
			relatedFeatures.remove(f.getName());
		}
		for(int i = 0 ; i< relatedFeatures.size()-1;i++){
			if(relatedFeatures.get(i).equals(relatedFeatures.get(i+1))){
				relatedFeatures.remove(relatedFeatures.get(i));
			}
			
		}
		Set<String> stringSet = new HashSet<>(relatedFeatures);
		String[] relatedFeatures11 = stringSet.toArray(new String[0]);
	    List<String> relatedFeatures12 = Arrays.asList(relatedFeatures11);
		return new Object[]{relatedFeatures12,formalizedRequires,formalizedExcludes};
		
	}
	
	
	@SuppressWarnings("unchecked")
	public static List<String> computeWidgetFeatures(IFeatureProject featureProject) {
		IFeatureModel featureModel = featureProject.getFeatureModel();
	    Configuration configuration = new Configuration(featureModel);
		FileHandler.load(Paths.get(featureProject.getCurrentConfiguration().getLocationURI()), configuration, new DefaultFormat());
		List<IFeature> childF = new ArrayList<>();
		List<String> widgetFeatures = new ArrayList<>();
		List<IFeature> unselectedFeatures = configuration.getUndefinedSelectedFeatures();
		for(IFeature f: unselectedFeatures) {
			Iterable<IFeature> j = (Iterable<IFeature>) FeatureUtils.getChildren(f).iterator();
			if(FeatureUtils.hasChildren(f)){	
				for (; ((Iterator<IFeature>) j).hasNext();)
		        {
					Object next = ((Iterator<IFeature>) j).next();
					childF.add((IFeature) next);	
		        }
			}
			
		}
		unselectedFeatures.removeAll(childF);
		for(IFeature f : unselectedFeatures) {
			widgetFeatures.add(f.getName());
		}
		return widgetFeatures;
	}
	
	public static int eval(IFeatureProject featureProject) {
		IFeatureModel featureModel = featureProject.getFeatureModel();
		Configuration configuration = new Configuration(featureModel);
		configuration.update();
		int currentValue = 0;
		int lastValue = 0;
		int maxValue = 0;
		while (true) {
			List<String> widgetFeatures = new ArrayList<>();
			List<IFeature> childF = new ArrayList<>();
			List<IFeature> unselectedFeatures = configuration.getUndefinedSelectedFeatures();
			for (IFeature f : unselectedFeatures) {
				Iterable<IFeature> j = (Iterable<IFeature>) FeatureUtils.getChildren(f).iterator();
				if (FeatureUtils.hasChildren(f)) {
					for (; ((Iterator<IFeature>) j).hasNext();) {
						Object next = ((Iterator<IFeature>) j).next();
						childF.add((IFeature) next);
					}
				}

			}
			unselectedFeatures.removeAll(childF);
			for (IFeature f : unselectedFeatures) {
				widgetFeatures.add(f.getName());
			}
			
			if (widgetFeatures.isEmpty()) {
				break;
			}
			
			String name = widgetFeatures.get(new Random().nextInt(widgetFeatures.size()));
		    Object[] relatedF	= getRelatedFeatures(featureProject, name);
			List<String> relatedFeatures = (List<String>)relatedF[0];
			Object[] NFPCenter = NFProps.computeNFP(featureProject,name);
			List<String> NFP = (List<String>)NFPCenter[0];
			currentValue = NFP.size() + relatedFeatures.size();
		    maxValue  = (currentValue > lastValue) ? currentValue : lastValue;
		    System.out.println("currentValue is "+currentValue+" lastValue is "+lastValue+" maxValue is"+maxValue);
			configuration.setManual(name, Selection.SELECTED);
			configuration.update();
			lastValue = maxValue;
		}
     return maxValue;
	}
}
