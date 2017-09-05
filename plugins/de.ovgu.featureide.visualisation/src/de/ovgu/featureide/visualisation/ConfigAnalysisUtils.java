package de.ovgu.featureide.visualisation;

import java.io.IOException;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collection;
import java.util.ConcurrentModificationException;
import java.util.Iterator;
import java.util.List;
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
	 		/*List<String> formalizedRequires11 = new ArrayList<String>();
	 		List<String> formalizedExcludes11 = new ArrayList<String>();
	 		List<String> formalizedRequires22 = new ArrayList<String>();
	 		List<String> formalizedExcludes22 = new ArrayList<String>();*/
	 		FeatureDependencies fd = new FeatureDependencies(featureModel);
	 		for (IFeature f : fd.always(fc)) {
	 			formalizedRequires.add(f.getName());
	 		}
	 		for (IFeature f : fd.never(fc)) {
	 			formalizedExcludes.add(f.getName());
	 		}
	 	
		List<String> relatedFeatures = computeWidgetFeatures(featureProject);
		  List<String> relatedFeatures11 = new ArrayList<>();
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
	    /*formalizedRequires11.addAll(formalizedRequires);
	    formalizedExcludes11.addAll(formalizedExcludes);
		for(IFeature f:HiddenF){
			formalizedRequires11.remove(f.getName());
			formalizedExcludes11.remove(f.getName());
		}
			
		for(IFeature f:coreF){
			formalizedRequires11.remove(f.getName());
			formalizedExcludes11.remove(f.getName());
		}
	
		try{
		for(String s:formalizedRequires11 ) {
        	IFeature fi = featureModel.getFeature(s);
        	for (IFeature f : fd.always(fi)) {
	 			formalizedRequires22.add(f.getName());
	 		}
	 		for (IFeature f : fd.never(fi)) {
	 			formalizedExcludes22.add(f.getName());
	 		}
		}
		}catch(ConcurrentModificationException ignored){
			
		}
		formalizedRequires.addAll(formalizedRequires22);
		formalizedExcludes.addAll(formalizedExcludes22);*/
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
		
		
		return new Object[]{relatedFeatures,formalizedRequires,formalizedExcludes};
		
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
}
