package de.ovgu.featureide.visualisation;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;


/**
 * NFProps
 * 
 * @author Hari Kumar Gurudu
 */
public class NFProps {

	public static Set<String> names = new HashSet<>();
	
	public  static Object[] computeNFP(IFeatureProject featureProject, String featureCenter){
		
		IFeatureModel featureModel = featureProject.getFeatureModel();
		IFeature fc = featureModel.getFeature(featureCenter);
		List<String> nfp = new ArrayList<String>();
		List<String> NFPValues = new ArrayList<String>();
		int quantityCount = 0;
		HashMap<String, String> keyWithMinMax = computeQuantity(featureProject);
	      try {
			String[] str = FeatureUtils.getDescription(fc).split("\\r?\\n");
			for(String a : str){
				String[] st = a.split(":");
				
				nfp.add(st[0]);
				
				if(isNumeric(st[1])) {
					quantityCount++;
					if(keyWithMinMax.containsKey(st[0])){
						NFPValues.add(normalize(Double.parseDouble(st[1]), keyWithMinMax.get(st[0])));
					
					}
				}else{
					NFPValues.add(getEquivalentNumber(st[1]));
				}
			}
	   }catch(ArrayIndexOutOfBoundsException ignored) {

       }
		return new Object[]{nfp, NFPValues,quantityCount};
	  }	
	
	public static List<Double> NFPGraphFeatures(IFeatureProject featureProject, String featureCenter,String nfpCenter) throws CoreException{
	   
	   HashMap<String, List<Double>> nfPropsHash = new HashMap<>();
	   
	   List<Double> valueList = null;
	   Object[] featurePredicts = ConfigAnalysisUtils.getRelatedFeatures(featureProject,featureCenter);
	   List<String> relatedFeatures = (List<String>)featurePredicts[0];
	   List<Double> featuresNFPValues = new ArrayList<>();
	   List<String> featuresNFP = new ArrayList<>();
	   relatedFeatures.add(featureCenter);
	   System.out.println("relatedFeatures list"+relatedFeatures);
	   for(String f : relatedFeatures){
		   Object[] nfProperties = computeNFP(featureProject,f);
		   List<String> nfp = (List<String>)nfProperties[0]; 
		   for(int i = 0 ; i < nfp.size() ; i ++){
			   if(nfp.get(i) == null || nfp.get(i).trim().length()== 0 || nfp.get(i).trim().equalsIgnoreCase("")){
				   nfp.remove(i);
				   i--;
			   }
				   
		   } 
		   List<String> nfpValues = (List<String>)nfProperties[1];
		   
		   for(String s :  names){
			   if(!nfp.contains(s)){
				   nfp.add(s);
				   nfpValues.add("2.0");
			   }
		   }
		   
		   
		   try{
				 for(int i=0; i< nfp.size();i++){
					   if(nfPropsHash.containsKey(nfp.get(i))) {
						   nfPropsHash.get(nfp.get(i)).add(Double.parseDouble(nfpValues.get(i)));
						}else{
							valueList = new ArrayList<>();
							valueList.add(Double.parseDouble(nfpValues.get(i)));
							nfPropsHash.put(nfp.get(i), valueList);
						}
				   }
		   } catch(Exception ex){
			   ex.printStackTrace();
		   }
	   }
	   
	   for(String key : nfPropsHash.keySet()){
		   featuresNFP.add(key);
		   if(key.equals(nfpCenter)){
			   featuresNFPValues.addAll(nfPropsHash.get(key));
		   }
		   System.out.println(nfPropsHash.get(key));
	   }
	
	 
	  System.out.println("featuresNFPValues ..."+featuresNFPValues);
	  System.out.println("featuresNFP.."+featuresNFP);
		return featuresNFPValues;
	}
	
	private static String getEquivalentNumber(String b){
		String result = null;
		if( b.equals("HighP")){
			result = "0.925";
	   }else if(b.equals("MedP")){
		   result = "0.765";
	   }else if (b.equals("LowP")){
			result = "0.595";
	   }else if (b.equals("LowN")){
			result = "0.595"; 
	   }else if (b.equals("MedN")){
			result = "0.255";
	   }else if(b.equals("HighN")){
			result = "0.085";
	   }
		return result;
	}
	
	private static String normalize(double actual, String strMinMax){
		String[] minMax = strMinMax.split("-");
		double result = 0D;
		if(minMax.length == 2 
				&& (Double.parseDouble( minMax[0]) != Double.parseDouble( minMax[1]))){
				result = 	(actual - Double.parseDouble(minMax[0]))/((Double.parseDouble(minMax[1]) - Double.parseDouble(minMax[0])));
		}else{
			result = 0.5;
		}
		return result+"";
		
	}
	
	public static boolean isNumeric(String str)
	{
	  return str.matches("-?\\d+(\\.\\d+)?");  //match a number with optional '-' and decimal.
	}
	
	
	
	public static HashMap<String, String> computeQuantity(IFeatureProject featureProject) {
		IFeatureModel featureModel = featureProject.getFeatureModel();
		HashMap<String, List<Double>> NFPHash = new HashMap<>();
		List<Double> valueList = null;
		HashMap<String, String> keyWithMinMax = new HashMap<>();

		for (IFeature f : featureModel.getFeatures()) {
			if (FeatureUtils.getDescription(f) != null) {
				String[] eachLine = FeatureUtils.getDescription(f).split("\\r?\\n");
				for (String a : eachLine) {
					String[] keyValStr = a.split(":");
					if(keyValStr.length==2){
						names.add(keyValStr[0]);
					}
					if(keyValStr.length==2 && isNumeric(keyValStr[1])){
						
						if(NFPHash.containsKey(keyValStr[0])) {
							NFPHash.get(keyValStr[0]).add(Double.parseDouble(keyValStr[1]));
						}
						else{
							valueList = new ArrayList<>();
							valueList.add(Double.parseDouble(keyValStr[1]));
							NFPHash.put(keyValStr[0], valueList);
						}
					}
				}
			}

		}
		
		for(String key : NFPHash.keySet()){
			Collections.sort(NFPHash.get(key));
			keyWithMinMax.put(key, NFPHash.get(key).get(0)+"-"+(NFPHash.get(key).size()==1 ?  NFPHash.get(key).get(0) : NFPHash.get(key).get(NFPHash.get(key).size()-1)));
		}
		System.out.println(keyWithMinMax);
		return keyWithMinMax;
	  }		
}
