/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.conversion;

import static org.junit.Assert.*;

import java.io.File;
import java.io.FileFilter;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.editing.Comparison;
import de.ovgu.featureide.fm.core.editing.ModelComparator;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelWriter;

// TODO: Add tests for refactorings of complex constraints

/**
 * Tests for ComplexConstraintConverter.
 * 
 * @author Arthur Hammer
 */
@RunWith(Parameterized.class)
public class ComplexConstraintConverterTest {

	private static final ComplexConstraintConverterCNF cnfConverter = new ComplexConstraintConverterCNF(true);
	private static final ComplexConstraintConverterDNF dnfConverter = new ComplexConstraintConverterDNF();
	private static final ModelComparator comparator = new ModelComparator(10000);

	private FeatureModel fm;
	private FeatureModel result;
	@SuppressWarnings("unused")
	private String name; 

	private final static String FOLDER_NAME = "testConstraintConversionModels";
	protected static File MODEL_FILE_FOLDER = new File("/home/itidbrun/TeamCity/buildAgent/work/featureide/tests/de.ovgu.featureide.fm.core-test/src/" + FOLDER_NAME + "/");

	public ComplexConstraintConverterTest(FeatureModel fm, String name) {
		this.fm = fm;
		this.name = name;
	}

	@Parameters(name = "{1}")
	public static Collection<Object[]> getModels()
			throws FileNotFoundException, UnsupportedModelException {
		// first tries the location on build server, if this fails tries to use local location
		if (!MODEL_FILE_FOLDER.canRead()){
			MODEL_FILE_FOLDER = new File(ClassLoader.getSystemResource(FOLDER_NAME).getPath());
		}
		Collection<Object[]> params = new ArrayList<Object[]>();
		for (File f : MODEL_FILE_FOLDER.listFiles(getFileFilter(".xml"))) {
			Object[] models = new Object[2];

			FeatureModel fm = new FeatureModel();
			XmlFeatureModelReader r = new XmlFeatureModelReader(fm);
			r.readFromFile(f);
			models[0] = fm;
			models[1] = f.getName();
			params.add(models);
		}

		return params;
	}

	@Test
	public void testConvertCNF() throws UnsupportedModelException {
		result = cnfConverter.convert(fm);
		assertTrue(refactoring(fm, result));
	}

	@Test
	public void testConvertNaiveCNF() throws UnsupportedModelException {
		result = cnfConverter.convertNaive(fm);
		assertTrue(refactoring(fm, result));
	}

	@Test
	public void testConvertDNF() throws UnsupportedModelException {
		result = dnfConverter.convert(fm);
		assertTrue(refactoring(fm, result));
	}

//	@Test
//	public void testConvertNaiveDNF() throws UnsupportedModelException {
//		result = dnfConverter.convertNaive(fm);
//		assertTrue(refactoring(fm, result));
//	}

	// TODO: Easier way to get number of configurations?
	@Test
	public void testConvertConfigsCNF() throws TimeoutException {
		boolean old = cnfConverter.getUseEquivalence();
		cnfConverter.setUseEquivalence(true);
		result = cnfConverter.convertNaive(fm);
		cnfConverter.setUseEquivalence(old);

		Configuration config = new Configuration(fm);
		Configuration resultConfig = new Configuration(result);
		
		assertEquals(config.getSolutions(10000).size(), resultConfig.getSolutions(10000).size());
	}

	// TODO: For now, we test for refactorings by writing the model into a string and re-parsing it.
	//       Somehow, directly comparing with the comparator seems not to be working.
	private static boolean refactoring(FeatureModel fm, FeatureModel fm2) throws UnsupportedModelException {
		XmlFeatureModelWriter writer = new XmlFeatureModelWriter(fm2);
		XmlFeatureModelReader reader = new XmlFeatureModelReader(new FeatureModel());
		
		reader.readFromString(writer.writeToString());
		fm2 = reader.getFeatureModel();
		
		Comparison result = comparator.compare(fm, fm2);
		System.out.println(result);
		return result == Comparison.REFACTORING;
	}

	private final static FileFilter getFileFilter(final String s) {
		FileFilter filter = new FileFilter() {
			@Override
			public boolean accept(File pathname) {
				return pathname.getName().endsWith(s);
			}
		};
		return filter;
	}
}
