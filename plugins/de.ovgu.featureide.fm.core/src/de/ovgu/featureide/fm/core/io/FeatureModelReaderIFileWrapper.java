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
package de.ovgu.featureide.fm.core.io;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.InputStream;
import java.util.List;

import org.eclipse.core.resources.IFile;

import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * TODO description
 * 
 * @author Soenke Holthusen
 */
public class FeatureModelReaderIFileWrapper extends
	AbstractFeatureModelReader {
    private AbstractFeatureModelReader reader;

    public FeatureModelReaderIFileWrapper(AbstractFeatureModelReader reader) {
	this.reader = reader;
    }

    public void setFeatureModel(FeatureModel featureModel) {
	reader.featureModel = featureModel;
    }

    public FeatureModel getFeatureModel() {
	return reader.featureModel;
    }

    public void readFromString(String text) throws UnsupportedModelException {
	reader.readFromString(text);
    }

    public void readFromFile(IFile ifile) throws UnsupportedModelException,
	    FileNotFoundException {
	File file = ifile.getRawLocation().makeAbsolute().toFile();

	reader.readFromFile(file);
    }

    public void readFromFile(File file) throws FileNotFoundException,
	    UnsupportedModelException {
	reader.readFromFile(file);
    }

    public List<ModelWarning> getWarnings() {
	return reader.getWarnings();
    }

    public AbstractFeatureModelReader getReader(){
	return reader;
    }
    
    @Override
    protected void parseInputStream(InputStream inputStream)
	    throws UnsupportedModelException {
	reader.parseInputStream(inputStream);
    }
}
