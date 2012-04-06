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

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.InputStream;
import java.nio.charset.Charset;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * TODO description
 * 
 * @author Soenke Holthusen
 */
public class FeatureModelWriterIFileWrapper extends AbstractFeatureModelWriter {

    private AbstractFeatureModelWriter writer;

    public FeatureModelWriterIFileWrapper(AbstractFeatureModelWriter writer) {
	this.writer = writer;
    }

    public void setFeatureModel(FeatureModel featureModel) {
	writer.setFeatureModel(featureModel);
    }

    public FeatureModel getFeatureModel() {
	return writer.getFeatureModel();
    }
    
    public void writeToFile(File file){
	writer.writeToFile(file);
    }

    @Override
    public String writeToString() {
	return writer.writeToString();
    }

    public void writeToFile(IFile file) throws CoreException {
	InputStream source = new ByteArrayInputStream(writeToString().getBytes(
		Charset.availableCharsets().get("UTF-8")));
	if (file.exists()) {
	    file.setContents(source, false, true, null);
	} else {
	    file.create(source, false, null);
	}
    }
}
