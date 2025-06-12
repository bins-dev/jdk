/*
 * Copyright (c) 2014, 2022, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.  Oracle designates this
 * particular file as subject to the "Classpath" exception as provided
 * by Oracle in the LICENSE file that accompanied this code.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 */
package jdk.internal.jimage;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.nio.IntBuffer;
import java.nio.file.Files;
import java.nio.file.attribute.BasicFileAttributes;
import java.nio.file.attribute.FileTime;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.Stream;

/**
 * @implNote This class needs to maintain JDK 8 source compatibility.
 *
 * It is used internally in the JDK to implement jimage/jrtfs access,
 * but also compiled and delivered as part of the jrtfs.jar to support access
 * to the jimage file provided by the shipped JDK by tools running on JDK 8.
 */
public final class ImageReader implements AutoCloseable {
    private final SharedImageReader reader;

    private volatile boolean closed;

    private ImageReader(SharedImageReader reader) {
        this.reader = reader;
    }

    public static ImageReader open(Path imagePath, ByteOrder byteOrder) throws IOException {
        Objects.requireNonNull(imagePath);
        Objects.requireNonNull(byteOrder);

        return SharedImageReader.open(imagePath, byteOrder);
    }

    public static ImageReader open(Path imagePath) throws IOException {
        return open(imagePath, ByteOrder.nativeOrder());
    }

    @Override
    public void close() throws IOException {
        if (closed) {
            throw new IOException("image file already closed");
        }
        reader.close(this);
        closed = true;
    }

    private void ensureOpen() throws IOException {
        if (closed) {
            throw new IOException("image file closed");
        }
    }

    private void requireOpen() {
        if (closed) {
            throw new IllegalStateException("image file closed");
        }
    }

    // TODO: Called by SystemImage (now completely pointless).
    // directory management interface
    public Directory getRootDirectory() throws IOException {
        ensureOpen();
        return (Directory) findNode("/");
    }

    // TODO: Called by SystemImage and SystemModuleFinders.
    public Node findNode(String name) throws IOException {
        ensureOpen();
        return reader.findNode(name);
    }

    // TODO: Called by SystemImage for JrtFileSystem.
    public byte[] getResource(Node node) throws IOException {
        ensureOpen();
        return reader.getResource(node);
    }

    // TODO: Called once from SystemModuleReader::release().
    public static void releaseByteBuffer(ByteBuffer buffer) {
        BasicImageReader.releaseByteBuffer(buffer);
    }

    // TODO: Avoid leaking ImageLocation into callers (only 3) so we can
    //  encapsulate better for exploded image etc.
    public ImageLocation findLocation(String mn, String rn) {
        requireOpen();
        return reader.findLocation(mn, rn);
    }

    public boolean verifyLocation(String mn, String rn) {
        requireOpen();
        return reader.verifyLocation(mn, rn);
    }

    // TODO: Only called once when processing module info.
    //  Maybe simplify to use findNode("/modules").getChildren() ?
    public String[] getModuleNames() {
        requireOpen();
        int off = "/modules/".length();
        return reader.findNode("/modules")
                .getChildNames()
                .map(s -> s.substring(off))
                .toArray(String[]::new);
    }

    // TODO: Called once by JavaURuntimeURLConnection ...
    public byte[] getResource(ImageLocation loc) {
        requireOpen();
        return reader.getResource(loc);
    }

    // TODO: Called twice in SystemModuleFinders.
    public ByteBuffer getResourceBuffer(ImageLocation loc) {
        requireOpen();
        return reader.getResourceBuffer(loc);
    }

    private static final class SharedImageReader extends BasicImageReader {
        private static final Map<Path, SharedImageReader> OPEN_FILES = new HashMap<>();

        // List of openers for this shared image.
        private final Set<ImageReader> openers;

        // attributes of the .jimage file. jimage file does not contain
        // attributes for the individual resources (yet). We use attributes
        // of the jimage file itself (creation, modification, access times).
        // Initialized lazily, see {@link #imageFileAttributes()}.
        private BasicFileAttributes imageFileAttributes;

        // TODO: Add JavaDoc explaining Image vs System paths.
        // Map from absolute "system path" to cached node instances.
        // This is guarded by via synchronization of 'this' instance.
        private final HashMap<String, Node> nodes;
        // Used to quickly test ImageLocation without needing string comparisons.
        private final int modulesStringOffset;
        private final int packagesStringOffset;

        private SharedImageReader(Path imagePath, ByteOrder byteOrder) throws IOException {
            super(imagePath, byteOrder);
            this.openers = new HashSet<>();
            // TODO: Given there are 30,000 nodes in the image, is setting an initial capacity a good idea?
            this.nodes = new HashMap<>();
            // The *really* should exist under all circumstances, but there's
            // probably a more robust way of getting it...
            this.modulesStringOffset = findLocation("/modules/java.base").getModuleOffset();
            this.packagesStringOffset = findLocation("/packages/java.lang").getModuleOffset();

            // Node creation is very lazy, se can just make the top-level directories
            // now without the risk of triggering the building of lots of other nodes.
            Directory packages = newDirectory("/packages");
            nodes.put(packages.getName(), packages);
            Directory modules = newDirectory("/modules");
            nodes.put(modules.getName(), modules);

            Directory root = newDirectory("/");
            root.setChildren(Arrays.asList(packages, modules));
            nodes.put(root.getName(), root);
        }

        public static ImageReader open(Path imagePath, ByteOrder byteOrder) throws IOException {
            Objects.requireNonNull(imagePath);
            Objects.requireNonNull(byteOrder);

            synchronized (OPEN_FILES) {
                SharedImageReader reader = OPEN_FILES.get(imagePath);

                if (reader == null) {
                    // Will fail with an IOException if wrong byteOrder.
                    reader =  new SharedImageReader(imagePath, byteOrder);
                    OPEN_FILES.put(imagePath, reader);
                } else if (reader.getByteOrder() != byteOrder) {
                    throw new IOException("\"" + reader.getName() + "\" is not an image file");
                }

                ImageReader image = new ImageReader(reader);
                reader.openers.add(image);

                return image;
            }
        }

        public void close(ImageReader image) throws IOException {
            Objects.requireNonNull(image);

            synchronized (OPEN_FILES) {
                if (!openers.remove(image)) {
                    throw new IOException("image file already closed");
                }

                if (openers.isEmpty()) {
                    close();
                    // TODO: Should this be synchronized by "this" ??
                    nodes.clear();

                    if (!OPEN_FILES.remove(this.getImagePath(), this)) {
                        throw new IOException("image file not found in open list");
                    }
                }
            }
        }

        /// Returns a node in the JRT filesystem namespace, or null if no resource or
        /// directory exists.
        ///
        /// Node names are absolute, {@code /}-separated path strings, prefixed with
        /// either {@code "/modules"} or {@code "/packages"}.
        ///
        /// This is the only public API by which anything outside this class can access
        /// Node instances either directly, or by resolving a symbolic link.
        ///
        /// Note also that there is no reentrant calling back to this method from within
        /// the node handling code.
        synchronized Node findNode(String name) {
            Node node = nodes.get(name);
            if (node == null) {
                node = buildNode(name);
                if (node != null) {
                    nodes.put(node.getName(), node);
                }
            } else if (!node.isCompleted()) {
                // Only directories can be incomplete.
                assert node instanceof Directory : "Invalid incomplete node: " + node;
                completeDirectory((Directory) node);
            }
            assert node == null || node.isCompleted() : "Incomplete node: " + node;
            return node;
        }

        /// Builds a new, "complete" node based on its absolute name.
        /// We only get here if the name is not yet present in the nodes map.
        private Node buildNode(String name) {
            // Zero-allocation test to reject any unexpected paths early.
            boolean isPackages = name.startsWith("/packages");
            boolean isModules = !isPackages && name.startsWith("/modules");
            if (!(isModules || isPackages)) {
                return null;
            }
            // Will FAIL for non-directory resources, since the image path does not
            // start with "/modules" (e.g. "/java.base/java/lang/Object.class").
            ImageLocation loc = findLocation(name);

            Node node = null;
            if (loc != null) {
                // A subtree node in either /modules/... or /packages/...
                node = isPackages
                        ? buildPackageNode(name, loc)
                        : buildModuleDirectory(name, loc);
            } else if (isModules) {
                // We still cannot trust that this path is valid, but if it is,
                // it must be a resource node in /modules/...
                node = buildResourceNode(name);
            }
            return node;
        }

        /// Completes a directory by ensuring its child list is populated correctly.
        private void completeDirectory(Directory dir) {
            String name = dir.getName();
            // Since the node exists, we can assert that it's name starts with
            // either /modules or /packages, making differentiation easy. It also
            // means that the name is valid and which must yield a location.
            assert name.startsWith("/modules") || name.startsWith("/packages");
            ImageLocation loc = findLocation(name);
            assert loc != null && name.equals(loc.getFullName()) : "Invalid location for name: " + name;
            // We cannot use 'isXxxSubdirectory()' methods here since we could
            // be given a top-level directory.
            if (name.charAt(1) == 'm') {
                completeModuleDirectory(dir, loc);
            } else {
                completePackageDirectory(dir, loc);
            }
            assert dir.isCompleted() : "Directory must be complete by now: " + dir;
        }

        /// Builds either a 2nd level package directory, or a 3rd level symbolic
        /// link from an {@code ImageLocation}. Possible names are:
        ///
        /// * {@code /packages/<package>}: Builds a {@code Directory}.
        /// * {@code /packages/<package>/<module>}: Builds a {@code LinkNode}.
        ///
        /// Called by {@code buildNode()} if a package node is not present in the
        /// cache. The top-level {@code /packages} directory was already built by
        /// {@code buildRootDirectory}.
        private Node buildPackageNode(String name, ImageLocation loc) {
            assert !name.equals("/packages") : "Cannot build root /packages directory";
            if (isPackagesSubdirectory(loc)) {
                return completePackageDirectory(newDirectory(name), loc);
            }
            int modStart = name.indexOf('/', "/packages/".length()) + 1;
            assert modStart > 0 && name.indexOf('/', modStart) == -1 : "Invalid link name: " + name;
            return newLinkNode(name, "/modules/" + name.substring(modStart));
        }

        /// Completes a package directory by setting the list of child nodes.
        ///
        /// This is called by {@code buildPackageNode()}, but also for the
        /// top-level {@code /packages} directory.
        private Directory completePackageDirectory(Directory dir, ImageLocation loc) {
            assert dir.getName().equals(loc.getFullName()) : "Mismatched location for directory: " + dir;
            // The only directories in the /packages namespace are /packages or
            // /packages/<package>. However, unlike /modules directories, the
            // location offsets mean different things.
            List<Node> children;
            if (dir.getName().equals("/packages")) {
                // Top-level directory just contains a list of subdirectories.
                children = createChildNodes(loc, c -> nodes.computeIfAbsent(c.getFullName(), this::newDirectory));
            } else {
                // A package directory's content is array of offset PAIRS in the
                // Strings table, but we only need the 2nd value of each pair.
                IntBuffer intBuffer = getOffsetBuffer(loc);
                int offsetCount = intBuffer.capacity();
                children = new ArrayList<>(offsetCount / 2);
                // Iterate the 2nd offset in each pair (odd indices).
                for (int i = 1; i < offsetCount; i += 2) {
                    String moduleName = getString(intBuffer.get(i));
                    children.add(nodes.computeIfAbsent(
                            dir.getName() + "/" + moduleName,
                            n -> newLinkNode(n, "/modules/" + moduleName)));
                }
            }
            // This only happens once and "completes" the directory.
            dir.setChildren(children);
            return dir;
        }

        /// Builds a modules subdirectory directory from an {@code ImageLocation}.
        ///
        /// Called by {@code buildNode()} if a module directory is not present in
        /// the cache. The top-level {@code /modules} directory was already built by
        /// {@code buildRootDirectory}.
        private Node buildModuleDirectory(String name, ImageLocation loc) {
            assert name.equals(loc.getFullName()) : "Mismatched location for directory: " + name;
            assert isModulesSubdirectory(loc) : "Invalid modules directory: " + name;
            return completeModuleDirectory(newDirectory(name), loc);
        }

        /// Completes a modules directory by setting the list of child nodes.
        ///
        /// The given directory can be the top level {@code /modules} directory
        /// (so it is NOT safe to use {@code isModulesSubdirectory(loc)} here).
        private Directory completeModuleDirectory(Directory dir, ImageLocation loc) {
            assert dir.getName().equals(loc.getFullName()) : "Mismatched location for directory: " + dir;
            List<Node> children = createChildNodes(loc, (childloc) -> {
                if (isModulesSubdirectory(childloc)) {
                    return nodes.computeIfAbsent(childloc.getFullName(), this::newDirectory);
                } else {
                    // Add the "/modules" prefix to image location paths to get
                    // Jrt file system names.
                    String resourceName = childloc.getFullName(true);
                    return nodes.computeIfAbsent(resourceName, n -> newResource(n, childloc));
                }
            });
            dir.setChildren(children);
            return dir;
        }

        /// Builds a resource node in the {@code /modules} hierarchy.
        ///
        /// Called by {@code buildNode()} if there was no entry for the given
        /// name in the cache. Unlike {@code buildPackageNode()} and
        /// {@code buildModuleDirectory()}, there is no ImageLocation (yet) and
        /// the given name cannot be trusted to belong to any resource (or even
        /// be a valid resource name).
        private Node buildResourceNode(String name) {
            if (!name.startsWith("/modules/")) {
                return null;
            }
            // Make sure that the thing that follows "/modules/" is a module name.
            int moduleEndIndex = name.indexOf('/', "/modules/".length());
            if (moduleEndIndex == -1) {
                return null;
            }
            // Tests that the implied module name actually exists before during
            // a full lookup for the location.
            // TODO: I don't think this is strictly necessary (maybe an assert)?
            ImageLocation moduleLoc = findLocation(name.substring(0, moduleEndIndex));
            if (moduleLoc == null || moduleLoc.getModuleOffset() == 0) {
                return null;
            }
            // Resource paths in the image are NOT prefixed with /modules.
            ImageLocation resourceLoc = findLocation(name.substring("/modules".length()));
            if (resourceLoc == null) {
                return null;
            }
            return newResource(name, resourceLoc);
        }

        /// Creates the list of child nodes for a {@code Directory} based on a
        /// given node creation function.
        ///
        /// Note: This cannot be used for package subdirectories as they have
        /// child offsets stored differently to other directories.
        private List<Node> createChildNodes(ImageLocation loc, Function<ImageLocation, Node> newChildFn) {
            IntBuffer offsets = getOffsetBuffer(loc);
            int childCount = offsets.capacity();
            List<Node> children = new ArrayList<>(childCount);
            for (int i = 0; i < childCount; i++) {
                children.add(newChildFn.apply(getLocation(offsets.get(i))));
            }
            return children;
        }

        /// Helper method to extract the integer offset buffer from a directory
        /// location.
        private IntBuffer getOffsetBuffer(ImageLocation dir) {
            assert isDirectory(dir) : "Not a directory: " + dir.getFullName();
            byte[] offsets = getResource(dir);
            ByteBuffer buffer = ByteBuffer.wrap(offsets);
            buffer.order(getByteOrder());
            return buffer.asIntBuffer();
        }

        /// Determines if an image location is a directory in the {@code /modules}
        /// namespace (if so, the location name is the Jrt filesystem name).
        ///
        /// In the image namespace, everything under {@code /modules/}  is a
        /// directory, and has the same value for {@code getModule()}.
        private boolean isModulesSubdirectory(ImageLocation loc) {
            return loc.getModuleOffset() == modulesStringOffset;
        }

        /// Determines if an image location is a directory in the {@code /packages}
        /// namespace (if so, the location name is the Jrt filesystem name).
        ///
        /// For locations under {@code /packages/} you have both directories and
        /// symbolic links. Directories are only at the first level, with symbolic
        /// links under them (and symbolic link entries have no content).
        private boolean isPackagesSubdirectory(ImageLocation loc) {
            return loc.getModuleOffset() == packagesStringOffset
                    && loc.getUncompressedSize() > 0;
        }

        /// Determines if an image location represents a directory of some kind.
        /// Directory locations store child offsets in their content.
        private boolean isDirectory(ImageLocation loc) {
            return isModulesSubdirectory(loc) || isPackagesSubdirectory(loc)
                    || loc.getFullName().equals("/modules") || loc.getFullName().equals("/packages");
        }

        /// Returns the file attributes of the image file. Currently, all nodes
        /// share the same attributes.
        private BasicFileAttributes imageFileAttributes() {
            BasicFileAttributes attrs = imageFileAttributes;
            if (attrs == null) {
                try {
                    attrs = Files.readAttributes(getImagePath(), BasicFileAttributes.class);
                } catch (IOException ioe) {
                    throw new UncheckedIOException(ioe);
                }
                imageFileAttributes = attrs;
            }
            return attrs;
        }

        /// Creates an "incomplete" directory node with no child nodes set.
        /// Directories need to be "completed" before they are returned by
        /// {@code findNode()}.
        private Directory newDirectory(String name) {
            return new Directory(name, imageFileAttributes());
        }

        /// Creates a new resource from an image location. This is the only case
        /// where the image location name does not match the requested node name.
        /// In image files, resource locations are NOT prefixed by {@code /modules}.
        private Resource newResource(String name, ImageLocation loc) {
            assert name.equals(loc.getFullName(true)) : "Mismatched location for resource: " + name;
            return new Resource(name, loc, imageFileAttributes());
        }

        /// Creates a new link node pointing at the given target name.
        ///
        /// Note that target node is resolved each time {@code resolve()} is
        /// called, so if a link node is retained after its reader is closed,
        /// it will begin to fail.
        private LinkNode newLinkNode(String name, String targetName) {
            return new LinkNode(name, () -> findNode(targetName), imageFileAttributes());
        }

        /// Returns the content of a resource node.
        private byte[] getResource(Node node) throws IOException {
            // We could have been given a non-resource node here.
            // TODO: Would it be more robust to have this method accept Resource
            //  and have the caller verify by type (getLocation() fails anyway)?
            if (node.isResource()) {
                return super.getResource(node.getLocation());
            }
            throw new IOException("Not a resource: " + node);
        }
    }

    public abstract static class Node {
        private final String name;
        private final BasicFileAttributes fileAttrs;

        // TODO: Only visible for use by ExplodedImage.
        protected Node(String name, BasicFileAttributes fileAttrs) {
            this.name = Objects.requireNonNull(name);
            this.fileAttrs = Objects.requireNonNull(fileAttrs);
        }

        /**
         * A node is completed when all its direct children have been built. As
         * such, non-directory nodes are always complete.
         */
        boolean isCompleted() {
            return true;
        }

        public final String getName() {
            return name;
        }

        public final BasicFileAttributes getFileAttributes() {
            return fileAttrs;
        }

        // resolve this Node (if this is a soft link, get underlying Node)
        public final Node resolveLink() {
            return resolveLink(false);
        }

        public Node resolveLink(boolean recursive) {
            return this;
        }

        // is this a soft link Node?
        public boolean isLink() {
            return false;
        }

        public boolean isDirectory() {
            return false;
        }

        public Stream<String> getChildNames() {
            throw new IllegalArgumentException("not a directory: " + getNameString());
        }

        public boolean isResource() {
            return false;
        }

        public ImageLocation getLocation() {
            throw new IllegalArgumentException("not a resource: " + getNameString());
        }

        public long size() {
            return 0L;
        }

        public long compressedSize() {
            return 0L;
        }

        public String extension() {
            return null;
        }

        public final FileTime creationTime() {
            return fileAttrs.creationTime();
        }

        public final FileTime lastAccessTime() {
            return fileAttrs.lastAccessTime();
        }

        public final FileTime lastModifiedTime() {
            return fileAttrs.lastModifiedTime();
        }

        public final String getNameString() {
            return name;
        }

        @Override
        public final String toString() {
            return getNameString();
        }

        @Override
        public final int hashCode() {
            return name.hashCode();
        }

        @Override
        public final boolean equals(Object other) {
            if (this == other) {
                return true;
            }

            if (other instanceof Node) {
                return name.equals(((Node) other).name);
            }

            return false;
        }
    }

    /// Directory node (referenced from a full path, without a trailing '/').
    ///
    /// Directory nodes have two distinct states:
    /// * Incomplete: The child list has not been set.
    /// * Complete: The child list has been set.
    ///
    /// When a directory node is returned by {@code findNode()} it is ensured to
    /// be complete, but this DOES NOT mean that its child nodes are complete.
    ///
    /// The users of {@code ImageReader} are expected to account for this and
    /// avoid directly traversing the node hierarchy. This isn't as awkward as
    /// it seems however, since {@code JrtFileSystem} (the primary user of this
    /// API) always represents node locations via {@code JrtPath}, and so will
    /// always lookup nodes directly by name rather than traversing the node
    /// hierarchy.
    ///
    /// If it was ever a requirement that {@code getChildren()} would return
    /// complete nodes, that could be easily achieved via a memoized child list
    /// supplier, but this would likely come at the cost of performance.
    ///
    /// The exact rule(s) by which the set of child nodes is determined is
    /// inferred in `buildNode()` from the structure of the requested path and
    /// the underlying `ImageLocation` data.
    private static final class Directory extends Node {
        // Monotonic reference, will be set to the unmodifiable child list exactly once.
        private List<Node> children = null;

        private Directory(String name, BasicFileAttributes fileAttrs) {
            super(name, fileAttrs);
        }

        @Override
        boolean isCompleted() {
            return children != null;
        }

        @Override
        public boolean isDirectory() {
            return true;
        }

        @Override
        public Stream<String> getChildNames() {
            if (children != null) {
                return children.stream().map(Node::getName);
            }
            throw new IllegalStateException("Cannot get child nodes of an incomplete directory: " + getName());
        }

        private void setChildren(List<Node> children) {
            assert this.children == null : this + ": Cannot set child nodes twice!";
            this.children = Collections.unmodifiableList(children);
        }
    }

    /// Resource node (a ".class" or any other data resource in jimage).
    ///
    /// Resources are leaf nodes referencing an underlying image location. They
    /// are lightweight, and do not cache their contents.
    ///
    /// Unlike directories (where the node name matches the jimage path for the
    /// corresponding {@code ImageLocation}), resource node names are NOT the
    /// same as the corresponding jimage path. The difference is simply that
    /// jimage paths are not prefixed with "/modules", and just start with
    /// their module name (e.g. "/java.base/java/lang/Object.class").
    private static class Resource extends Node {
        private final ImageLocation loc;

        private Resource(String name, ImageLocation loc, BasicFileAttributes fileAttrs) {
            super(name, fileAttrs);
            this.loc = loc;
        }

        @Override
        public boolean isResource() {
            return true;
        }

        @Override
        public ImageLocation getLocation() {
            return loc;
        }

        @Override
        public long size() {
            return loc.getUncompressedSize();
        }

        @Override
        public long compressedSize() {
            return loc.getCompressedSize();
        }

        @Override
        public String extension() {
            return loc.getExtension();
        }
    }

    /// Link node (a symbolic link to a top-level modules directory).
    ///
    /// Link nodes resolve their target by invoking a given supplier, and do not
    /// cache the result. Since nodes are cached by the {@code ImageReader}, this
    /// means that only the first call to {@code resolveLink()} can do any work.
    private static class LinkNode extends Node {
        private final Supplier<Node> link;

        private LinkNode(String name, Supplier<Node> link, BasicFileAttributes fileAttrs) {
            super(name, fileAttrs);
            this.link = link;
        }

        @Override
        public Node resolveLink(boolean recursive) {
            return link.get();
        }

        @Override
        public boolean isLink() {
            return true;
        }
    }
}
