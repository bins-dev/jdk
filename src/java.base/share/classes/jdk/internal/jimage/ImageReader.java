/*
 * Copyright (c) 2014, 2025, Oracle and/or its affiliates. All rights reserved.
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
import java.nio.file.Path;
import java.nio.file.attribute.BasicFileAttributes;
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
 * An adapter for {@link BasicImageReader} to present jimage resources in a
 * file system friendly way. The jimage entries (resources, module and package
 * information) are mapped into a unified hierarchy of named nodes, which serve
 * as the underlying structure for the {@code JrtFileSystem} and other utilities.
 *
 * <p>This class is not a conceptual subtype of {@code BasicImageReader} and
 * deliberately hides types such as {@code ImageLocation} to give a focused API
 * based only on the {@link Node} type. Entries in jimage are expressed as one
 * of three {@link Node} types resource nodes, directory nodes and link nodes.
 *
 * <p>When remapping jimage entries, jimage location names (e.g. {@code
 * "/java.base/java/lang/Integer.class"}) are prefixed with {@code "/modules"}
 * to form the names of resource nodes. This aligns with the naming of module
 * entries in jimage (e.g. "/modules/java.base/java/lang"), which appear as
 * directory nodes in {@code ImageReader}.
 *
 * <p>Package entries (e.g. {@code "/packages/java.lang"} appear as directory
 * nodes containing link nodes, which resolve back to the root directory of the
 * module in which that package exists (e.g. {@code "/modules/java.base"}).
 * Unlike other nodes, the jimage file does not contain explicit entries for
 * link nodes, and their existence is derived only from the contents of the
 * parent directory.
 *
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

    /**
     * Opens an image reader for a jimage file at the specified path, using the
     * given byte order.
     *
     * <p>Almost all callers should use {@link #open(Path)} to obtain a reader
     * with the platform native byte ordering. Using a non-native ordering is
     * extremely unusual.
     */
    public static ImageReader open(Path imagePath, ByteOrder byteOrder) throws IOException {
        Objects.requireNonNull(imagePath);
        Objects.requireNonNull(byteOrder);

        return SharedImageReader.open(imagePath, byteOrder);
    }

    /**
     * Opens an image reader for a jimage file at the specified path, using the
     * platform native byte order.
     *
     * <p>This is the expected was to open an {@code ImageReader}, and it should
     * be rare for anything other than the native byte order to be needed.
     */
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

    /**
     * Finds the node for the given JRT file system name.
     *
     * @param name a JRT file system name (path) of the form
     * {@code "/modules/<module>/...} or {@code "/packages/<package>/...}.
     * @return a node representing a resource, directory or symbolic link.
     */
    public Node findNode(String name) throws IOException {
        ensureOpen();
        return reader.findNode(name);
    }

    /**
     * Returns the content of a resource node.
     *
     * @throws IOException if the content cannot be returned (including if the
     * given node is not a resource node).
     */
    public byte[] getResource(Node node) throws IOException {
        ensureOpen();
        return reader.getResource(node);
    }

    /**
     * Releases a (possibly cached) {@link ByteBuffer} obtained via
     * {@link #getResourceBuffer(Node)}.
     *
     * <p>Note that no testing is performed to check whether the buffer about
     * to be released actually came from a call to {@code getResourceBuffer()}.
     */
    public static void releaseByteBuffer(ByteBuffer buffer) {
        BasicImageReader.releaseByteBuffer(buffer);
    }

    /**
     * Returns the content of a resource node in a possibly cached byte buffer.
     * Callers of this method must call {@link #releaseByteBuffer(ByteBuffer)}
     * when they are finished with it.
     */
    public ByteBuffer getResourceBuffer(Node node) {
        requireOpen();
        if (!node.isResource()) {
            throw new IllegalStateException("Not a resource node: " + node);
        }
        return reader.getResourceBuffer(node.getLocation());
    }

    private static final class SharedImageReader extends BasicImageReader {
        private static final Map<Path, SharedImageReader> OPEN_FILES = new HashMap<>();
        public static final String MODULES_ROOT = "/modules";
        public static final String PACKAGES_ROOT = "/packages";

        // List of openers for this shared image.
        private final Set<ImageReader> openers;

        // Attributes of the .jimage file. The jimage file does not contain
        // attributes for the individual resources (yet). We use attributes
        // of the jimage file itself (creation, modification, access times).
        // Initialized lazily, see imageFileAttributes().
        private BasicFileAttributes imageFileAttributes;

        // Guarded by synchronizing 'this' instance.
        private final HashMap<String, Node> nodes;
        // Used to classify ImageLocation instances without string comparison.
        private final int modulesStringOffset;
        private final int packagesStringOffset;

        private SharedImageReader(Path imagePath, ByteOrder byteOrder) throws IOException {
            super(imagePath, byteOrder);
            this.openers = new HashSet<>();
            // TODO (review note): Given there are ~30,000 nodes in the image, is setting an initial capacity a good idea?
            this.nodes = new HashMap<>();
            // TODO (review note): These should exist under all circumstances, but there's
            //  probably a more robust way of getting at these offsets.
            this.modulesStringOffset = findLocation("/modules/java.base").getModuleOffset();
            this.packagesStringOffset = findLocation("/packages/java.lang").getModuleOffset();

            // Node creation is very lazy, so we can just make the top-level directories
            // now without the risk of triggering the building of lots of other nodes.
            Directory packages = newDirectory(PACKAGES_ROOT);
            nodes.put(packages.getName(), packages);
            Directory modules = newDirectory(MODULES_ROOT);
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
                    // TODO (review note): Should this be synchronized by "this" ??
                    nodes.clear();

                    if (!OPEN_FILES.remove(this.getImagePath(), this)) {
                        throw new IOException("image file not found in open list");
                    }
                }
            }
        }

        /// Returns a node in the JRT filesystem namespace, or null if no resource or
        /// directory of that name exists.
        ///
        /// Node names are absolute, `/`-separated path strings, prefixed with
        /// either "/modules" or "/packages".
        ///
        /// This is the only public API by which anything outside this class can access
        /// `Node` instances either directly, or by resolving a symbolic link.
        ///
        /// Note also that there is no reentrant calling back to this method from within
        /// the node handling code.
        synchronized Node findNode(String name) {
            Node node = nodes.get(name);
            if (node == null) {
                // We cannot be given the root paths ("/modules" or "/packages")
                // because those nodes are already in the nodes cache.
                if (name.startsWith(MODULES_ROOT + "/")) {
                    node = buildModulesNode(name);
                } else if (name.startsWith(PACKAGES_ROOT + "/")) {
                    node = buildPackagesNode(name);
                }
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

        /// Builds a node in the "/modules/..." namespace.
        ///
        /// Called by `findNode()` if a `/modules` node is not present in the cache.
        Node buildModulesNode(String name) {
            assert name.startsWith(MODULES_ROOT + "/") : "Invalid module node name: " + name;
            // Will fail for non-directory resources, since the image path does not
            // start with "/modules" (e.g. "/java.base/java/lang/Object.class").
            ImageLocation loc = findLocation(name);
            if (loc != null) {
                assert name.equals(loc.getFullName()) : "Mismatched location for directory: " + name;
                assert isModulesSubdirectory(loc) : "Invalid modules directory: " + name;
                return completeModuleDirectory(newDirectory(name), loc);
            }
            // TODO (review note): This is a heuristic to avoid spending time on lookup
            //  in cases of failure, but is not strictly required for correct behaviour.
            // If there is no ImageLocation, the given name cannot be trusted to
            // belong to any resource (or even be a valid resource name).
            int moduleEnd = name.indexOf('/', MODULES_ROOT.length() + 1);
            if (moduleEnd == -1) {
                return null;
            }
            // Tests that the implied module name actually exists before doing
            // a full lookup for the location.
            ImageLocation moduleLoc = findLocation(name.substring(0, moduleEnd));
            if (moduleLoc == null || moduleLoc.getModuleOffset() == 0) {
                return null;
            }
            // Resource paths in the image are NOT prefixed with "/modules".
            ImageLocation resourceLoc = findLocation(name.substring(MODULES_ROOT.length()));
            return resourceLoc != null ? newResource(name, resourceLoc) : null;
        }

        /// Builds a node in the "/packages/..." namespace.
        ///
        /// Called by `findNode()` if a `/packages` node is not present in the cache.
        private Node buildPackagesNode(String name) {
            // There are only locations for the root "/packages" or "/packages/xxx"
            // directories, but not the symbolic links below them (the links can be
            // entirely derived from the name information in the parent directory).
            // However, unlike resources this means that we do not have a constant
            // time lookup for link nodes when creating them.
            int packageStart = PACKAGES_ROOT.length() + 1;
            int packageEnd = name.indexOf('/', packageStart);
            if (packageEnd == -1) {
                ImageLocation loc = findLocation(name);
                return loc != null ? completePackageDirectory(newDirectory(name), loc) : null;
            } else {
                // We cannot assume that because the given name was not cached, the
                // directory exists (the given name is untrusted and could reference
                // a non-existent link). However, *if* the parent directory *is*
                // present, we can conclude that the given name is not a valid link.
                String dirName = name.substring(0, packageEnd);
                if (!nodes.containsKey(dirName)) {
                    ImageLocation loc = findLocation(dirName);
                    if (loc != null) {
                        Directory dir = completePackageDirectory(newDirectory(dirName), loc);
                        // When the parent is created, its child nodes are cached.
                        nodes.put(dir.getName(), dir);
                        return nodes.get(name);
                    }
                }
            }
            return null;
        }

        /// Completes a directory by ensuring its child list is populated correctly.
        private void completeDirectory(Directory dir) {
            String name = dir.getName();
            // Since the node exists, we can assert that its name starts with
            // either "/modules" or "/packages", making differentiation easy. It
            // also means that the name is valid, so it must yield a location.
            assert name.startsWith(MODULES_ROOT) || name.startsWith(PACKAGES_ROOT);
            ImageLocation loc = findLocation(name);
            assert loc != null && name.equals(loc.getFullName()) : "Invalid location for name: " + name;
            // We cannot use 'isXxxSubdirectory()' methods here since we could
            // be given a top-level directory (for which that test doesn't work).
            // TODO (review note): I feel a bit dirty putting this test in, but it is fast and accurate.
            if (name.charAt(1) == 'm') {
                completeModuleDirectory(dir, loc);
            } else {
                completePackageDirectory(dir, loc);
            }
            assert dir.isCompleted() : "Directory must be complete by now: " + dir;
        }

        /// Completes a modules directory by setting the list of child nodes.
        ///
        /// The given directory can be the top level `/modules` directory, so
        /// it is NOT safe to use `isModulesSubdirectory(loc)` here.
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

        /// Completes a package directory by setting the list of child nodes.
        ///
        /// The given directory can be the top level `/packages` directory, so
        /// it is NOT safe to use `isPackagesSubdirectory(loc)` here.
        private Directory completePackageDirectory(Directory dir, ImageLocation loc) {
            assert dir.getName().equals(loc.getFullName()) : "Mismatched location for directory: " + dir;
            // The only directories in the "/packages" namespace are "/packages" or
            // "/packages/<package>". However, unlike "/modules" directories, the
            // location offsets mean different things.
            List<Node> children;
            if (dir.getName().equals(PACKAGES_ROOT)) {
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

        /// Creates the list of child nodes for a `Directory` based on a given
        /// node creation function.
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

        /// Helper to extract the integer offset buffer from a directory location.
        private IntBuffer getOffsetBuffer(ImageLocation dir) {
            assert isDirectory(dir) : "Not a directory: " + dir.getFullName();
            byte[] offsets = getResource(dir);
            ByteBuffer buffer = ByteBuffer.wrap(offsets);
            buffer.order(getByteOrder());
            return buffer.asIntBuffer();
        }

        /// Determines if an image location is a directory in the `/modules`
        /// namespace (if so, the location name is the Jrt filesystem name).
        ///
        /// In jimage, every `ImageLocation` under `/modules/` is a directory
        /// and has the same value for `getModule()`, and `getModuleOffset()`.
        private boolean isModulesSubdirectory(ImageLocation loc) {
            return loc.getModuleOffset() == modulesStringOffset;
        }

        /// Determines if an image location is a directory in the `/packages``
        /// namespace (if so, the location name is the Jrt filesystem name).
        ///
        /// In jimage, every `ImageLocation` under `/packages/` is a directory
        /// and has the same value for `getModule()`, and `getModuleOffset()`.
        private boolean isPackagesSubdirectory(ImageLocation loc) {
            return loc.getModuleOffset() == packagesStringOffset;
        }

        /// Determines if an image location represents a directory of some kind.
        private boolean isDirectory(ImageLocation loc) {
            return isModulesSubdirectory(loc) || isPackagesSubdirectory(loc) || loc.getModuleOffset() == 0;
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
        /// `findNode()`.
        private Directory newDirectory(String name) {
            return new Directory(name, imageFileAttributes());
        }

        /// Creates a new resource from an image location. This is the only case
        /// where the image location name does not match the requested node name.
        /// In image files, resource locations are NOT prefixed by `/modules`.
        private Resource newResource(String name, ImageLocation loc) {
            assert name.equals(loc.getFullName(true)) : "Mismatched location for resource: " + name;
            return new Resource(name, loc, imageFileAttributes());
        }

        /// Creates a new link node pointing at the given target name.
        ///
        /// Note that target node is resolved each time `resolve()` is called, so
        /// if a link node is retained after its reader is closed, it will fail.
        private LinkNode newLinkNode(String name, String targetName) {
            return new LinkNode(name, () -> findNode(targetName), imageFileAttributes());
        }

        /// Returns the content of a resource node.
        private byte[] getResource(Node node) throws IOException {
            // We could have been given a non-resource node here.
            if (node.isResource()) {
                return super.getResource(node.getLocation());
            }
            throw new IOException("Not a resource: " + node);
        }
    }

    /**
     * A directory, resource or symbolic link in the JRT file system namespace.
     */
    public abstract static class Node {
        private final String name;
        private final BasicFileAttributes fileAttrs;

        // Only visible for use by ExplodedImage.
        protected Node(String name, BasicFileAttributes fileAttrs) {
            this.name = Objects.requireNonNull(name);
            this.fileAttrs = Objects.requireNonNull(fileAttrs);
        }

        // A node is completed when all its direct children have been built.
        // As such, non-directory nodes are always complete.
        boolean isCompleted() {
            return true;
        }

        // Only resources can return a location.
        ImageLocation getLocation() {
            throw new IllegalArgumentException("not a resource: " + getName());
        }

        /**
         * Returns the JRT file system compatible name of this node (e.g.
         * {@code "/modules/java.base/java/lang/Object.class"} or {@code
         * "/packages/java.lang"}).
         */
        public final String getName() {
            return name;
        }

        /**
         * Returns file attributes for this node. The value returned may be the
         * same for all nodes, and should not be relied upon for accuracy.
         */
        public final BasicFileAttributes getFileAttributes() {
            return fileAttrs;
        }

        /**
         * Resolves a symbolic link to its target node. If this code is not a
         * symbolic link, then it resolves to itself.
         */
        public final Node resolveLink() {
            return resolveLink(false);
        }

        /**
         * Resolves a symbolic link to its target node. If this code is not a
         * symbolic link, then it resolves to itself.
         */
        public Node resolveLink(boolean recursive) {
            return this;
        }

        /** Returns whether this node is a symbolic link. */
        public boolean isLink() {
            return false;
        }

        /**
         * Returns whether this node is a directory. Directory nodes can have
         * {@link #getChildNames()} invoked to get the fully qualified names
         * of any child nodes.
         */
        public boolean isDirectory() {
            return false;
        }

        /**
         * Returns whether this node is a resource. Resource nodes can have
         * their contents obtained via {@link ImageReader#getResource(Node)}
         * or {@link ImageReader#getResourceBuffer(Node)}.
         */
        public boolean isResource() {
            return false;
        }

        // TODO (review note): Sure this could/should be IllegalStateException?
        /**
         * Returns the fully qualified names of any child nodes for a directory.
         *
         * <p>If this node is not a directory ({@code isDirectory() == false})
         * then this method will throw {@link IllegalArgumentException}.
         */
        public Stream<String> getChildNames() {
            throw new IllegalArgumentException("not a directory: " + getName());
        }

        /**
         * Returns the uncompressed size of this node's content. If this node is
         * not a resource, this method returns zero.
         */
        public long size() {
            return 0L;
        }

        /**
         * Returns the compressed size of this node's content. If this node is
         * not a resource, this method returns zero.
         */
        public long compressedSize() {
            return 0L;
        }

        /**
         * Returns the extension string of a resource node. If this node is not
         * a resource, this method returns null.
         */
        public String extension() {
            return null;
        }

        @Override
        public final String toString() {
            return getName();
        }

        ///  TODO (review note): In general, nodes are NOT comparable by name. They
        /// can differ depending on the reader they came from, and soon preview mode.
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
    /// When a directory node is returned by `findNode()` it is always complete,
    /// but this DOES NOT mean that its child nodes are complete yet.
    ///
    /// To avoid users being able to access incomplete child nodes, the
    /// `Node` API offers only a way to obtain child node names, forcing
    /// callers to invoke {@link ImageReader#findNode(String)} if they need to
    /// access the child node itself.
    ///
    /// This approach allows directories to be implemented lazily with respect
    /// to child nodes, while retaining efficiency when child nodes are accessed
    /// (since any incomplete nodes will be created and placed in the node cache
    /// when the parent was first returned to the user).
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

    /// Resource node (e.g. a ".class" entry, or any other data resource).
    ///
    /// Resources are leaf nodes referencing an underlying image location. They
    /// are lightweight, and do not cache their contents.
    ///
    /// Unlike directories (where the node name matches the jimage path for the
    /// corresponding `ImageLocation`), resource node names are NOT the same as
    /// the corresponding jimage path. The difference is that node names for
    /// resources are prefixed with "/modules", which is missing from the
    /// equivalent jimage path.
    private static class Resource extends Node {
        private final ImageLocation loc;

        private Resource(String name, ImageLocation loc, BasicFileAttributes fileAttrs) {
            super(name, fileAttrs);
            this.loc = loc;
        }

        @Override
        ImageLocation getLocation() {
            return loc;
        }

        @Override
        public boolean isResource() {
            return true;
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
    /// cache the result. Since nodes are cached by the `ImageReader`, this
    /// means that only the first call to `resolveLink()` could do any
    /// significant work.
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
