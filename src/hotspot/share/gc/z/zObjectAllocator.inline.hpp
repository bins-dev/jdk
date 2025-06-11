/*
 * Copyright (c) 2025, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
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

#ifndef SHARE_GC_Z_ZOBJECTALLOCATOR_INLINE_HPP
#define SHARE_GC_Z_ZOBJECTALLOCATOR_INLINE_HPP

#include "gc/z/zObjectAllocator.hpp"

#include "gc/z/zHeap.hpp"
#include "gc/z/zPageAge.inline.hpp"

inline ZObjectAllocator* ZObjectAllocator::allocator(ZPageAge age) {
  return _allocators->at((int)untype(age));
}

inline ZObjectAllocator* ZObjectAllocator::eden() {
  return allocator(ZPageAge::eden);
}

inline zaddress ZObjectAllocator::alloc_tlab(size_t size) {
  guarantee(size <= ZHeap::heap()->max_tlab_size(), "TLAB too large");
  return alloc_object(size);
}

inline void ZObjectAllocator::retire_pages(ZPageAgeRange range) {
  for (ZPageAge age : range) {
    _allocators->at((int)untype(age))->retire_pages();
  }
}

#endif // SHARE_GC_Z_ZOBJECTALLOCATOR_INLINE_HPP
