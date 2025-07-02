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

/**
 * @test
 * @bug 8360146
 * @summary Test Security property for disable PKCS1Padding against SunPKCS11
 *         provider
 * @library /test/lib ..
 * @run main/othervm TestPKCS1PaddingProp true
 * @run main/othervm TestPKCS1PaddingProp false
 * @run main/othervm TestPKCS1PaddingProp huh
 */

import java.util.List;
import java.security.NoSuchAlgorithmException;
import java.security.Provider;
import java.security.Security;
import javax.crypto.Cipher;
import javax.crypto.NoSuchPaddingException;

public class TestPKCS1PaddingProp extends PKCS11Test {

    private static final String PROP_NAME = "jdk.crypto.supportPKCS1Padding";

    private static void test(String alg, Provider p, boolean shouldThrow) {
        System.out.println("Testing " + p.getName() + ": " + alg +
                ", shouldThrow=" + shouldThrow);
        try {
            Cipher c = Cipher.getInstance(alg, p);
            if (shouldThrow) {
                throw new RuntimeException("Expected ex not thrown");
            }
        } catch (NoSuchAlgorithmException | NoSuchPaddingException e) {
            if (!shouldThrow) {
                throw new RuntimeException("Unexpected ex", e);
            }
        }
    }

    @Override
    public void main(Provider p) throws Exception {
        boolean shouldThrow =
                Security.getProperty(PROP_NAME).equalsIgnoreCase("false");
        for (String a : List.of("RSA/ECB/PKCS1Padding", "RSA")) {
            test(a, p, shouldThrow);
        }
        System.out.println("Done");
    }

    public static void main(String[] args) throws Exception {
        String propValue = args[0];
        System.out.println("Setting Security Prop " + PROP_NAME + " = " +
                propValue);
        Security.setProperty(PROP_NAME, propValue);
        main(new TestPKCS1PaddingProp(), args);
    }
}
