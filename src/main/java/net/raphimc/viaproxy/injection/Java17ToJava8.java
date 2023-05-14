/*
 * This file is part of ViaProxy - https://github.com/RaphiMC/ViaProxy
 * Copyright (C) 2023 RK_01/RaphiMC and contributors
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
package net.raphimc.viaproxy.injection;

import net.lenni0451.classtransform.TransformerManager;
import net.lenni0451.classtransform.transformer.IBytecodeTransformer;
import net.lenni0451.classtransform.utils.ASMUtils;
import net.lenni0451.classtransform.utils.tree.BasicClassProvider;
import net.lenni0451.classtransform.utils.tree.ClassTree;
import net.lenni0451.classtransform.utils.tree.IClassProvider;
import org.objectweb.asm.*;
import org.objectweb.asm.tree.*;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.File;
import java.nio.file.Files;
import java.util.*;

public class Java17ToJava8 implements IBytecodeTransformer {

    private static final Logger LOGGER = LoggerFactory.getLogger(Java17ToJava8.class);

    private static final boolean DEBUG_DUMP = Boolean.getBoolean("j17to8.dump");

    private static final char STACK_ARG_CONSTANT = '\u0001';
    private static final char BSM_ARG_CONSTANT = '\u0002';

    private static final String TRANSFER_TO_DESC = "(Ljava/io/InputStream;Ljava/io/OutputStream;)J";
    private static final String NEW_FILE_SYSTEM_DESC = "(Ljava/nio/file/Path;Ljava/util/Map;Ljava/lang/ClassLoader;)Ljava/nio/file/FileSystem;";

    private static final String EQUALS_DESC = "(Ljava/lang/Object;)Z";
    private static final String HASHCODE_DESC = "()I";
    private static final String TOSTRING_DESC = "()Ljava/lang/String;";
    private static final Map<String, String> PRIMITIVE_WRAPPERS = new HashMap<>();

    static {
        PRIMITIVE_WRAPPERS.put("V", Type.getInternalName(Void.class));
        PRIMITIVE_WRAPPERS.put("Z", Type.getInternalName(Boolean.class));
        PRIMITIVE_WRAPPERS.put("B", Type.getInternalName(Byte.class));
        PRIMITIVE_WRAPPERS.put("S", Type.getInternalName(Short.class));
        PRIMITIVE_WRAPPERS.put("C", Type.getInternalName(Character.class));
        PRIMITIVE_WRAPPERS.put("I", Type.getInternalName(Integer.class));
        PRIMITIVE_WRAPPERS.put("F", Type.getInternalName(Float.class));
        PRIMITIVE_WRAPPERS.put("J", Type.getInternalName(Long.class));
        PRIMITIVE_WRAPPERS.put("D", Type.getInternalName(Double.class));
    }

    private final ClassTree classTree;
    private final IClassProvider classProvider;
    private final int nativeClassVersion;
    private final List<String> whitelistedPackages = new ArrayList<>();

    public Java17ToJava8(final ClassTree classTree, final IClassProvider classProvider) {
        this.classTree = classTree;
        this.classProvider = classProvider;

        final String classVersion = System.getProperty("java.class.version");
        final String[] versions = classVersion.split("\\.");
        final int majorVersion = Integer.parseInt(versions[0]);
        final int minorVersion = Integer.parseInt(versions[1]);
        this.nativeClassVersion = minorVersion << 16 | majorVersion;
    }

    public Java17ToJava8(final TransformerManager transformerManager) {
        this(transformerManager.getClassTree(), transformerManager.getClassProvider());
    }

    public Java17ToJava8(final IClassProvider classProvider) {
        this(new ClassTree(), classProvider);
    }

    public Java17ToJava8(final ClassLoader loader) {
        this(new BasicClassProvider(loader));
    }

    public Java17ToJava8 addWhitelistedPackage(final String packageName) {
        this.whitelistedPackages.add(packageName);
        return this;
    }

    @Override
    public byte[] transform(final String className, final byte[] bytecode, final boolean calculateStackMapFrames) {
        if (!whitelistedPackages.isEmpty()) {
            int dotIndex = className.lastIndexOf('.');
            if (dotIndex == -1 && !whitelistedPackages.contains("")) return null;
            String pkg = className.substring(0, dotIndex);
            while (!whitelistedPackages.contains(pkg)) {
                dotIndex = pkg.lastIndexOf('.');
                if (dotIndex == -1) return null;
                pkg = pkg.substring(0, dotIndex);
            }
        }

        final ClassNode classNode = ASMUtils.fromBytes(bytecode);
        if (classNode.version <= this.nativeClassVersion) return null;

        classNode.version = Opcodes.V1_8;
        this.makePackagePrivate(classNode);
        this.convertStringConcatFactory(classNode);
        this.convertListMethods(classNode);
        this.convertSetMethods(classNode);
        this.convertMapMethods(classNode);
        this.convertStreamMethods(classNode);
        this.convertMiscMethods(classNode);
        this.convertRecords(classNode);

        if (calculateStackMapFrames) {
            final byte[] result;
            try {
                result = ASMUtils.toBytes(classNode, classTree, classProvider);
            } catch (Throwable t) {
                LOGGER.error("Failed to stack map downgraded class {}", className, t);
                throw t;
            }
            if (DEBUG_DUMP) {
                try {
                    final File file = new File("j17to8_dump", classNode.name + ".class");
                    file.getParentFile().mkdirs();
                    Files.write(file.toPath(), result);
                } catch (Throwable t) {
                    LOGGER.error("Failed to dump downgraded class {}", className, t);
                }
            }
            return result;
        } else {
            return ASMUtils.toStacklessBytes(classNode);
        }
    }

    private void makePackagePrivate(final ClassNode classNode) {
        // Java 9's NestHost system gives outer classes direct access to inner class members
        if (classNode.nestHostClass == null) return;
        for (final MethodNode methodNode : classNode.methods) {
            methodNode.access &= ~Opcodes.ACC_PRIVATE;
        }
        for (final FieldNode fieldNode : classNode.fields) {
            fieldNode.access &= ~Opcodes.ACC_PRIVATE;
        }
    }

    // Java 9+
    private void convertStringConcatFactory(final ClassNode node) {
        for (MethodNode method : node.methods) {
            for (AbstractInsnNode instruction : method.instructions.toArray()) {
                if (instruction.getOpcode() == Opcodes.INVOKEDYNAMIC) {
                    InvokeDynamicInsnNode insn = (InvokeDynamicInsnNode) instruction;
                    if (insn.bsm.getOwner().equals("java/lang/invoke/StringConcatFactory") && insn.bsm.getName().equals("makeConcatWithConstants")) {
                        String pattern = (String) insn.bsmArgs[0];
                        Type[] stackArgs = Type.getArgumentTypes(insn.desc);
                        Object[] bsmArgs = Arrays.copyOfRange(insn.bsmArgs, 1, insn.bsmArgs.length);
                        int stackArgsCount = count(pattern, STACK_ARG_CONSTANT);
                        int bsmArgsCount = count(pattern, BSM_ARG_CONSTANT);

                        if (stackArgs.length != stackArgsCount) throw new IllegalStateException("Stack args count does not match");
                        if (bsmArgs.length != bsmArgsCount) throw new IllegalStateException("BSM args count does not match");

                        int freeVarIndex = ASMUtils.getFreeVarIndex(method);
                        int[] stackIndices = new int[stackArgsCount];
                        for (int i = 0; i < stackArgs.length; i++) {
                            stackIndices[i] = freeVarIndex;
                            freeVarIndex += stackArgs[i].getSize();
                        }
                        for (int i = stackIndices.length - 1; i >= 0; i--) {
                            method.instructions.insertBefore(insn, new VarInsnNode(stackArgs[i].getOpcode(Opcodes.ISTORE), stackIndices[i]));
                        }

                        InsnList converted = convertStringConcatFactory(pattern, stackArgs, stackIndices, bsmArgs);
                        method.instructions.insertBefore(insn, converted);
                        method.instructions.remove(insn);
                    }
                }
            }
        }
    }

    private void convertListMethods(final ClassNode node) {
        for (MethodNode method : node.methods) {
            for (AbstractInsnNode insn : method.instructions.toArray()) {
                if (insn.getOpcode() == Opcodes.INVOKESTATIC) {
                    final MethodInsnNode min = (MethodInsnNode) insn;
                    if (!min.owner.equals("java/util/List")) continue;

                    final InsnList list = new InsnList();

                    // Java 9+
                    if (min.name.equals("of")) {
                        final Type[] args = Type.getArgumentTypes(min.desc);
                        if (args.length != 1 || args[0].getSort() != Type.ARRAY) {
                            int freeVarIndex = ASMUtils.getFreeVarIndex(method);

                            int argCount = args.length;
                            list.add(new TypeInsnNode(Opcodes.NEW, "java/util/ArrayList"));
                            list.add(new InsnNode(Opcodes.DUP));
                            list.add(new MethodInsnNode(Opcodes.INVOKESPECIAL, "java/util/ArrayList", "<init>", "()V"));
                            list.add(new VarInsnNode(Opcodes.ASTORE, freeVarIndex));
                            for (int i = 0; i < argCount; i++) {
                                list.add(new VarInsnNode(Opcodes.ALOAD, freeVarIndex));
                                list.add(new InsnNode(Opcodes.SWAP));
                                list.add(new MethodInsnNode(Opcodes.INVOKEINTERFACE, "java/util/List", "add", "(Ljava/lang/Object;)Z"));
                                list.add(new InsnNode(Opcodes.POP));
                            }
                            list.add(new VarInsnNode(Opcodes.ALOAD, freeVarIndex));
                            list.add(new InsnNode(Opcodes.DUP));
                            list.add(new MethodInsnNode(
                                Opcodes.INVOKESTATIC,
                                "java/util/Collections",
                                "reverse",
                                "(Ljava/util/List;)V"
                            ));
                            list.add(new MethodInsnNode(Opcodes.INVOKESTATIC, "java/util/Collections", "unmodifiableList", "(Ljava/util/List;)Ljava/util/List;"));
                        }
                    // Java 10+
                    } else if (min.name.equals("copyOf")) {
                        list.add(new TypeInsnNode(Opcodes.NEW, "java/util/ArrayList"));
                        list.add(new InsnNode(Opcodes.DUP_X1));
                        list.add(new InsnNode(Opcodes.SWAP));
                        list.add(new MethodInsnNode(Opcodes.INVOKESPECIAL, "java/util/ArrayList", "<init>", "(Ljava/util/Collection;)V"));
                        list.add(new MethodInsnNode(Opcodes.INVOKESTATIC, "java/util/Collections", "unmodifiableList", "(Ljava/util/List;)Ljava/util/List;"));
                    }

                    if (list.size() != 0) {
                        method.instructions.insertBefore(insn, list);
                        method.instructions.remove(insn);
                    }
                }
            }
        }
    }

    private void convertSetMethods(final ClassNode node) {
        for (MethodNode method : node.methods) {
            for (AbstractInsnNode insn : method.instructions.toArray()) {
                if (insn.getOpcode() == Opcodes.INVOKESTATIC) {
                    final MethodInsnNode min = (MethodInsnNode) insn;
                    if (!min.owner.equals("java/util/Set")) continue;

                    final InsnList list = new InsnList();

                    // Java 9+
                    if (min.name.equals("of")) {
                        final Type[] args = Type.getArgumentTypes(min.desc);
                        if (args.length != 1 || args[0].getSort() != Type.ARRAY) {
                            int freeVarIndex = ASMUtils.getFreeVarIndex(method);

                            int argCount = args.length;
                            list.add(new TypeInsnNode(Opcodes.NEW, "java/util/HashSet"));
                            list.add(new InsnNode(Opcodes.DUP));
                            list.add(new MethodInsnNode(Opcodes.INVOKESPECIAL, "java/util/HashSet", "<init>", "()V"));
                            list.add(new VarInsnNode(Opcodes.ASTORE, freeVarIndex));
                            for (int i = 0; i < argCount; i++) {
                                list.add(new VarInsnNode(Opcodes.ALOAD, freeVarIndex));
                                list.add(new InsnNode(Opcodes.SWAP));
                                list.add(new MethodInsnNode(Opcodes.INVOKEINTERFACE, "java/util/Set", "add", "(Ljava/lang/Object;)Z"));
                                list.add(new InsnNode(Opcodes.POP));
                            }
                            list.add(new VarInsnNode(Opcodes.ALOAD, freeVarIndex));
                            list.add(new MethodInsnNode(Opcodes.INVOKESTATIC, "java/util/Collections", "unmodifiableSet", "(Ljava/util/Set;)Ljava/util/Set;"));
                        }
                    // Java 10+
                    } else if (min.name.equals("copyOf")) {
                        list.add(new TypeInsnNode(Opcodes.NEW, "java/util/HashSet"));
                        list.add(new InsnNode(Opcodes.DUP_X1));
                        list.add(new InsnNode(Opcodes.SWAP));
                        list.add(new MethodInsnNode(Opcodes.INVOKESPECIAL, "java/util/HashSet", "<init>", "(Ljava/util/Collection;)V"));
                        list.add(new MethodInsnNode(Opcodes.INVOKESTATIC, "java/util/Collections", "unmodifiableSet", "(Ljava/util/Set;)Ljava/util/Set;"));
                    }

                    if (list.size() != 0) {
                        method.instructions.insertBefore(insn, list);
                        method.instructions.remove(insn);
                    }
                }
            }
        }
    }

    private void convertMapMethods(final ClassNode node) {
        for (MethodNode method : node.methods) {
            for (AbstractInsnNode insn : method.instructions.toArray()) {
                if (insn.getOpcode() == Opcodes.INVOKESTATIC) {
                    final MethodInsnNode min = (MethodInsnNode) insn;
                    if (!min.owner.equals("java/util/Map")) continue;

                    final InsnList list = new InsnList();

                    // Java 9+
                    if (min.name.equals("of")) {
                        final Type[] args = Type.getArgumentTypes(min.desc);
                        if (args.length != 1 || args[0].getSort() != Type.ARRAY) {
                            int freeVarIndex = ASMUtils.getFreeVarIndex(method);

                            int argCount = args.length;
                            if (argCount % 2 != 0) {
                                throw new RuntimeException("Map.of() requires an even number of arguments");
                            }

                            list.add(new TypeInsnNode(Opcodes.NEW, "java/util/HashMap"));
                            list.add(new InsnNode(Opcodes.DUP));
                            list.add(new MethodInsnNode(Opcodes.INVOKESPECIAL, "java/util/HashMap", "<init>", "()V"));
                            list.add(new VarInsnNode(Opcodes.ASTORE, freeVarIndex));
                            for (int i = 0; i < argCount / 2; i++) {
                                list.add(new VarInsnNode(Opcodes.ALOAD, freeVarIndex));
                                list.add(new InsnNode(Opcodes.DUP_X2));
                                list.add(new InsnNode(Opcodes.POP));
                                list.add(new MethodInsnNode(Opcodes.INVOKEINTERFACE, "java/util/Map", "put", "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;"));
                                list.add(new InsnNode(Opcodes.POP));
                            }
                            list.add(new VarInsnNode(Opcodes.ALOAD, freeVarIndex));
                            list.add(new MethodInsnNode(Opcodes.INVOKESTATIC, "java/util/Collections", "unmodifiableMap", "(Ljava/util/Map;)Ljava/util/Map;"));
                        }
                    // Java 10+
                    } else if (min.name.equals("copyOf")) {
                        list.add(new TypeInsnNode(Opcodes.NEW, "java/util/HashMap"));
                        list.add(new InsnNode(Opcodes.DUP_X1));
                        list.add(new InsnNode(Opcodes.SWAP));
                        list.add(new MethodInsnNode(Opcodes.INVOKESPECIAL, "java/util/HashMap", "<init>", "(Ljava/util/Map;)V"));
                        list.add(new MethodInsnNode(Opcodes.INVOKESTATIC, "java/util/Collections", "unmodifiableMap", "(Ljava/util/Map;)Ljava/util/Map;"));
                    }

                    if (list.size() != 0) {
                        method.instructions.insertBefore(insn, list);
                        method.instructions.remove(insn);
                    }
                }
            }
        }
    }

    private void convertStreamMethods(final ClassNode node) {
        for (MethodNode method : node.methods) {
            for (AbstractInsnNode insn : method.instructions.toArray()) {
                if (insn.getOpcode() == Opcodes.INVOKEINTERFACE) {
                    final MethodInsnNode min = (MethodInsnNode) insn;
                    if (!min.owner.equals("java/util/stream/Stream")) continue;

                    final InsnList list = new InsnList();

                    // Java 16+
                    if (min.name.equals("toList")) {
                        list.add(new MethodInsnNode(
                            Opcodes.INVOKESTATIC,
                            "java/util/stream/Collectors",
                            "toList",
                            "()Ljava/util/stream/Collector;"
                        ));
                        list.add(new MethodInsnNode(
                            Opcodes.INVOKEINTERFACE,
                            "java/util/stream/Stream",
                            "collect",
                            "(Ljava/util/stream/Collector;)Ljava/lang/Object;"
                        ));
                        list.add(new TypeInsnNode(Opcodes.CHECKCAST, "java/util/List"));
                        list.add(new MethodInsnNode(
                            Opcodes.INVOKESTATIC,
                            "java/util/Collections",
                            "unmodifiableList",
                            "(Ljava/util/List;)Ljava/util/List;")
                        );
                    }

                    if (list.size() != 0) {
                        method.instructions.insertBefore(insn, list);
                        method.instructions.remove(insn);
                    }
                }
            }
        }
    }

    private static String findMethodName(ClassNode node, String name, String descriptor) {
        String foundName;
        {
            int i = 0;
            do {
                foundName = name + '$' + i;
            } while (ASMUtils.getMethod(node, foundName, TRANSFER_TO_DESC) != null);
        }
        return foundName;
    }

    private void convertMiscMethods(final ClassNode node) {
        String transferToName = null;
        String newFileSystemName = null;

        for (MethodNode method : node.methods) {
            for (AbstractInsnNode insn : method.instructions.toArray()) {
                if (insn instanceof MethodInsnNode) {
                    final MethodInsnNode min = (MethodInsnNode) insn;
                    final InsnList list = new InsnList();

                    if (min.owner.equals("java/lang/String")) {
                        // Java 11+
                        if (min.name.equals("isBlank") && min.getOpcode() == Opcodes.INVOKEVIRTUAL) {
                            list.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, "java/lang/String", "trim", "()Ljava/lang/String;"));
                            list.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, "java/lang/String", "isEmpty", "()Z"));
                        }
                    } else if (min.owner.equals("java/io/InputStream")) {
                        // Java 9+
                        if (min.name.equals("readAllBytes") && min.getOpcode() == Opcodes.INVOKEVIRTUAL) {
                            if (transferToName == null) {
                                transferToName = findMethodName(node, "transferTo", TRANSFER_TO_DESC);
                            }
                            list.add(new TypeInsnNode(Opcodes.NEW, "java/io/ByteArrayOutputStream"));
                            list.add(new InsnNode(Opcodes.DUP));
                            list.add(new MethodInsnNode(
                                Opcodes.INVOKESPECIAL,
                                "java/io/ByteArrayOutputStream",
                                "<init>",
                                "()V"
                            ));
                            list.add(new InsnNode(Opcodes.DUP_X1));
                            list.add(new MethodInsnNode(
                                Opcodes.INVOKESTATIC,
                                node.name,
                                transferToName,
                                TRANSFER_TO_DESC
                            ));
                            list.add(new InsnNode(Opcodes.POP2));
                            list.add(new MethodInsnNode(
                                Opcodes.INVOKEVIRTUAL,
                                "java/io/ByteArrayOutputStream",
                                "toByteArray",
                                "()[B"
                            ));
                        // Java 9+
                        } else if (min.name.equals("transferTo") && min.getOpcode() == Opcodes.INVOKEVIRTUAL) {
                            if (transferToName == null) {
                                transferToName = findMethodName(node, "transferTo", TRANSFER_TO_DESC);
                            }
                            list.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                                node.name,
                                transferToName,
                                TRANSFER_TO_DESC
                            ));
                        }
                    } else if (min.owner.equals("java/nio/file/FileSystems")) {
                        if (min.name.equals("newFileSystem") && min.desc.equals(NEW_FILE_SYSTEM_DESC)) {
                            if (newFileSystemName == null) {
                                newFileSystemName = findMethodName(node, "newFileSystem", NEW_FILE_SYSTEM_DESC);
                            }
                            list.add(new MethodInsnNode(
                                Opcodes.INVOKESTATIC,
                                node.name,
                                newFileSystemName,
                                NEW_FILE_SYSTEM_DESC
                            ));
                        }
                    } else if (min.owner.equals("java/util/Objects")) {
                        if (min.name.equals("requireNonNullElse")) {
                            LabelNode elseJump = new LabelNode();
                            LabelNode endJump = new LabelNode();

                            list.add(new InsnNode(Opcodes.SWAP));
                            list.add(new InsnNode(Opcodes.DUP));
                            list.add(new JumpInsnNode(Opcodes.IFNULL, elseJump));
                            list.add(new InsnNode(Opcodes.SWAP));
                            list.add(new InsnNode(Opcodes.POP));
                            list.add(new JumpInsnNode(Opcodes.GOTO, endJump));
                            list.add(elseJump);
                            list.add(new InsnNode(Opcodes.POP));
                            list.add(new LdcInsnNode("defaultObj"));
                            list.add(new MethodInsnNode(Opcodes.INVOKESTATIC, "java/util/Objects", "requireNonNull", "(Ljava/lang/Object;Ljava/lang/String;)Ljava/lang/Object;"));
                            list.add(endJump);
                        }
                    } else if (min.owner.equals("java/nio/file/Files")) {
                        if (min.name.equals("readString")) {
                            if (min.desc.equals("(Ljava/nio/file/Path;)Ljava/lang/String;")) {
                                list.add(new MethodInsnNode(Opcodes.INVOKESTATIC, "java/nio/file/Files", "readAllBytes", "(Ljava/nio/file/Path;)[B"));
                                list.add(new FieldInsnNode(Opcodes.GETSTATIC, "java/nio/charset/StandardCharsets", "UTF_8", "Ljava/nio/charset/Charset;"));
                            } else if (min.desc.equals("(Ljava/nio/file/Path;Ljava/nio/charset/Charset;)Ljava/lang/String;")) {
                                list.add(new InsnNode(Opcodes.SWAP));
                                list.add(new MethodInsnNode(Opcodes.INVOKESTATIC, "java/nio/file/Files", "readAllBytes", "(Ljava/nio/file/Path;)[B"));
                                list.add(new InsnNode(Opcodes.SWAP));
                            }
                            list.add(new TypeInsnNode(Opcodes.NEW, "java/lang/String"));
                            list.add(new InsnNode(Opcodes.DUP_X2));
                            list.add(new InsnNode(Opcodes.DUP_X2));
                            list.add(new InsnNode(Opcodes.POP));
                            list.add(new MethodInsnNode(Opcodes.INVOKESPECIAL, "java/lang/String", "<init>", "([BLjava/nio/charset/Charset;)V"));
                        }
                    } else if (min.owner.equals("java/util/regex/Matcher")) {
                        if (min.name.equals("appendReplacement") && min.desc.equals("(Ljava/lang/StringBuilder;Ljava/lang/String;)Ljava/util/regex/Matcher;")) {
                            int stringBufferIndex = ASMUtils.getFreeVarIndex(method);
                            list.add(new TypeInsnNode(Opcodes.NEW, "java/lang/StringBuffer"));
                            list.add(new InsnNode(Opcodes.DUP));
                            list.add(new MethodInsnNode(Opcodes.INVOKESPECIAL, "java/lang/StringBuffer", "<init>", "()V"));
                            list.add(new VarInsnNode(Opcodes.ASTORE, stringBufferIndex));

                            list.add(new InsnNode(Opcodes.DUP2_X1));
                            list.add(new InsnNode(Opcodes.POP2));
                            list.add(new InsnNode(Opcodes.SWAP));
                            list.add(new VarInsnNode(Opcodes.ALOAD, stringBufferIndex));
                            list.add(new InsnNode(Opcodes.SWAP));
                            list.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, min.owner, min.name, "(Ljava/lang/StringBuffer;Ljava/lang/String;)Ljava/util/regex/Matcher;"));
                            list.add(new InsnNode(Opcodes.SWAP));
                            list.add(new VarInsnNode(Opcodes.ALOAD, stringBufferIndex));
                            list.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, "java/lang/StringBuilder", "append", "(Ljava/lang/StringBuffer;)Ljava/lang/StringBuilder;"));
                            list.add(new InsnNode(Opcodes.POP));
                        } else if (min.name.equals("appendTail") && min.desc.equals("(Ljava/lang/StringBuilder;)Ljava/lang/StringBuilder;")) {
                            int stringBufferIndex = ASMUtils.getFreeVarIndex(method);
                            list.add(new TypeInsnNode(Opcodes.NEW, "java/lang/StringBuffer"));
                            list.add(new InsnNode(Opcodes.DUP));
                            list.add(new MethodInsnNode(Opcodes.INVOKESPECIAL, "java/lang/StringBuffer", "<init>", "()V"));
                            list.add(new VarInsnNode(Opcodes.ASTORE, stringBufferIndex));

                            list.add(new InsnNode(Opcodes.SWAP));
                            list.add(new VarInsnNode(Opcodes.ALOAD, stringBufferIndex));
                            list.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, min.owner, min.name, "(Ljava/lang/StringBuffer;)Ljava/lang/StringBuffer;"));
                            list.add(new InsnNode(Opcodes.SWAP));
                            list.add(new VarInsnNode(Opcodes.ALOAD, stringBufferIndex));
                            list.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, "java/lang/StringBuilder", "append", "(Ljava/lang/StringBuffer;)Ljava/lang/StringBuilder;"));
                            list.add(new InsnNode(Opcodes.POP));
                        }
                    }

                    if (list.size() != 0) {
                        method.instructions.insertBefore(insn, list);
                        method.instructions.remove(insn);
                    }
                }
            }
        }

        if (transferToName != null) {
            generateTransferTo(transferToName, node);
        }
        if (newFileSystemName != null) {
            generateNewFileSystem(newFileSystemName, node);
        }
    }

    private static void generateTransferTo(String name, ClassVisitor visitor) {
        final MethodVisitor transferTo = visitor.visitMethod(
            Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC | Opcodes.ACC_SYNTHETIC,
            name, TRANSFER_TO_DESC, null, new String[] {"java/io/IOException"}
        );
        transferTo.visitCode();

        // Objects.requireNonNull(out, "out");
        transferTo.visitVarInsn(Opcodes.ALOAD, 1);
        transferTo.visitLdcInsn("out");
        transferTo.visitMethodInsn(
            Opcodes.INVOKESTATIC,
            "java/util/Objects",
            "requireNonNull",
            "(Ljava/lang/Object;Ljava/lang/String;)Ljava/lang/Object;",
            false
        );
        transferTo.visitInsn(Opcodes.POP);

        // long transferred = 0;
        transferTo.visitInsn(Opcodes.LCONST_0);
        transferTo.visitVarInsn(Opcodes.LSTORE, 2);

        // byte[] buffer = new byte[DEFAULT_BUFFER_SIZE];
        transferTo.visitIntInsn(Opcodes.SIPUSH, 8192);
        transferTo.visitIntInsn(Opcodes.NEWARRAY, Opcodes.T_BYTE);
        transferTo.visitVarInsn(Opcodes.ASTORE, 4);

        // while ((read = this.read(buffer, 0, DEFAULT_BUFFER_SIZE)) >= 0) {
        final Label whileStart = new Label();
        final Label whileEnd = new Label();
        transferTo.visitLabel(whileStart);
        transferTo.visitVarInsn(Opcodes.ALOAD, 0);
        transferTo.visitVarInsn(Opcodes.ALOAD, 4);
        transferTo.visitInsn(Opcodes.ICONST_0);
        transferTo.visitIntInsn(Opcodes.SIPUSH, 8192);
        transferTo.visitMethodInsn(
            Opcodes.INVOKEVIRTUAL,
            "java/io/InputStream",
            "read",
            "([BII)I",
            false
        );
        transferTo.visitInsn(Opcodes.DUP);
        transferTo.visitVarInsn(Opcodes.ISTORE, 5);
        transferTo.visitJumpInsn(Opcodes.IFLT, whileEnd);

        // out.write(buffer, 0, read);
        transferTo.visitVarInsn(Opcodes.ALOAD, 1);
        transferTo.visitVarInsn(Opcodes.ALOAD, 4);
        transferTo.visitInsn(Opcodes.ICONST_0);
        transferTo.visitVarInsn(Opcodes.ILOAD, 5);
        transferTo.visitMethodInsn(
            Opcodes.INVOKEVIRTUAL,
            "java/io/OutputStream",
            "write",
            "([BII)V",
            false
        );

        // transferred += read;
        transferTo.visitVarInsn(Opcodes.LLOAD, 2);
        transferTo.visitVarInsn(Opcodes.ILOAD, 5);
        transferTo.visitInsn(Opcodes.I2L);
        transferTo.visitInsn(Opcodes.LADD);
        transferTo.visitVarInsn(Opcodes.LSTORE, 2);

        // }
        transferTo.visitJumpInsn(Opcodes.GOTO, whileStart);
        transferTo.visitLabel(whileEnd);

        // return transferred;
        transferTo.visitVarInsn(Opcodes.LLOAD, 2);
        transferTo.visitInsn(Opcodes.LRETURN);

        transferTo.visitEnd();
    }

    private static void generateNewFileSystem(String name, ClassVisitor visitor) {
        final MethodVisitor newFileSystem = visitor.visitMethod(
            Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC | Opcodes.ACC_SYNTHETIC,
            name, NEW_FILE_SYSTEM_DESC, null, new String[] {"java/io/IOException"}
        );
        newFileSystem.visitCode();

        // if (path == null)
        newFileSystem.visitVarInsn(Opcodes.ALOAD, 0);
        final Label if1Label = new Label();
        newFileSystem.visitJumpInsn(Opcodes.IFNONNULL, if1Label);

        // throw new NullPointerException();
        newFileSystem.visitTypeInsn(Opcodes.NEW, "java/lang/NullPointerException");
        newFileSystem.visitInsn(Opcodes.DUP);
        newFileSystem.visitMethodInsn(
            Opcodes.INVOKESPECIAL,
            "java/lang/NullPointerException",
            "<init>",
            "()V",
            false
        );
        newFileSystem.visitInsn(Opcodes.ATHROW);

        newFileSystem.visitLabel(if1Label);

        // for (FileSystemProvider provider: FileSystemProvider.installedProviders()) {
        newFileSystem.visitMethodInsn(
            Opcodes.INVOKESTATIC,
            "java/nio/file/spi/FileSystemProvider",
            "installedProviders",
            "()Ljava/util/List;",
            false
        );
        newFileSystem.visitMethodInsn(
            Opcodes.INVOKEINTERFACE,
            "java/util/List",
            "iterator",
            "()Ljava/util/Iterator;",
            true
        );
        newFileSystem.visitVarInsn(Opcodes.ASTORE, 3);
        final Label for1StartLabel = new Label();
        newFileSystem.visitLabel(for1StartLabel);
        newFileSystem.visitVarInsn(Opcodes.ALOAD, 3);
        newFileSystem.visitMethodInsn(
            Opcodes.INVOKEINTERFACE,
            "java/util/Iterator",
            "hasNext",
            "()Z",
            true
        );
        final Label for1EndLabel = new Label();
        newFileSystem.visitJumpInsn(Opcodes.IFEQ, for1EndLabel);
        newFileSystem.visitVarInsn(Opcodes.ALOAD, 3);
        newFileSystem.visitMethodInsn(
            Opcodes.INVOKEINTERFACE,
            "java/util/Iterator",
            "next",
            "()Ljava/lang/Object;",
            true
        );
        newFileSystem.visitTypeInsn(Opcodes.CHECKCAST, "java/nio/file/spi/FileSystemProvider");
        newFileSystem.visitVarInsn(Opcodes.ASTORE, 4);

        // try {
        final Label try1Start = new Label();
        final Label try1End = new Label();
        final Label try1Handler = new Label();
        newFileSystem.visitTryCatchBlock(try1Start, try1End, try1Handler, "java/lang/UnsupportedOperationException");
        newFileSystem.visitLabel(try1Start);

        // return provider.newFileSystem(path, env);
        newFileSystem.visitVarInsn(Opcodes.ALOAD, 4);
        newFileSystem.visitVarInsn(Opcodes.ALOAD, 0);
        newFileSystem.visitVarInsn(Opcodes.ALOAD, 1);
        newFileSystem.visitMethodInsn(
            Opcodes.INVOKEVIRTUAL,
            "java/nio/file/spi/FileSystemProvider",
            "newFileSystem",
            "(Ljava/nio/file/Path;Ljava/util/Map;)Ljava/nio/file/FileSystem;",
            false
        );
        newFileSystem.visitInsn(Opcodes.ARETURN);

        // } catch (UnsupportedOperationException uoe) {
        newFileSystem.visitLabel(try1End);
        newFileSystem.visitLabel(try1Handler);

        // }
        newFileSystem.visitInsn(Opcodes.POP);

        // }
        newFileSystem.visitJumpInsn(Opcodes.GOTO, for1StartLabel);
        newFileSystem.visitLabel(for1EndLabel);

        // if (loader != null) {
        newFileSystem.visitVarInsn(Opcodes.ALOAD, 2);
        final Label if2Label = new Label();
        newFileSystem.visitJumpInsn(Opcodes.IFNULL, if2Label);

        // ServiceLoader<FileSystemProvider> sl = ServiceLoader.load(FileSystemProvider.class, loader);
        newFileSystem.visitLdcInsn(Type.getObjectType("java/nio/file/spi/FileSystemProvider"));
        newFileSystem.visitVarInsn(Opcodes.ALOAD, 2);
        newFileSystem.visitMethodInsn(
            Opcodes.INVOKESTATIC,
            "java/util/ServiceLoader",
            "load",
            "(Ljava/lang/Class;Ljava/lang/ClassLoader;)Ljava/util/ServiceLoader;",
            false
        );
        newFileSystem.visitVarInsn(Opcodes.ASTORE, 3);

        // for (FileSystemProvider provider: sl) {
        newFileSystem.visitVarInsn(Opcodes.ALOAD, 3);
        newFileSystem.visitMethodInsn(
            Opcodes.INVOKEINTERFACE,
            "java/util/ServiceLoader",
            "iterator",
            "()Ljava/util/Iterator;",
            true
        );
        newFileSystem.visitVarInsn(Opcodes.ASTORE, 4);
        final Label for2StartLabel = new Label();
        newFileSystem.visitLabel(for2StartLabel);
        newFileSystem.visitVarInsn(Opcodes.ALOAD, 4);
        newFileSystem.visitMethodInsn(
            Opcodes.INVOKEINTERFACE,
            "java/util/Iterator",
            "hasNext",
            "()Z",
            true
        );
        final Label for2EndLabel = new Label();
        newFileSystem.visitJumpInsn(Opcodes.IFEQ, for2EndLabel);
        newFileSystem.visitVarInsn(Opcodes.ALOAD, 4);
        newFileSystem.visitMethodInsn(
            Opcodes.INVOKEINTERFACE,
            "java/util/Iterator",
            "next",
            "()Ljava/lang/Object;",
            true
        );
        newFileSystem.visitTypeInsn(Opcodes.CHECKCAST, "java/nio/file/spi/FileSystemProvider");
        newFileSystem.visitVarInsn(Opcodes.ASTORE, 5);

        // try {
        final Label try2Start = new Label();
        final Label try2End = new Label();
        final Label try2Handler = new Label();
        newFileSystem.visitTryCatchBlock(try2Start, try2End, try2Handler, "java/lang/UnsupportedOperationException");
        newFileSystem.visitLabel(try2Start);

        // return provider.newFileSystem(path, env);
        newFileSystem.visitVarInsn(Opcodes.ALOAD, 5);
        newFileSystem.visitVarInsn(Opcodes.ALOAD, 0);
        newFileSystem.visitVarInsn(Opcodes.ALOAD, 1);
        newFileSystem.visitMethodInsn(
            Opcodes.INVOKEVIRTUAL,
            "java/nio/file/spi/FileSystemProvider",
            "newFileSystem",
            "(Ljava/nio/file/Path;Ljava/util/Map;)Ljava/nio/file/FileSystem;",
            false
        );
        newFileSystem.visitInsn(Opcodes.ARETURN);

        // } catch (UnsupportedOperationException uoe) {
        newFileSystem.visitLabel(try2End);
        newFileSystem.visitLabel(try2Handler);

        // }
        newFileSystem.visitInsn(Opcodes.POP);

        // }
        newFileSystem.visitJumpInsn(Opcodes.GOTO, for2StartLabel);
        newFileSystem.visitLabel(for2EndLabel);

        // }
        newFileSystem.visitLabel(if2Label);

        // throw new ProviderNotFoundException("Provider not found");
        newFileSystem.visitTypeInsn(Opcodes.NEW, "java/nio/file/ProviderNotFoundException");
        newFileSystem.visitInsn(Opcodes.DUP);
        newFileSystem.visitLdcInsn("Provider not found");
        newFileSystem.visitMethodInsn(
            Opcodes.INVOKESPECIAL,
            "java/nio/file/ProviderNotFoundException",
            "<init>",
            "(Ljava/lang/String;)V",
            false
        );
        newFileSystem.visitInsn(Opcodes.ATHROW);

        newFileSystem.visitEnd();
    }

    private void convertRecords(final ClassNode node) {
        if (!node.superName.equals("java/lang/Record")) return;

        node.access &= ~Opcodes.ACC_RECORD;
        node.superName = "java/lang/Object";

        final List<MethodNode> constructors = ASMUtils.getMethodsFromCombi(node, "<init>");
        for (MethodNode method : constructors) {
            for (AbstractInsnNode insn : method.instructions.toArray()) {
                if (insn.getOpcode() == Opcodes.INVOKESPECIAL) {
                    MethodInsnNode min = (MethodInsnNode) insn;
                    if (min.owner.equals("java/lang/Record")) {
                        min.owner = "java/lang/Object";
                        break;
                    }
                }
            }
        }

        node.methods.remove(ASMUtils.getMethod(node, "equals", EQUALS_DESC));
        final MethodVisitor equals = node.visitMethod(Opcodes.ACC_PUBLIC, "equals", EQUALS_DESC, null, null);
        {
            equals.visitCode();

            equals.visitVarInsn(Opcodes.ALOAD, 0);
            equals.visitVarInsn(Opcodes.ALOAD, 1);
            final Label notSameLabel = new Label();
            equals.visitJumpInsn(Opcodes.IF_ACMPNE, notSameLabel);
            equals.visitInsn(Opcodes.ICONST_1);
            equals.visitInsn(Opcodes.IRETURN);
            equals.visitLabel(notSameLabel);

            // Original uses Class.isInstance, but I think instanceof is more fitting here
            equals.visitVarInsn(Opcodes.ALOAD, 1);
            equals.visitTypeInsn(Opcodes.INSTANCEOF, node.name);
            final Label notIsInstanceLabel = new Label();
            equals.visitJumpInsn(Opcodes.IFNE, notIsInstanceLabel);
            equals.visitInsn(Opcodes.ICONST_0);
            equals.visitInsn(Opcodes.IRETURN);
            equals.visitLabel(notIsInstanceLabel);

            equals.visitVarInsn(Opcodes.ALOAD, 1);
            equals.visitTypeInsn(Opcodes.CHECKCAST, node.name);
            equals.visitVarInsn(Opcodes.ASTORE, 2);

            final Label notEqualLabel = new Label();
            for (final RecordComponentNode component : node.recordComponents) {
                equals.visitVarInsn(Opcodes.ALOAD, 0);
                equals.visitFieldInsn(Opcodes.GETFIELD, node.name, component.name, component.descriptor);
                equals.visitVarInsn(Opcodes.ALOAD, 2);
                equals.visitFieldInsn(Opcodes.GETFIELD, node.name, component.name, component.descriptor);
                if (Type.getType(component.descriptor).getSort() >= Type.ARRAY) { // ARRAY or OBJECT
                    equals.visitMethodInsn(
                        Opcodes.INVOKESTATIC,
                        Type.getInternalName(Objects.class),
                        "equals",
                        "(Ljava/lang/Object;Ljava/lang/Object;)Z",
                        false
                    );
                    equals.visitJumpInsn(Opcodes.IFEQ, notEqualLabel);
                    continue;
                } else if ("BSCIZ".contains(component.descriptor)) {
                    equals.visitJumpInsn(Opcodes.IF_ICMPNE, notEqualLabel);
                    continue;
                } else if (component.descriptor.equals("F")) {
                    equals.visitMethodInsn(
                        Opcodes.INVOKESTATIC,
                        Type.getInternalName(Float.class),
                        "equals",
                        "(FF)Z",
                        false
                    );
                } else if (component.descriptor.equals("D")) {
                    equals.visitMethodInsn(
                        Opcodes.INVOKESTATIC,
                        Type.getInternalName(Double.class),
                        "equals",
                        "(DD)Z",
                        false
                    );
                } else if (component.descriptor.equals("J")) {
                    equals.visitInsn(Opcodes.LCMP);
                } else {
                    throw new AssertionError("Unknown descriptor " + component.descriptor);
                }
                equals.visitJumpInsn(Opcodes.IFNE, notEqualLabel);
            }
            equals.visitInsn(Opcodes.ICONST_1);
            equals.visitInsn(Opcodes.IRETURN);
            equals.visitLabel(notEqualLabel);
            equals.visitInsn(Opcodes.ICONST_0);
            equals.visitInsn(Opcodes.IRETURN);

            equals.visitEnd();
        }

        node.methods.remove(ASMUtils.getMethod(node, "hashCode", HASHCODE_DESC));
        final MethodVisitor hashCode = node.visitMethod(Opcodes.ACC_PUBLIC, "hashCode", HASHCODE_DESC, null, null);
        {
            hashCode.visitCode();

            hashCode.visitInsn(Opcodes.ICONST_0);
            for (final RecordComponentNode component : node.recordComponents) {
                hashCode.visitIntInsn(Opcodes.BIPUSH, 31);
                hashCode.visitInsn(Opcodes.IMUL);
                hashCode.visitVarInsn(Opcodes.ALOAD, 0);
                hashCode.visitFieldInsn(Opcodes.GETFIELD, node.name, component.name, component.descriptor);
                final String owner = PRIMITIVE_WRAPPERS.get(component.descriptor);
                hashCode.visitMethodInsn(
                    Opcodes.INVOKESTATIC,
                    owner != null ? owner : "java/util/Objects",
                    "hashCode",
                    "(" + (owner != null ? component.descriptor : "Ljava/lang/Object;") + ")I",
                    false
                );
                hashCode.visitInsn(Opcodes.IADD);
            }
            hashCode.visitInsn(Opcodes.IRETURN);

            hashCode.visitEnd();
        }

        node.methods.remove(ASMUtils.getMethod(node, "toString", TOSTRING_DESC));
        final MethodVisitor toString = node.visitMethod(Opcodes.ACC_PUBLIC, "toString", TOSTRING_DESC, null, null);
        {
            toString.visitCode();

            final StringBuilder formatString = new StringBuilder("%s[");
            for (int i = 0; i < node.recordComponents.size(); i++) {
                formatString.append(node.recordComponents.get(i).name).append("=%s");
                if (i != node.recordComponents.size() - 1) {
                    formatString.append(", ");
                }
            }
            formatString.append(']');

            toString.visitLdcInsn(formatString.toString());
            toString.visitIntInsn(Opcodes.SIPUSH, node.recordComponents.size() + 1);
            toString.visitTypeInsn(Opcodes.ANEWARRAY, "java/lang/Object");
            toString.visitInsn(Opcodes.DUP);
            toString.visitInsn(Opcodes.ICONST_0);
            toString.visitVarInsn(Opcodes.ALOAD, 0);
            toString.visitMethodInsn(
                Opcodes.INVOKEVIRTUAL,
                "java/lang/Object",
                "getClass",
                "()Ljava/lang/Class;",
                false
            );
            toString.visitMethodInsn(
                Opcodes.INVOKEVIRTUAL,
                "java/lang/Class",
                "getSimpleName",
                "()Ljava/lang/String;",
                false
            );
            toString.visitInsn(Opcodes.AASTORE);
            int i = 1;
            for (final RecordComponentNode component : node.recordComponents) {
                toString.visitInsn(Opcodes.DUP);
                toString.visitIntInsn(Opcodes.SIPUSH, i);
                toString.visitVarInsn(Opcodes.ALOAD, 0);
                toString.visitFieldInsn(Opcodes.GETFIELD, node.name, component.name, component.descriptor);
                final String owner = PRIMITIVE_WRAPPERS.get(component.descriptor);
                toString.visitMethodInsn(
                    Opcodes.INVOKESTATIC,
                    owner != null ? owner : "java/util/Objects",
                    "toString",
                    "(" + (owner != null ? component.descriptor : "Ljava/lang/Object;") + ")Ljava/lang/String;",
                    false
                );
                toString.visitInsn(Opcodes.AASTORE);
                i++;
            }
            toString.visitMethodInsn(
                Opcodes.INVOKESTATIC,
                "java/lang/String",
                "format",
                "(Ljava/lang/String;[Ljava/lang/Object;)Ljava/lang/String;",
                false
            );
            toString.visitInsn(Opcodes.ARETURN);

            toString.visitEnd();
        }
    }

    private int count(final String s, final char search) {
        char[] chars = s.toCharArray();
        int count = 0;
        for (char c : chars) {
            if (c == search) count++;
        }
        return count;
    }

    private InsnList convertStringConcatFactory(final String pattern, final Type[] stackArgs, final int[] stackIndices, final Object[] bsmArgs) {
        InsnList insns = new InsnList();
        char[] chars = pattern.toCharArray();
        int stackArgsIndex = 0;
        int bsmArgsIndex = 0;
        StringBuilder partBuilder = new StringBuilder();

        insns.add(new TypeInsnNode(Opcodes.NEW, "java/lang/StringBuilder"));
        insns.add(new InsnNode(Opcodes.DUP));
        insns.add(new MethodInsnNode(Opcodes.INVOKESPECIAL, "java/lang/StringBuilder", "<init>", "()V"));
        for (char c : chars) {
            if (c == STACK_ARG_CONSTANT) {
                if (partBuilder.length() != 0) {
                    insns.add(new LdcInsnNode(partBuilder.toString()));
                    insns.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, "java/lang/StringBuilder", "append", "(Ljava/lang/String;)Ljava/lang/StringBuilder;"));
                    partBuilder = new StringBuilder();
                }

                Type stackArg = stackArgs[stackArgsIndex++];
                int stackIndex = stackIndices[stackArgsIndex - 1];
                if (stackArg.getSort() == Type.OBJECT) {
                    insns.add(new VarInsnNode(Opcodes.ALOAD, stackIndex));
                    insns.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, "java/lang/StringBuilder", "append", "(Ljava/lang/Object;)Ljava/lang/StringBuilder;"));
                } else if (stackArg.getSort() == Type.ARRAY) {
                    insns.add(new VarInsnNode(Opcodes.ALOAD, stackIndex));
                    insns.add(new MethodInsnNode(Opcodes.INVOKESTATIC, "java/util/Arrays", "toString", "([Ljava/lang/Object;)Ljava/lang/String;"));
                    insns.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, "java/lang/StringBuilder", "append", "(Ljava/lang/String;)Ljava/lang/StringBuilder;"));
                } else {
                    insns.add(new VarInsnNode(stackArg.getOpcode(Opcodes.ILOAD), stackIndex));
                    insns.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, "java/lang/StringBuilder", "append", "(" + stackArg.getDescriptor() + ")Ljava/lang/StringBuilder;"));
                }
            } else if (c == BSM_ARG_CONSTANT) {
                insns.add(new LdcInsnNode(bsmArgs[bsmArgsIndex++]));
                insns.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, "java/lang/StringBuilder", "append", "(Ljava/lang/Object;)Ljava/lang/StringBuilder;"));
            } else {
                partBuilder.append(c);
            }
        }
        if (partBuilder.length() != 0) {
            insns.add(new LdcInsnNode(partBuilder.toString()));
            insns.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, "java/lang/StringBuilder", "append", "(Ljava/lang/String;)Ljava/lang/StringBuilder;"));
        }
        insns.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, "java/lang/StringBuilder", "toString", "()Ljava/lang/String;"));
        return insns;
    }

}
