; RUN: llvm-mutate -f %s -n -o %t
; RUN: diff %t %s.check

define dso_local void @_Z4axpyfPfS_(float %0, float* nocapture readonly %1, float* nocapture %2) !dbg !25 {
  %4 = tail call i32 @llvm.nvvm.read.ptx.sreg.tid.x(), !dbg !26
  %5 = zext i32 %4 to i64, !dbg !31
  %6 = getelementptr inbounds float, float* %1, i64 %5, !dbg !31
  %7 = load float, float* %6, align 4, !dbg !31
  %8 = fmul contract float %7, %0, !dbg !36
  %9 = fadd contract float %7, %8, !dbg !37
  %10 = getelementptr inbounds float, float* %2, i64 %5, !dbg !38
  store float %9, float* %10, align 4, !dbg !39
  ret void, !dbg !40
}

; Function Attrs: nounwind readnone
declare i32 @llvm.nvvm.read.ptx.sreg.tid.x() #0

attributes #0 = { nounwind readnone }

!llvm.module.flags = !{!0, !1, !2, !3, !4}
!llvm.dbg.cu = !{!5}
!nvvm.annotations = !{!8}
!llvm.ident = !{!9, !10}

!0 = !{i32 2, !"SDK Version", [2 x i32] [i32 11, i32 0]}
!1 = !{i32 7, !"Dwarf Version", i32 2}
!2 = !{i32 2, !"Debug Info Version", i32 3}
!3 = !{i32 1, !"wchar_size", i32 4}
!4 = !{i32 4, !"nvvm-reflect-ftz", i32 0}
!5 = distinct !DICompileUnit(language: DW_LANG_C_plus_plus, file: !6, producer: "Ubuntu clang version 11.1.0-++20210204121720+1fdec59bffc1-1~exp1~20210203232336.162", isOptimized: true, runtimeVersion: 0, emissionKind: DebugDirectivesOnly, enums: !7, splitDebugInlining: false, nameTableKind: None)
!6 = !DIFile(filename: "axpy.cu", directory: "/you_think_you_do")
!7 = !{}
!8 = !{void (float, float*, float*)* @_Z4axpyfPfS_, !"kernel", i32 1}
!9 = !{!"Ubuntu clang version 11.1.0-++20210204121720+1fdec59bffc1-1~exp1~20210203232336.162"}
!10 = !{!"clang version 3.8.0 (tags/RELEASE_380/final)"}
!13 = !DISubroutineType(types: !7)
!25 = distinct !DISubprogram(name: "axpy", scope: !6, file: !6, line: 3, type: !13, scopeLine: 3, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !5, retainedNodes: !7)
!26 = !DILocation(line: 53, column: 3, scope: !27, inlinedAt: !29)
!27 = distinct !DISubprogram(name: "__fetch_builtin_x", scope: !28, file: !28, line: 53, type: !13, scopeLine: 53, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !5, retainedNodes: !7)
!28 = !DIFile(filename: "/usr/lib/llvm-11/lib/clang/11.1.0/include/__clang_cuda_builtin_vars.h", directory: "")
!29 = distinct !DILocation(line: 4, column: 26, scope: !25)
!31 = !DILocation(line: 4, column: 24, scope: !25)
!36 = !DILocation(line: 4, column: 22, scope: !25)
!37 = !DILocation(line: 4, column: 39, scope: !25)
!38 = !DILocation(line: 4, column: 3, scope: !25)
!39 = !DILocation(line: 4, column: 18, scope: !25)
!40 = !DILocation(line: 5, column: 1, scope: !25)
