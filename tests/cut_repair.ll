; RUN: llvm-mutate -f %s -c U4 | filecheck %s
; CHECK:        %U3 = getelementptr
; CHECK-NOT:    %U4 = load
; CHECK-NEXT:   %nop = add i8 0, 0,
; CHECK-NOT:    %U4 = load
; CHECK-NEXT:   %U5 = fmul contract float {{(%A1|1.000000e\+00)}}
; CHECK-NEXT:   %U6 = fadd contract float {{(%A1|1.000000e\+00)}}
; CHECK: U4.d

define dso_local void @_Z4axpyfPfS_(float %A1, float* nocapture readonly %A2, float* nocapture %A3) {
  %U1 = tail call i32 @llvm.nvvm.read.ptx.sreg.tid.x(), !uniqueID !0
  %U2 = zext i32 %U1 to i64, !uniqueID !1
  %U3 = getelementptr inbounds float, float* %A2, i64 %U2, !uniqueID !2
  %U4 = load float, float* %U3, align 4, !uniqueID !3
  %U5 = fmul contract float %U4, %A1, !uniqueID !4
  %U6 = fadd contract float %U4, %U5, !uniqueID !5
  %U7 = getelementptr inbounds float, float* %A3, i64 %U2, !uniqueID !6
  store float %U6, float* %U7, align 4, !uniqueID !7
  ret void, !uniqueID !8
}

; Function Attrs: nounwind readnone
declare i32 @llvm.nvvm.read.ptx.sreg.tid.x() #0

attributes #0 = { nounwind readnone }

!0 = !{!"U1"}
!1 = !{!"U2"}
!2 = !{!"U3"}
!3 = !{!"U4"}
!4 = !{!"U5"}
!5 = !{!"U6"}
!6 = !{!"U7"}
!7 = !{!"U8"}
!8 = !{!"U9"}
