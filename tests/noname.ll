; RUN: llvm-mutate -f %s -n -o %t
; RUN: diff %t %s.check

define dso_local void @_Z4axpyfPfS_(float %0, float* nocapture readonly %1, float* nocapture %2) {
  %4 = tail call i32 @llvm.nvvm.read.ptx.sreg.tid.x() 
  %5 = zext i32 %4 to i64
  %6 = getelementptr inbounds float, float* %1, i64 %5
  %7 = load float, float* %6, align 4
  %8 = fmul contract float %7, %0
  %9 = fadd contract float %7, %8
  %10 = getelementptr inbounds float, float* %2, i64 %5
  store float %9, float* %10, align 4
  ret void
}

; Function Attrs: nofree norecurse nounwind
declare i32 @llvm.nvvm.read.ptx.sreg.tid.x() #0

attributes #0 = { nounwind readnone }
