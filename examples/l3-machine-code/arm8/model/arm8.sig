(* arm8 - generated by L3 - Fri Jun 24 16:40:21 2016 *)

signature arm8 =
sig

structure Map: MutableMap

(* -------------------------------------------------------------------------
   Types
   ------------------------------------------------------------------------- *)

type ProcState =
  { C: bool, EL: BitsN.nbit, N: bool, SPS: bool, V: bool, Z: bool }

type TCR_EL1 = { TBI0: bool, TBI1: bool, tcr_el1'rst: BitsN.nbit }

type TCR_EL2_EL3 = { TBI: bool, tcr_el2_el3'rst: BitsN.nbit }

type SCTLRType =
  { A: bool, E0E: bool, EE: bool, SA: bool, SA0: bool,
    sctlrtype'rst: BitsN.nbit }

datatype BranchType
  = BranchType_CALL | BranchType_ERET | BranchType_DBGEXIT
  | BranchType_RET | BranchType_JMP | BranchType_EXCEPTION
  | BranchType_UNKNOWN

datatype AccType
  = AccType_NORMAL | AccType_VEC | AccType_STREAM | AccType_VECSTREAM
  | AccType_ATOMIC | AccType_ORDERED | AccType_UNPRIV | AccType_IFETCH
  | AccType_PTW | AccType_DC | AccType_IC | AccType_AT

datatype ShiftType
  = ShiftType_LSL | ShiftType_LSR | ShiftType_ASR | ShiftType_ROR

datatype ExtendType
  = ExtendType_UXTB | ExtendType_UXTH | ExtendType_UXTW | ExtendType_UXTX
  | ExtendType_SXTB | ExtendType_SXTH | ExtendType_SXTW | ExtendType_SXTX

datatype LogicalOp = LogicalOp_AND | LogicalOp_ORR | LogicalOp_EOR

datatype MemOp = MemOp_LOAD | MemOp_STORE | MemOp_PREFETCH

datatype MemBarrierOp
  = MemBarrierOp_DSB | MemBarrierOp_DMB | MemBarrierOp_ISB

datatype MoveWideOp = MoveWideOp_N | MoveWideOp_Z | MoveWideOp_K

datatype RevOp = RevOp_RBIT | RevOp_REV16 | RevOp_REV32 | RevOp_REV64

datatype SystemHintOp
  = SystemHintOp_NOP | SystemHintOp_YIELD | SystemHintOp_WFE
  | SystemHintOp_WFI | SystemHintOp_SEV | SystemHintOp_SEVL

datatype PSTATEField
  = PSTATEField_DAIFSet | PSTATEField_DAIFClr | PSTATEField_SP

datatype System
  = ExceptionReturn
  | HypervisorCall of BitsN.nbit
  | MoveImmediateProcState of PSTATEField * BitsN.nbit
  | MoveSystemRegister of
      bool *
      (BitsN.nbit *
       (BitsN.nbit *
        (BitsN.nbit * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))))
  | SecureMonitorCall of BitsN.nbit
  | SupervisorCall of BitsN.nbit
  | SystemInstruction of
      BitsN.nbit *
      (BitsN.nbit * (BitsN.nbit * (BitsN.nbit * (bool * BitsN.nbit))))

datatype Debug
  = Breakpoint of BitsN.nbit
  | DebugRestore
  | DebugSwitch of BitsN.nbit
  | Halt of BitsN.nbit

datatype LoadStore
  = LoadLiteral''32 of
      BitsN.nbit * (MemOp * (bool * (BitsN.nbit * BitsN.nbit)))
  | LoadLiteral''64 of
      BitsN.nbit * (MemOp * (bool * (BitsN.nbit * BitsN.nbit)))
  | LoadStoreAcquire''16 of
      BitsN.nbit *
      (MemOp *
       (AccType *
        (bool * (bool * (bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))))))
  | LoadStoreAcquire''32 of
      BitsN.nbit *
      (MemOp *
       (AccType *
        (bool * (bool * (bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))))))
  | LoadStoreAcquire''64 of
      BitsN.nbit *
      (MemOp *
       (AccType *
        (bool * (bool * (bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))))))
  | LoadStoreAcquire''8 of
      BitsN.nbit *
      (MemOp *
       (AccType *
        (bool * (bool * (bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))))))
  | LoadStoreAcquirePair''128 of
      BitsN.nbit *
      (MemOp *
       (AccType *
        (bool *
         (bool * (BitsN.nbit * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))))))
  | LoadStoreAcquirePair''64 of
      BitsN.nbit *
      (MemOp *
       (AccType *
        (bool *
         (bool * (BitsN.nbit * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))))))
  | LoadStoreImmediate''16 of
      BitsN.nbit *
      (bool *
       (MemOp *
        (AccType *
         (bool *
          (bool *
           (bool *
            (bool *
             (bool * (bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))))))))))
  | LoadStoreImmediate''32 of
      BitsN.nbit *
      (bool *
       (MemOp *
        (AccType *
         (bool *
          (bool *
           (bool *
            (bool *
             (bool * (bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))))))))))
  | LoadStoreImmediate''64 of
      BitsN.nbit *
      (bool *
       (MemOp *
        (AccType *
         (bool *
          (bool *
           (bool *
            (bool *
             (bool * (bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))))))))))
  | LoadStoreImmediate''8 of
      BitsN.nbit *
      (bool *
       (MemOp *
        (AccType *
         (bool *
          (bool *
           (bool *
            (bool *
             (bool * (bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))))))))))
  | LoadStorePair''32 of
      BitsN.nbit *
      (MemOp *
       (AccType *
        (bool *
         (bool *
          (bool *
           (bool *
            (bool *
             (BitsN.nbit * (BitsN.nbit * (BitsN.nbit * BitsN.nbit))))))))))
  | LoadStorePair''64 of
      BitsN.nbit *
      (MemOp *
       (AccType *
        (bool *
         (bool *
          (bool *
           (bool *
            (bool *
             (BitsN.nbit * (BitsN.nbit * (BitsN.nbit * BitsN.nbit))))))))))
  | LoadStoreRegister''16 of
      BitsN.nbit *
      (bool *
       (MemOp *
        (bool *
         (BitsN.nbit *
          (ExtendType * (Nat.nat * (BitsN.nbit * BitsN.nbit)))))))
  | LoadStoreRegister''32 of
      BitsN.nbit *
      (bool *
       (MemOp *
        (bool *
         (BitsN.nbit *
          (ExtendType * (Nat.nat * (BitsN.nbit * BitsN.nbit)))))))
  | LoadStoreRegister''64 of
      BitsN.nbit *
      (bool *
       (MemOp *
        (bool *
         (BitsN.nbit *
          (ExtendType * (Nat.nat * (BitsN.nbit * BitsN.nbit)))))))
  | LoadStoreRegister''8 of
      BitsN.nbit *
      (bool *
       (MemOp *
        (bool *
         (BitsN.nbit *
          (ExtendType * (Nat.nat * (BitsN.nbit * BitsN.nbit)))))))

datatype Branch
  = BranchConditional of BitsN.nbit * BitsN.nbit
  | BranchImmediate of BitsN.nbit * BranchType
  | BranchRegister of BitsN.nbit * BranchType
  | CompareAndBranch''32 of
      BitsN.nbit * (bool * (BitsN.nbit * BitsN.nbit))
  | CompareAndBranch''64 of
      BitsN.nbit * (bool * (BitsN.nbit * BitsN.nbit))
  | TestBitAndBranch''32 of
      BitsN.nbit * (BitsN.nbit * (bool * (BitsN.nbit * BitsN.nbit)))
  | TestBitAndBranch''64 of
      BitsN.nbit * (BitsN.nbit * (bool * (BitsN.nbit * BitsN.nbit)))

datatype CRCExt
  = CRC''16 of
      BitsN.nbit * (bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))
  | CRC''32 of
      BitsN.nbit * (bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))
  | CRC''64 of
      BitsN.nbit * (bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))
  | CRC''8 of
      BitsN.nbit * (bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))

datatype Data
  = AddSubCarry''32 of
      BitsN.nbit *
      (bool * (bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit))))
  | AddSubCarry''64 of
      BitsN.nbit *
      (bool * (bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit))))
  | AddSubExtendRegister''32 of
      BitsN.nbit *
      (bool *
       (bool *
        (BitsN.nbit *
         (ExtendType * (BitsN.nbit * (BitsN.nbit * BitsN.nbit))))))
  | AddSubExtendRegister''64 of
      BitsN.nbit *
      (bool *
       (bool *
        (BitsN.nbit *
         (ExtendType * (BitsN.nbit * (BitsN.nbit * BitsN.nbit))))))
  | AddSubImmediate''32 of
      BitsN.nbit *
      (bool * (bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit))))
  | AddSubImmediate''64 of
      BitsN.nbit *
      (bool * (bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit))))
  | AddSubShiftedRegister''32 of
      BitsN.nbit *
      (bool *
       (bool *
        (ShiftType *
         (BitsN.nbit * (BitsN.nbit * (BitsN.nbit * BitsN.nbit))))))
  | AddSubShiftedRegister''64 of
      BitsN.nbit *
      (bool *
       (bool *
        (ShiftType *
         (BitsN.nbit * (BitsN.nbit * (BitsN.nbit * BitsN.nbit))))))
  | BitfieldMove''32 of
      BitsN.nbit *
      (bool *
       (bool *
        (BitsN.nbit *
         (BitsN.nbit * (Nat.nat * (Nat.nat * (BitsN.nbit * BitsN.nbit)))))))
  | BitfieldMove''64 of
      BitsN.nbit *
      (bool *
       (bool *
        (BitsN.nbit *
         (BitsN.nbit * (Nat.nat * (Nat.nat * (BitsN.nbit * BitsN.nbit)))))))
  | ConditionalCompareImmediate''32 of
      BitsN.nbit *
      (bool *
       (BitsN.nbit *
        (BitsN.nbit * ((bool * (bool * (bool * bool))) * BitsN.nbit))))
  | ConditionalCompareImmediate''64 of
      BitsN.nbit *
      (bool *
       (BitsN.nbit *
        (BitsN.nbit * ((bool * (bool * (bool * bool))) * BitsN.nbit))))
  | ConditionalCompareRegister''32 of
      BitsN.nbit *
      (bool *
       (BitsN.nbit *
        ((bool * (bool * (bool * bool))) * (BitsN.nbit * BitsN.nbit))))
  | ConditionalCompareRegister''64 of
      BitsN.nbit *
      (bool *
       (BitsN.nbit *
        ((bool * (bool * (bool * bool))) * (BitsN.nbit * BitsN.nbit))))
  | ConditionalSelect''32 of
      BitsN.nbit *
      (bool *
       (bool * (BitsN.nbit * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))))
  | ConditionalSelect''64 of
      BitsN.nbit *
      (bool *
       (bool * (BitsN.nbit * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))))
  | CountLeading''32 of BitsN.nbit * (bool * (BitsN.nbit * BitsN.nbit))
  | CountLeading''64 of BitsN.nbit * (bool * (BitsN.nbit * BitsN.nbit))
  | Division''32 of
      BitsN.nbit * (bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))
  | Division''64 of
      BitsN.nbit * (bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))
  | ExtractRegister''32 of
      BitsN.nbit * (BitsN.nbit * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))
  | ExtractRegister''64 of
      BitsN.nbit * (BitsN.nbit * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))
  | LogicalImmediate''32 of
      BitsN.nbit *
      (LogicalOp * (bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit))))
  | LogicalImmediate''64 of
      BitsN.nbit *
      (LogicalOp * (bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit))))
  | LogicalShiftedRegister''32 of
      BitsN.nbit *
      (LogicalOp *
       (bool *
        (bool *
         (ShiftType * (Nat.nat * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))))))
  | LogicalShiftedRegister''64 of
      BitsN.nbit *
      (LogicalOp *
       (bool *
        (bool *
         (ShiftType * (Nat.nat * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))))))
  | MoveWide''32 of
      BitsN.nbit * (MoveWideOp * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))
  | MoveWide''64 of
      BitsN.nbit * (MoveWideOp * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))
  | MultiplyAddSub''32 of
      BitsN.nbit *
      (bool * (BitsN.nbit * (BitsN.nbit * (BitsN.nbit * BitsN.nbit))))
  | MultiplyAddSub''64 of
      BitsN.nbit *
      (bool * (BitsN.nbit * (BitsN.nbit * (BitsN.nbit * BitsN.nbit))))
  | MultiplyAddSubLong of
      bool *
      (bool * (BitsN.nbit * (BitsN.nbit * (BitsN.nbit * BitsN.nbit))))
  | MultiplyHigh of bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit))
  | Reverse''32 of BitsN.nbit * (RevOp * (BitsN.nbit * BitsN.nbit))
  | Reverse''64 of BitsN.nbit * (RevOp * (BitsN.nbit * BitsN.nbit))
  | Shift''32 of
      BitsN.nbit * (ShiftType * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))
  | Shift''64 of
      BitsN.nbit * (ShiftType * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))

datatype instruction
  = Address of bool * (BitsN.nbit * BitsN.nbit)
  | Branch of Branch
  | CRCExt of CRCExt
  | ClearExclusive of BitsN.nbit
  | Data of Data
  | Debug of Debug
  | Hint of SystemHintOp
  | LoadStore of LoadStore
  | MemoryBarrier of MemBarrierOp * BitsN.nbit
  | Reserved
  | System of System
  | Unallocated

datatype MachineCode = ARM8 of BitsN.nbit | BadCode of string

datatype maybe_instruction
  = FAIL of string
  | OK of instruction
  | PENDING of string * instruction
  | WORD of BitsN.nbit

(* -------------------------------------------------------------------------
   Exceptions
   ------------------------------------------------------------------------- *)

exception ALIGNMENT_FAULT

exception ASSERT of string

exception UNDEFINED_FAULT of string

(* -------------------------------------------------------------------------
   Functions
   ------------------------------------------------------------------------- *)

structure Cast:
sig

val natToBranchType:Nat.nat -> BranchType
val BranchTypeToNat:BranchType-> Nat.nat
val stringToBranchType:string -> BranchType
val BranchTypeToString:BranchType-> string
val natToAccType:Nat.nat -> AccType
val AccTypeToNat:AccType-> Nat.nat
val stringToAccType:string -> AccType
val AccTypeToString:AccType-> string
val natToShiftType:Nat.nat -> ShiftType
val ShiftTypeToNat:ShiftType-> Nat.nat
val stringToShiftType:string -> ShiftType
val ShiftTypeToString:ShiftType-> string
val natToExtendType:Nat.nat -> ExtendType
val ExtendTypeToNat:ExtendType-> Nat.nat
val stringToExtendType:string -> ExtendType
val ExtendTypeToString:ExtendType-> string
val natToLogicalOp:Nat.nat -> LogicalOp
val LogicalOpToNat:LogicalOp-> Nat.nat
val stringToLogicalOp:string -> LogicalOp
val LogicalOpToString:LogicalOp-> string
val natToMemOp:Nat.nat -> MemOp
val MemOpToNat:MemOp-> Nat.nat
val stringToMemOp:string -> MemOp
val MemOpToString:MemOp-> string
val natToMemBarrierOp:Nat.nat -> MemBarrierOp
val MemBarrierOpToNat:MemBarrierOp-> Nat.nat
val stringToMemBarrierOp:string -> MemBarrierOp
val MemBarrierOpToString:MemBarrierOp-> string
val natToMoveWideOp:Nat.nat -> MoveWideOp
val MoveWideOpToNat:MoveWideOp-> Nat.nat
val stringToMoveWideOp:string -> MoveWideOp
val MoveWideOpToString:MoveWideOp-> string
val natToRevOp:Nat.nat -> RevOp
val RevOpToNat:RevOp-> Nat.nat
val stringToRevOp:string -> RevOp
val RevOpToString:RevOp-> string
val natToSystemHintOp:Nat.nat -> SystemHintOp
val SystemHintOpToNat:SystemHintOp-> Nat.nat
val stringToSystemHintOp:string -> SystemHintOp
val SystemHintOpToString:SystemHintOp-> string
val natToPSTATEField:Nat.nat -> PSTATEField
val PSTATEFieldToNat:PSTATEField-> Nat.nat
val stringToPSTATEField:string -> PSTATEField
val PSTATEFieldToString:PSTATEField-> string

end

val MEM: (BitsN.nbit Map.map) ref
val PC: BitsN.nbit ref
val PSTATE: ProcState ref
val REG: (BitsN.nbit Map.map) ref
val SCTLR_EL1: SCTLRType ref
val SCTLR_EL2: SCTLRType ref
val SCTLR_EL3: SCTLRType ref
val SP_EL0: BitsN.nbit ref
val SP_EL1: BitsN.nbit ref
val SP_EL2: BitsN.nbit ref
val SP_EL3: BitsN.nbit ref
val TCR_EL1: TCR_EL1 ref
val TCR_EL2: TCR_EL2_EL3 ref
val TCR_EL3: TCR_EL2_EL3 ref
val branch_hint: (BranchType option) ref
val ProcState_C_rupd: ProcState * bool -> ProcState
val ProcState_EL_rupd: ProcState * BitsN.nbit -> ProcState
val ProcState_N_rupd: ProcState * bool -> ProcState
val ProcState_SPS_rupd: ProcState * bool -> ProcState
val ProcState_V_rupd: ProcState * bool -> ProcState
val ProcState_Z_rupd: ProcState * bool -> ProcState
val TCR_EL1_TBI0_rupd: TCR_EL1 * bool -> TCR_EL1
val TCR_EL1_TBI1_rupd: TCR_EL1 * bool -> TCR_EL1
val TCR_EL1_tcr_el1'rst_rupd: TCR_EL1 * BitsN.nbit -> TCR_EL1
val TCR_EL2_EL3_TBI_rupd: TCR_EL2_EL3 * bool -> TCR_EL2_EL3
val TCR_EL2_EL3_tcr_el2_el3'rst_rupd:
  TCR_EL2_EL3 * BitsN.nbit -> TCR_EL2_EL3
val SCTLRType_A_rupd: SCTLRType * bool -> SCTLRType
val SCTLRType_E0E_rupd: SCTLRType * bool -> SCTLRType
val SCTLRType_EE_rupd: SCTLRType * bool -> SCTLRType
val SCTLRType_SA_rupd: SCTLRType * bool -> SCTLRType
val SCTLRType_SA0_rupd: SCTLRType * bool -> SCTLRType
val SCTLRType_sctlrtype'rst_rupd: SCTLRType * BitsN.nbit -> SCTLRType
val boolify'32:
  BitsN.nbit ->
  bool *
  (bool *
   (bool *
    (bool *
     (bool *
      (bool *
       (bool *
        (bool *
         (bool *
          (bool *
           (bool *
            (bool *
             (bool *
              (bool *
               (bool *
                (bool *
                 (bool *
                  (bool *
                   (bool *
                    (bool *
                     (bool *
                      (bool *
                       (bool *
                        (bool *
                         (bool *
                          (bool *
                           (bool *
                            (bool * (bool * (bool * (bool * bool))))))))))))))))))))))))))))))
val rec'TCR_EL1: BitsN.nbit -> TCR_EL1
val reg'TCR_EL1: TCR_EL1 -> BitsN.nbit
val write'rec'TCR_EL1: (BitsN.nbit * TCR_EL1) -> BitsN.nbit
val write'reg'TCR_EL1: (TCR_EL1 * BitsN.nbit) -> TCR_EL1
val rec'TCR_EL2_EL3: BitsN.nbit -> TCR_EL2_EL3
val reg'TCR_EL2_EL3: TCR_EL2_EL3 -> BitsN.nbit
val write'rec'TCR_EL2_EL3: (BitsN.nbit * TCR_EL2_EL3) -> BitsN.nbit
val write'reg'TCR_EL2_EL3: (TCR_EL2_EL3 * BitsN.nbit) -> TCR_EL2_EL3
val rec'SCTLRType: BitsN.nbit -> SCTLRType
val reg'SCTLRType: SCTLRType -> BitsN.nbit
val write'rec'SCTLRType: (BitsN.nbit * SCTLRType) -> BitsN.nbit
val write'reg'SCTLRType: (SCTLRType * BitsN.nbit) -> SCTLRType
val X:Nat.nat-> BitsN.nbit -> BitsN.nbit
val write'X:Nat.nat-> (BitsN.nbit * BitsN.nbit) -> unit
val SP:Nat.nat-> BitsN.nbit
val write'SP:Nat.nat-> BitsN.nbit -> unit
val TranslationRegime: unit -> BitsN.nbit
val SCTLR: unit -> SCTLRType
val Hint_Branch: BranchType -> unit
val BranchTo: (BitsN.nbit * BranchType) -> unit
val Align:Nat.nat-> (BitsN.nbit * Nat.nat) -> BitsN.nbit
val Aligned:Nat.nat-> (BitsN.nbit * Nat.nat) -> bool
val CheckSPAlignment: unit -> unit
val CheckAlignment: (BitsN.nbit * (Nat.nat * (AccType * bool))) -> bool
val BigEndian: unit -> bool
val ByteList: (bool list) -> ((bool list) list)
val BigEndianReverse: (bool list) -> (bool list)
val Mem:Nat.nat-> (BitsN.nbit * (Nat.nat * AccType)) -> BitsN.nbit
val write'Mem:Nat.nat->
  (BitsN.nbit * (BitsN.nbit * (Nat.nat * AccType))) -> unit
val ConditionTest: (BitsN.nbit * (bool * (bool * (bool * bool)))) -> bool
val ConditionHolds: BitsN.nbit -> bool
val Ones: Nat.nat -> (bool list)
val Zeros: Nat.nat -> (bool list)
val Replicate:Nat.nat-> (bool list) -> BitsN.nbit
val HighestSetBit:Nat.nat-> BitsN.nbit -> IntInf.int
val CountLeadingZeroBits:Nat.nat-> BitsN.nbit -> Nat.nat
val CountLeadingSignBits:Nat.nat-> BitsN.nbit -> Nat.nat
val Poly32Mod2_loop:
  (Nat.nat * ((bool list) * (bool list))) -> (bool list)
val Poly32Mod2: ((bool list) * BitsN.nbit) -> BitsN.nbit
val AddWithCarry:Nat.nat->
  (BitsN.nbit * (BitsN.nbit * bool)) ->
  (BitsN.nbit * (bool * (bool * (bool * bool))))
val SetTheFlags: (bool * (bool * (bool * (bool * bool)))) -> unit
val DecodeShift: BitsN.nbit -> ShiftType
val ShiftValue:Nat.nat->
  (BitsN.nbit * (ShiftType * Nat.nat)) -> BitsN.nbit
val ShiftReg:Nat.nat-> (BitsN.nbit * (ShiftType * Nat.nat)) -> BitsN.nbit
val ExtendWord:Nat.nat * Nat.nat-> (BitsN.nbit * bool) -> BitsN.nbit
val Extend:Nat.nat-> ((bool list) * bool) -> BitsN.nbit
val DecodeRegExtend: BitsN.nbit -> ExtendType
val ExtendValue:Nat.nat->
  (BitsN.nbit * (ExtendType * Nat.nat)) -> BitsN.nbit
val ExtendReg:Nat.nat->
  (BitsN.nbit * (ExtendType * Nat.nat)) -> BitsN.nbit
val DecodeBitMasks:Nat.nat->
  (BitsN.nbit * (BitsN.nbit * (BitsN.nbit * bool))) ->
  ((BitsN.nbit * BitsN.nbit) option)
val dfn'Address: (bool * (BitsN.nbit * BitsN.nbit)) -> unit
val dfn'AddSubCarry:Nat.nat->
  (BitsN.nbit * (bool * (bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit))))) ->
  unit
val dfn'AddSubExtendRegister:Nat.nat->
  (BitsN.nbit *
   (bool *
    (bool *
     (BitsN.nbit * (ExtendType * (BitsN.nbit * (BitsN.nbit * BitsN.nbit))))))) ->
  unit
val dfn'AddSubImmediate:Nat.nat->
  (BitsN.nbit * (bool * (bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit))))) ->
  unit
val dfn'AddSubShiftedRegister:Nat.nat->
  (BitsN.nbit *
   (bool *
    (bool *
     (ShiftType * (BitsN.nbit * (BitsN.nbit * (BitsN.nbit * BitsN.nbit))))))) ->
  unit
val dfn'LogicalImmediate:Nat.nat->
  (BitsN.nbit *
   (LogicalOp * (bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit))))) ->
  unit
val dfn'LogicalShiftedRegister:Nat.nat->
  (BitsN.nbit *
   (LogicalOp *
    (bool *
     (bool *
      (ShiftType * (Nat.nat * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))))))) ->
  unit
val dfn'Shift:Nat.nat->
  (BitsN.nbit * (ShiftType * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))) ->
  unit
val dfn'MoveWide:Nat.nat->
  (BitsN.nbit * (MoveWideOp * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))) ->
  unit
val dfn'BitfieldMove:Nat.nat->
  (BitsN.nbit *
   (bool *
    (bool *
     (BitsN.nbit *
      (BitsN.nbit * (Nat.nat * (Nat.nat * (BitsN.nbit * BitsN.nbit)))))))) ->
  unit
val dfn'ConditionalCompareImmediate:Nat.nat->
  (BitsN.nbit *
   (bool *
    (BitsN.nbit *
     (BitsN.nbit * ((bool * (bool * (bool * bool))) * BitsN.nbit))))) ->
  unit
val dfn'ConditionalCompareRegister:Nat.nat->
  (BitsN.nbit *
   (bool *
    (BitsN.nbit *
     ((bool * (bool * (bool * bool))) * (BitsN.nbit * BitsN.nbit))))) ->
  unit
val dfn'ConditionalSelect:Nat.nat->
  (BitsN.nbit *
   (bool *
    (bool * (BitsN.nbit * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))))) ->
  unit
val dfn'CountLeading:Nat.nat->
  (BitsN.nbit * (bool * (BitsN.nbit * BitsN.nbit))) -> unit
val dfn'ExtractRegister:Nat.nat->
  (BitsN.nbit * (BitsN.nbit * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))) ->
  unit
val dfn'Division:Nat.nat->
  (BitsN.nbit * (bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))) -> unit
val dfn'MultiplyAddSub:Nat.nat->
  (BitsN.nbit *
   (bool * (BitsN.nbit * (BitsN.nbit * (BitsN.nbit * BitsN.nbit))))) ->
  unit
val dfn'MultiplyAddSubLong:
  (bool * (bool * (BitsN.nbit * (BitsN.nbit * (BitsN.nbit * BitsN.nbit))))) ->
  unit
val dfn'MultiplyHigh:
  (bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit))) -> unit
val dfn'Reverse:Nat.nat->
  (BitsN.nbit * (RevOp * (BitsN.nbit * BitsN.nbit))) -> unit
val dfn'CRC:Nat.nat->
  (BitsN.nbit * (bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))) -> unit
val dfn'BranchConditional: (BitsN.nbit * BitsN.nbit) -> unit
val dfn'BranchImmediate: (BitsN.nbit * BranchType) -> unit
val dfn'BranchRegister: (BitsN.nbit * BranchType) -> unit
val dfn'CompareAndBranch:Nat.nat->
  (BitsN.nbit * (bool * (BitsN.nbit * BitsN.nbit))) -> unit
val dfn'TestBitAndBranch:Nat.nat->
  (BitsN.nbit * (BitsN.nbit * (bool * (BitsN.nbit * BitsN.nbit)))) -> unit
val LoadStoreSingle:Nat.nat->
  (BitsN.nbit *
   (bool *
    (MemOp *
     (AccType *
      (bool *
       (bool *
        (bool * (bool * (bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit))))))))))) ->
  unit
val dfn'LoadStoreImmediate:Nat.nat->
  (BitsN.nbit *
   (bool *
    (MemOp *
     (AccType *
      (bool *
       (bool *
        (bool *
         (bool *
          (bool * (bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))))))))))) ->
  unit
val dfn'LoadStoreRegister:Nat.nat->
  (BitsN.nbit *
   (bool *
    (MemOp *
     (bool *
      (BitsN.nbit * (ExtendType * (Nat.nat * (BitsN.nbit * BitsN.nbit)))))))) ->
  unit
val dfn'LoadStorePair:Nat.nat->
  (BitsN.nbit *
   (MemOp *
    (AccType *
     (bool *
      (bool *
       (bool *
        (bool *
         (bool * (BitsN.nbit * (BitsN.nbit * (BitsN.nbit * BitsN.nbit))))))))))) ->
  unit
val ExclusiveMonitorPass: (BitsN.nbit * Nat.nat) -> bool
val SetExclusiveMonitors: (BitsN.nbit * Nat.nat) -> unit
val ExclusiveMonitorStatus: BitsN.nbit
val dfn'LoadStoreAcquire:Nat.nat->
  (BitsN.nbit *
   (MemOp *
    (AccType *
     (bool * (bool * (bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))))))) ->
  unit
val dfn'LoadStoreAcquirePair:Nat.nat->
  (BitsN.nbit *
   (MemOp *
    (AccType *
     (bool *
      (bool * (BitsN.nbit * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))))))) ->
  unit
val dfn'LoadLiteral:Nat.nat->
  (BitsN.nbit * (MemOp * (bool * (BitsN.nbit * BitsN.nbit)))) -> unit
val dfn'MemoryBarrier: (MemBarrierOp * BitsN.nbit) -> unit
val dfn'ClearExclusive: BitsN.nbit -> unit
val dfn'Hint: SystemHintOp -> unit
val dfn'Breakpoint: BitsN.nbit -> unit
val dfn'DebugSwitch: BitsN.nbit -> unit
val dfn'DebugRestore: unit -> unit
val dfn'Halt: BitsN.nbit -> unit
val dfn'SystemInstruction:
  (BitsN.nbit *
   (BitsN.nbit * (BitsN.nbit * (BitsN.nbit * (bool * BitsN.nbit))))) ->
  unit
val dfn'MoveSystemRegister:
  (bool *
   (BitsN.nbit *
    (BitsN.nbit * (BitsN.nbit * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))))) ->
  unit
val dfn'MoveImmediateProcState: (PSTATEField * BitsN.nbit) -> unit
val dfn'SupervisorCall: BitsN.nbit -> unit
val dfn'HypervisorCall: BitsN.nbit -> unit
val dfn'SecureMonitorCall: BitsN.nbit -> unit
val dfn'ExceptionReturn: unit -> unit
val dfn'Unallocated: unit -> unit
val dfn'Reserved: unit -> unit
val Run: instruction -> unit
val DecodeLogicalOp: BitsN.nbit -> (LogicalOp * bool)
val NoOperation: instruction
val LoadStoreRegister:
  (BitsN.nbit *
   (bool *
    (MemOp *
     (bool *
      (BitsN.nbit * (ExtendType * (Nat.nat * (BitsN.nbit * BitsN.nbit)))))))) ->
  instruction
val LoadStoreImmediateN:
  (BitsN.nbit *
   (bool *
    (MemOp *
     (AccType *
      (bool *
       (bool *
        (bool *
         (bool *
          (bool * (bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))))))))))) ->
  instruction
val LoadStoreImmediate:
  (BitsN.nbit *
   (BitsN.nbit *
    (AccType *
     (bool * (bool * (bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))))))) ->
  instruction
val LoadStorePairN:
  (BitsN.nbit *
   (MemOp *
    (AccType *
     (bool *
      (bool *
       (bool *
        (bool *
         (bool * (BitsN.nbit * (BitsN.nbit * (BitsN.nbit * BitsN.nbit))))))))))) ->
  instruction
val LoadStorePair:
  (BitsN.nbit *
   (MemOp *
    (AccType *
     (bool *
      (bool *
       (bool * (BitsN.nbit * (BitsN.nbit * (BitsN.nbit * BitsN.nbit))))))))) ->
  instruction
val LoadStoreAcquireN:
  (BitsN.nbit *
   (MemOp *
    (AccType *
     (bool *
      (bool *
       (bool *
        (bool * (BitsN.nbit * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))))))))) ->
  instruction
val LoadStoreAcquire:
  (BitsN.nbit *
   (MemOp *
    (AccType *
     (bool *
      (bool * (BitsN.nbit * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))))))) ->
  instruction
val Decode: BitsN.nbit -> instruction
val Fetch: unit -> BitsN.nbit
val Next: unit -> unit
val CountTrailing:Nat.nat-> (bool * BitsN.nbit) -> Nat.nat
val EncodeBitMaskAux:Nat.nat->
  BitsN.nbit -> (Nat.nat * (Nat.nat * Nat.nat))
val EncodeBitMask:Nat.nat->
  BitsN.nbit -> ((BitsN.nbit * (BitsN.nbit * BitsN.nbit)) option)
val e_sf:Nat.nat-> BitsN.nbit -> BitsN.nbit
val EncodeLogicalOp: (LogicalOp * bool) -> (BitsN.nbit option)
val e_data: Data -> MachineCode
val e_debug: Debug -> BitsN.nbit
val e_crc: CRCExt -> BitsN.nbit
val e_branch: Branch -> MachineCode
val e_system: System -> BitsN.nbit
val e_LoadStoreImmediate:
  (BitsN.nbit *
   (bool *
    (MemOp *
     (AccType *
      (bool *
       (bool * (bool * (bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))))))))) ->
  MachineCode
val e_LoadStoreRegister:
  (BitsN.nbit *
   (bool *
    (MemOp *
     (bool *
      (BitsN.nbit * (ExtendType * (Nat.nat * (BitsN.nbit * BitsN.nbit)))))))) ->
  MachineCode
val e_load_store: LoadStore -> MachineCode
val Encode: instruction -> MachineCode
val skipSpaces: string -> string
val stripSpaces: string -> string
val p_number: string -> (Nat.nat option)
val p_encode_immediate:Nat.nat-> string -> ((bool * BitsN.nbit) option)
val p_unbounded_immediate: string -> (Nat.nat option)
val p_immediate:Nat.nat-> string -> ((bool * BitsN.nbit) option)
val p_neg_immediate:Nat.nat-> string -> ((bool * BitsN.nbit) option)
val p_pos_immediate:Nat.nat-> string -> ((bool * BitsN.nbit) option)
val p_signed_immediate:Nat.nat-> string -> ((bool * BitsN.nbit) option)
val p_offset:Nat.nat-> string -> ((bool * BitsN.nbit) option)
val p_label: string -> (string option)
val p_cond: string -> (BitsN.nbit option)
val invert_cond: string -> string
val p_w_x: string -> ((bool * string) option)
val is_wide_reg: string -> bool
val p_register: (bool * string) -> ((bool * BitsN.nbit) option)
val p_register1: (bool * (string list)) -> ((bool * BitsN.nbit) option)
val p_register2:
  (bool * (bool * (string list))) ->
  ((bool * (BitsN.nbit * BitsN.nbit)) option)
val p_register3:
  (bool * (bool * (bool * (string list)))) ->
  ((bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit))) option)
val p_register4:
  (bool * (bool * (bool * (bool * (string list))))) ->
  ((bool * (BitsN.nbit * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))) option)
val p_register2z:
  (string list) -> ((bool * (BitsN.nbit * BitsN.nbit)) option)
val p_register3z:
  (string list) ->
  ((bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit))) option)
val p_extend_amount:
  (ExtendType * (bool * string)) -> ((ExtendType * Nat.nat) option)
val p_extend: string -> ((ExtendType * Nat.nat) option)
val p_extend2:
  (Nat.nat * (bool * string)) -> ((ExtendType * Nat.nat) option)
val p_shift_amount: (ShiftType * string) -> ((ShiftType * Nat.nat) option)
val p_shift_imm: string -> ((ShiftType * Nat.nat) option)
val closingAddress: string -> ((bool * string) option)
val p_address:
  (string list) ->
  (string * ((BitsN.nbit * (BitsN.nbit * (bool * bool))) option))
val p_exclusive_address: (string list) -> (BitsN.nbit option)
val p_opening_reg: string -> ((bool * BitsN.nbit) option)
val p_reg_address:
  (Nat.nat * (string list)) ->
  ((BitsN.nbit * (BitsN.nbit * (ExtendType * Nat.nat))) option)
val p_ldr_literal:
  (Nat.nat *
   (MemOp * (bool * (bool * (bool * (BitsN.nbit * (string list))))))) ->
  maybe_instruction
val p_ldr_str:
  (Nat.nat * (MemOp * (AccType * (bool * (bool * (string list)))))) ->
  maybe_instruction
val p_ldar_stlr:
  (Nat.nat * (MemOp * (AccType * (bool * (string list))))) ->
  maybe_instruction
val p_ldp_stp:
  (MemOp * (AccType * (bool * (string list)))) -> maybe_instruction
val p_ldxp: (AccType * (string list)) -> maybe_instruction
val p_stxp: (AccType * (string list)) -> maybe_instruction
val p_adr: (bool * (string list)) -> maybe_instruction
val p_conditional_b: (BitsN.nbit * (string list)) -> maybe_instruction
val p_b_bl: (BranchType * (string list)) -> maybe_instruction
val p_br_etc: (BranchType * (string list)) -> maybe_instruction
val p_cbz_cbnz: (bool * (string list)) -> maybe_instruction
val p_tbz_tbnz: (bool * (string list)) -> maybe_instruction
val p_extend_register:
  (bool *
   (bool *
    (ExtendType * (Nat.nat * (bool * (string * (string * string))))))) ->
  maybe_instruction
val p_add_sub: (bool * (bool * (string list))) -> maybe_instruction
val p_and_etc_fail: maybe_instruction
val p_and_etc_imm_fail: maybe_instruction
val p_and_etc:
  (LogicalOp * (bool * (bool * (string list)))) -> maybe_instruction
val p_movk_etc: (MoveWideOp * (string list)) -> maybe_instruction
val p_adc_sbc: (bool * (bool * (string list))) -> maybe_instruction
val p_asrv_etc: (ShiftType * (string list)) -> maybe_instruction
val p_cls_clz: (bool * (string list)) -> maybe_instruction
val p_sdiv_udiv: (bool * (string list)) -> maybe_instruction
val p_madd_msub: (bool * (string list)) -> maybe_instruction
val p_smaddl_etc: (bool * (bool * (string list))) -> maybe_instruction
val p_smulh_umulh: (bool * (string list)) -> maybe_instruction
val p_rbit_etc: (RevOp * (string list)) -> maybe_instruction
val p_crc32b_etc: (Nat.nat * (bool * (string list))) -> maybe_instruction
val p_crc32x: (bool * (string list)) -> maybe_instruction
val p_bfm_etc: (bool * (bool * (string list))) -> maybe_instruction
val p_ccmn_ccmp: (bool * (string list)) -> maybe_instruction
val p_csel_etc: (bool * (bool * (string list))) -> maybe_instruction
val p_extr: (string list) -> maybe_instruction
val p_hint: (string list) -> maybe_instruction
val p_call: (Nat.nat * (string list)) -> maybe_instruction
val p_clrex: (string list) -> maybe_instruction
val p_dmb_etc: (MemBarrierOp * (string list)) -> maybe_instruction
val wzr_xzr: string -> string
val convert_immediate: (bool * BitsN.nbit) -> (string list)
val p_mov: (string list) -> maybe_instruction
val p_shift: (ShiftType * (string list)) -> maybe_instruction
val p_neg: (bool * (string list)) -> maybe_instruction
val convert_bfxil_etc: (string list) -> (string list)
val convert_bfi_etc: (string list) -> (string list)
val convert_cinc_etc: (string list) -> (string list)
val convert_cset_csetm: (string list) -> (string list)
val convert_zr1: (string list) -> (string list)
val convert_zr2: (string list) -> (string list)
val convert_zr_end: (string list) -> (string list)
val p_tokens: string -> (string list)
val instructionFromString: string -> maybe_instruction
val EncodeARM: string -> (string * (string option))
val s_cond: BitsN.nbit -> string
val s_regz: (bool * BitsN.nbit) -> string
val s_regp: (bool * BitsN.nbit) -> string
val s_reg2z: (bool * (BitsN.nbit * BitsN.nbit)) -> string
val s_reg3z: (bool * (BitsN.nbit * (BitsN.nbit * BitsN.nbit))) -> string
val s_reg4z:
  (bool * (BitsN.nbit * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)))) ->
  string
val s_nat: Nat.nat -> string
val s_dec:Nat.nat-> BitsN.nbit -> string
val s_hex:Nat.nat-> BitsN.nbit -> string
val s_immn: Nat.nat -> string
val s_imm:Nat.nat-> BitsN.nbit -> string
val s_offset: BitsN.nbit -> string
val s_signed_imm: BitsN.nbit -> string
val s_shifted_imm:Nat.nat-> BitsN.nbit -> string
val s_extend_type: ExtendType -> string
val s_shift_type: ShiftType -> string
val s_move_wide_op: MoveWideOp -> string
val s_logical_op: LogicalOp -> string
val s_invert_logical_op: LogicalOp -> string
val s_rev_op: RevOp -> string
val s_hint_op: SystemHintOp -> string
val s_barrier_op: MemBarrierOp -> string
val s_shift_amount: (ShiftType * Nat.nat) -> string
val s_nzcv: (bool * (bool * (bool * bool))) -> string
val s_data: Data -> (string * string)
val s_crc: CRCExt -> (string * string)
val s_branch: Branch -> (string * string)
val s_debug: Debug -> (string * string)
val s_system: System -> (string * string)
val s_load_store: LoadStore -> (string * string)
val instructionToString: instruction -> (string * string)
val diss: string -> string

end