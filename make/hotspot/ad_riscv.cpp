#line 1 "ad_riscv.cpp"
//
// Copyright (c) 2003, 2022, Oracle and/or its affiliates. All rights reserved.
// Copyright (c) 2014, 2020, Red Hat Inc. All rights reserved.
// Copyright (c) 2020, 2022, Huawei Technologies Co., Ltd. All rights reserved.
// DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
//
// This code is free software; you can redistribute it and/or modify it
// under the terms of the GNU General Public License version 2 only, as
// published by the Free Software Foundation.
//
// This code is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
// version 2 for more details (a copy is included in the LICENSE file that
// accompanied this code).
//
// You should have received a copy of the GNU General Public License version
// 2 along with this work; if not, write to the Free Software Foundation,
// Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
//
// Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
// or visit www.oracle.com if you need additional information or have any
// questions.
//
//

// Machine Generated File.  Do Not Edit!

#include "precompiled.hpp"
#include "adfiles/adGlobals_riscv.hpp"
#include "adfiles/ad_riscv.hpp"
#include "memory/allocation.inline.hpp"
#include "code/codeCache.hpp"
#include "code/compiledIC.hpp"
#include "code/nativeInst.hpp"
#include "code/vmreg.inline.hpp"
#include "gc/shared/collectedHeap.inline.hpp"
#include "oops/compiledICHolder.hpp"
#include "oops/compressedOops.hpp"
#include "oops/markWord.hpp"
#include "oops/method.hpp"
#include "oops/oop.inline.hpp"
#include "opto/c2_MacroAssembler.hpp"
#include "opto/cfgnode.hpp"
#include "opto/intrinsicnode.hpp"
#include "opto/locknode.hpp"
#include "opto/opcodes.hpp"
#include "opto/regalloc.hpp"
#include "opto/regmask.hpp"
#include "opto/runtime.hpp"
#include "runtime/safepointMechanism.hpp"
#include "runtime/sharedRuntime.hpp"
#include "runtime/stubRoutines.hpp"
#include "utilities/growableArray.hpp"
#include "utilities/powerOfTwo.hpp"

//SourceForm

#line 1032 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"


// Derived RegMask with conditionally allocatable registers

RegMask _ANY_REG32_mask;
RegMask _ANY_REG_mask;
RegMask _PTR_REG_mask;
RegMask _NO_SPECIAL_REG32_mask;
RegMask _NO_SPECIAL_REG_mask;
RegMask _NO_SPECIAL_PTR_REG_mask;

void reg_mask_init() {

  _ANY_REG32_mask = _ALL_REG32_mask;
  _ANY_REG32_mask.Remove(OptoReg::as_OptoReg(x0->as_VMReg()));

  _ANY_REG_mask = _ALL_REG_mask;
  _ANY_REG_mask.SUBTRACT(_ZR_REG_mask);

  _PTR_REG_mask = _ALL_REG_mask;
  _PTR_REG_mask.SUBTRACT(_ZR_REG_mask);

  _NO_SPECIAL_REG32_mask = _ALL_REG32_mask;
  _NO_SPECIAL_REG32_mask.SUBTRACT(_NON_ALLOCATABLE_REG32_mask);

  _NO_SPECIAL_REG_mask = _ALL_REG_mask;
  _NO_SPECIAL_REG_mask.SUBTRACT(_NON_ALLOCATABLE_REG_mask);

  _NO_SPECIAL_PTR_REG_mask = _ALL_REG_mask;
  _NO_SPECIAL_PTR_REG_mask.SUBTRACT(_NON_ALLOCATABLE_REG_mask);

  // x27 is not allocatable when compressed oops is on
  if (UseCompressedOops) {
    _NO_SPECIAL_REG32_mask.Remove(OptoReg::as_OptoReg(x27->as_VMReg()));
    _NO_SPECIAL_REG_mask.SUBTRACT(_HEAPBASE_REG_mask);
    _NO_SPECIAL_PTR_REG_mask.SUBTRACT(_HEAPBASE_REG_mask);
  }

  // x8 is not allocatable when PreserveFramePointer is on
  if (PreserveFramePointer) {
    _NO_SPECIAL_REG32_mask.Remove(OptoReg::as_OptoReg(x8->as_VMReg()));
    _NO_SPECIAL_REG_mask.SUBTRACT(_FP_REG_mask);
    _NO_SPECIAL_PTR_REG_mask.SUBTRACT(_FP_REG_mask);
  }
}

void PhaseOutput::pd_perform_mach_node_analysis() {
}

int MachNode::pd_alignment_required() const {
  return 1;
}

int MachNode::compute_padding(int current_offset) const {
  return 0;
}

// is_CAS(int opcode, bool maybe_volatile)
//
// return true if opcode is one of the possible CompareAndSwapX
// values otherwise false.
bool is_CAS(int opcode, bool maybe_volatile)
{
  switch (opcode) {
    // We handle these
    case Op_CompareAndSwapI:
    case Op_CompareAndSwapL:
    case Op_CompareAndSwapP:
    case Op_CompareAndSwapN:
    case Op_ShenandoahCompareAndSwapP:
    case Op_ShenandoahCompareAndSwapN:
    case Op_CompareAndSwapB:
    case Op_CompareAndSwapS:
    case Op_GetAndSetI:
    case Op_GetAndSetL:
    case Op_GetAndSetP:
    case Op_GetAndSetN:
    case Op_GetAndAddI:
    case Op_GetAndAddL:
      return true;
    case Op_CompareAndExchangeI:
    case Op_CompareAndExchangeN:
    case Op_CompareAndExchangeB:
    case Op_CompareAndExchangeS:
    case Op_CompareAndExchangeL:
    case Op_CompareAndExchangeP:
    case Op_WeakCompareAndSwapB:
    case Op_WeakCompareAndSwapS:
    case Op_WeakCompareAndSwapI:
    case Op_WeakCompareAndSwapL:
    case Op_WeakCompareAndSwapP:
    case Op_WeakCompareAndSwapN:
    case Op_ShenandoahWeakCompareAndSwapP:
    case Op_ShenandoahWeakCompareAndSwapN:
    case Op_ShenandoahCompareAndExchangeP:
    case Op_ShenandoahCompareAndExchangeN:
      return maybe_volatile;
    default:
      return false;
  }
}

// predicate controlling translation of CAS
//
// returns true if CAS needs to use an acquiring load otherwise false
bool needs_acquiring_load_reserved(const Node *n)
{
  assert(n != NULL && is_CAS(n->Opcode(), true), "expecting a compare and swap");

  LoadStoreNode* ldst = n->as_LoadStore();
  if (n != NULL && is_CAS(n->Opcode(), false)) {
    assert(ldst != NULL && ldst->trailing_membar() != NULL, "expected trailing membar");
  } else {
    return ldst != NULL && ldst->trailing_membar() != NULL;
  }
  // so we can just return true here
  return true;
}
#define __ _masm.

// advance declarations for helper functions to convert register
// indices to register objects

// the ad file has to provide implementations of certain methods
// expected by the generic code
//
// REQUIRED FUNCTIONALITY

//=============================================================================

// !!!!! Special hack to get all types of calls to specify the byte offset
//       from the start of the call to the point where the return address
//       will point.

int MachCallStaticJavaNode::ret_addr_offset()
{
  // jal
  return 1 * NativeInstruction::instruction_size;
}

int MachCallDynamicJavaNode::ret_addr_offset()
{
  return 7 * NativeInstruction::instruction_size; // movptr, jal
}

int MachCallRuntimeNode::ret_addr_offset() {
  // for generated stubs the call will be
  //   jal(addr)
  // or with far branches
  //   jal(trampoline_stub)
  // for real runtime callouts it will be 11 instructions
  // see riscv_enc_java_to_runtime
  //   la(t1, retaddr)                ->  auipc + addi
  //   la(t0, RuntimeAddress(addr))   ->  lui + addi + slli + addi + slli + addi
  //   addi(sp, sp, -2 * wordSize)    ->  addi
  //   sd(t1, Address(sp, wordSize))  ->  sd
  //   jalr(t0)                       ->  jalr
  CodeBlob *cb = CodeCache::find_blob(_entry_point);
  if (cb != NULL) {
    return 1 * NativeInstruction::instruction_size;
  } else {
    return 11 * NativeInstruction::instruction_size;
  }
}

//
// Compute padding required for nodes which need alignment
//

// With RVC a call instruction may get 2-byte aligned.
// The address of the call instruction needs to be 4-byte aligned to
// ensure that it does not span a cache line so that it can be patched.
int CallStaticJavaDirectNode::compute_padding(int current_offset) const
{
  // to make sure the address of jal 4-byte aligned.
  return align_up(current_offset, alignment_required()) - current_offset;
}

// With RVC a call instruction may get 2-byte aligned.
// The address of the call instruction needs to be 4-byte aligned to
// ensure that it does not span a cache line so that it can be patched.
int CallDynamicJavaDirectNode::compute_padding(int current_offset) const
{
  // skip the movptr in MacroAssembler::ic_call():
  // lui + addi + slli + addi + slli + addi
  // Though movptr() has already 4-byte aligned with or without RVC,
  // We need to prevent from further changes by explicitly calculating the size.
  const int movptr_size = 6 * NativeInstruction::instruction_size;
  current_offset += movptr_size;
  // to make sure the address of jal 4-byte aligned.
  return align_up(current_offset, alignment_required()) - current_offset;
}

//=============================================================================

#ifndef PRODUCT
void MachBreakpointNode::format(PhaseRegAlloc *ra_, outputStream *st) const {
  assert_cond(st != NULL);
  st->print("BREAKPOINT");
}
#endif

void MachBreakpointNode::emit(CodeBuffer &cbuf, PhaseRegAlloc *ra_) const {
  C2_MacroAssembler _masm(&cbuf);
  __ ebreak();
}

uint MachBreakpointNode::size(PhaseRegAlloc *ra_) const {
  return MachNode::size(ra_);
}

//=============================================================================

#ifndef PRODUCT
  void MachNopNode::format(PhaseRegAlloc*, outputStream* st) const {
    st->print("nop \t# %d bytes pad for loops and calls", _count);
  }
#endif

  void MachNopNode::emit(CodeBuffer &cbuf, PhaseRegAlloc*) const {
    C2_MacroAssembler _masm(&cbuf);
    Assembler::CompressibleRegion cr(&_masm); // nops shall be 2-byte under RVC for alignment purposes.
    for (int i = 0; i < _count; i++) {
      __ nop();
    }
  }

  uint MachNopNode::size(PhaseRegAlloc*) const {
    return _count * (UseRVC ? NativeInstruction::compressed_instruction_size : NativeInstruction::instruction_size);
  }

//=============================================================================
const RegMask& MachConstantBaseNode::_out_RegMask = RegMask::Empty;

int ConstantTable::calculate_table_base_offset() const {
  return 0;  // absolute addressing, no offset
}

bool MachConstantBaseNode::requires_postalloc_expand() const { return false; }
void MachConstantBaseNode::postalloc_expand(GrowableArray <Node *> *nodes, PhaseRegAlloc *ra_) {
  ShouldNotReachHere();
}

void MachConstantBaseNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  // Empty encoding
}

uint MachConstantBaseNode::size(PhaseRegAlloc* ra_) const {
  return 0;
}

#ifndef PRODUCT
void MachConstantBaseNode::format(PhaseRegAlloc* ra_, outputStream* st) const {
  assert_cond(st != NULL);
  st->print("-- \t// MachConstantBaseNode (empty encoding)");
}
#endif

#ifndef PRODUCT
void MachPrologNode::format(PhaseRegAlloc *ra_, outputStream *st) const {
  assert_cond(st != NULL && ra_ != NULL);
  Compile* C = ra_->C;

  int framesize = C->output()->frame_slots() << LogBytesPerInt;

  if (C->output()->need_stack_bang(framesize)) {
    st->print("# stack bang size=%d\n\t", framesize);
  }

  st->print("sd  fp, [sp, #%d]\n\t", - 2 * wordSize);
  st->print("sd  ra, [sp, #%d]\n\t", - wordSize);
  if (PreserveFramePointer) { st->print("sub  fp, sp, #%d\n\t", 2 * wordSize); }
  st->print("sub sp, sp, #%d\n\t", framesize);

  if (C->stub_function() == NULL && BarrierSet::barrier_set()->barrier_set_nmethod() != NULL) {
    st->print("ld  t0, [guard]\n\t");
    st->print("membar LoadLoad\n\t");
    st->print("ld  t1, [xthread, #thread_disarmed_offset]\n\t");
    st->print("beq t0, t1, skip\n\t");
    st->print("jalr #nmethod_entry_barrier_stub\n\t");
    st->print("j skip\n\t");
    st->print("guard: int\n\t");
    st->print("skip:\n\t");
  }
}
#endif

void MachPrologNode::emit(CodeBuffer &cbuf, PhaseRegAlloc *ra_) const {
  assert_cond(ra_ != NULL);
  Compile* C = ra_->C;
  C2_MacroAssembler _masm(&cbuf);

  // n.b. frame size includes space for return pc and fp
  const int framesize = C->output()->frame_size_in_bytes();

  // insert a nop at the start of the prolog so we can patch in a
  // branch if we need to invalidate the method later
  {
    Assembler::IncompressibleRegion ir(&_masm);  // keep the nop as 4 bytes for patching.
    MacroAssembler::assert_alignment(__ pc());
    __ nop();  // 4 bytes
  }

  assert_cond(C != NULL);

  if (C->clinit_barrier_on_entry()) {
    assert(!C->method()->holder()->is_not_initialized(), "initialization should have been started");

    Label L_skip_barrier;

    __ mov_metadata(t1, C->method()->holder()->constant_encoding());
    __ clinit_barrier(t1, t0, &L_skip_barrier);
    __ far_jump(RuntimeAddress(SharedRuntime::get_handle_wrong_method_stub()));
    __ bind(L_skip_barrier);
  }

  int bangsize = C->output()->bang_size_in_bytes();
  if (C->output()->need_stack_bang(bangsize)) {
    __ generate_stack_overflow_check(bangsize);
  }

  __ build_frame(framesize);

  if (C->stub_function() == NULL) {
    BarrierSetAssembler* bs = BarrierSet::barrier_set()->barrier_set_assembler();
    if (BarrierSet::barrier_set()->barrier_set_nmethod() != NULL) {
      // Dummy labels for just measuring the code size
      Label dummy_slow_path;
      Label dummy_continuation;
      Label dummy_guard;
      Label* slow_path = &dummy_slow_path;
      Label* continuation = &dummy_continuation;
      Label* guard = &dummy_guard;
      if (!Compile::current()->output()->in_scratch_emit_size()) {
        // Use real labels from actual stub when not emitting code for purpose of measuring its size
        C2EntryBarrierStub* stub = Compile::current()->output()->entry_barrier_table()->add_entry_barrier();
        slow_path = &stub->slow_path();
        continuation = &stub->continuation();
        guard = &stub->guard();
      }
      // In the C2 code, we move the non-hot part of nmethod entry barriers out-of-line to a stub.
      bs->nmethod_entry_barrier(&_masm, slow_path, continuation, guard);
    }
  }

  if (VerifyStackAtCalls) {
    Unimplemented();
  }

  C->output()->set_frame_complete(cbuf.insts_size());

  if (C->has_mach_constant_base_node()) {
    // NOTE: We set the table base offset here because users might be
    // emitted before MachConstantBaseNode.
    ConstantTable& constant_table = C->output()->constant_table();
    constant_table.set_table_base_offset(constant_table.calculate_table_base_offset());
  }
}

uint MachPrologNode::size(PhaseRegAlloc* ra_) const
{
  assert_cond(ra_ != NULL);
  return MachNode::size(ra_); // too many variables; just compute it
                              // the hard way
}

int MachPrologNode::reloc() const
{
  return 0;
}

//=============================================================================

#ifndef PRODUCT
void MachEpilogNode::format(PhaseRegAlloc *ra_, outputStream *st) const {
  assert_cond(st != NULL && ra_ != NULL);
  Compile* C = ra_->C;
  assert_cond(C != NULL);
  int framesize = C->output()->frame_size_in_bytes();

  st->print("# pop frame %d\n\t", framesize);

  if (framesize == 0) {
    st->print("ld  ra, [sp,#%d]\n\t", (2 * wordSize));
    st->print("ld  fp, [sp,#%d]\n\t", (3 * wordSize));
    st->print("add sp, sp, #%d\n\t", (2 * wordSize));
  } else {
    st->print("add  sp, sp, #%d\n\t", framesize);
    st->print("ld  ra, [sp,#%d]\n\t", - 2 * wordSize);
    st->print("ld  fp, [sp,#%d]\n\t", - wordSize);
  }

  if (do_polling() && C->is_method_compilation()) {
    st->print("# test polling word\n\t");
    st->print("ld t0, [xthread,#%d]\n\t", in_bytes(JavaThread::polling_word_offset()));
    st->print("bgtu sp, t0, #slow_path");
  }
}
#endif

void MachEpilogNode::emit(CodeBuffer &cbuf, PhaseRegAlloc *ra_) const {
  assert_cond(ra_ != NULL);
  Compile* C = ra_->C;
  C2_MacroAssembler _masm(&cbuf);
  assert_cond(C != NULL);
  int framesize = C->output()->frame_size_in_bytes();

  __ remove_frame(framesize);

  if (StackReservedPages > 0 && C->has_reserved_stack_access()) {
    __ reserved_stack_check();
  }

  if (do_polling() && C->is_method_compilation()) {
    Label dummy_label;
    Label* code_stub = &dummy_label;
    if (!C->output()->in_scratch_emit_size()) {
      code_stub = &C->output()->safepoint_poll_table()->add_safepoint(__ offset());
    }
    __ relocate(relocInfo::poll_return_type);
    __ safepoint_poll(*code_stub, true /* at_return */, false /* acquire */, true /* in_nmethod */);
  }
}

uint MachEpilogNode::size(PhaseRegAlloc *ra_) const {
  assert_cond(ra_ != NULL);
  // Variable size. Determine dynamically.
  return MachNode::size(ra_);
}

int MachEpilogNode::reloc() const {
  // Return number of relocatable values contained in this instruction.
  return 1; // 1 for polling page.
}
const Pipeline * MachEpilogNode::pipeline() const {
  return MachNode::pipeline_class();
}

//=============================================================================

// Figure out which register class each belongs in: rc_int, rc_float or
// rc_stack.
enum RC { rc_bad, rc_int, rc_float, rc_vector, rc_stack };

static enum RC rc_class(OptoReg::Name reg) {

  if (reg == OptoReg::Bad) {
    return rc_bad;
  }

  // we have 30 int registers * 2 halves
  // (t0 and t1 are omitted)
  int slots_of_int_registers = Register::max_slots_per_register * (Register::number_of_registers - 2);
  if (reg < slots_of_int_registers) {
    return rc_int;
  }

  // we have 32 float register * 2 halves
  int slots_of_float_registers = FloatRegister::max_slots_per_register * FloatRegister::number_of_registers;
  if (reg < slots_of_int_registers + slots_of_float_registers) {
    return rc_float;
  }

  // we have 32 vector register * 4 halves
  int slots_of_vector_registers = VectorRegister::max_slots_per_register * VectorRegister::number_of_registers;
  if (reg < slots_of_int_registers + slots_of_float_registers + slots_of_vector_registers) {
    return rc_vector;
  }

  // Between vector regs & stack is the flags regs.
  assert(OptoReg::is_stack(reg), "blow up if spilling flags");

  return rc_stack;
}

uint MachSpillCopyNode::implementation(CodeBuffer *cbuf, PhaseRegAlloc *ra_, bool do_size, outputStream *st) const {
  assert_cond(ra_ != NULL);
  Compile* C = ra_->C;

  // Get registers to move.
  OptoReg::Name src_hi = ra_->get_reg_second(in(1));
  OptoReg::Name src_lo = ra_->get_reg_first(in(1));
  OptoReg::Name dst_hi = ra_->get_reg_second(this);
  OptoReg::Name dst_lo = ra_->get_reg_first(this);

  enum RC src_hi_rc = rc_class(src_hi);
  enum RC src_lo_rc = rc_class(src_lo);
  enum RC dst_hi_rc = rc_class(dst_hi);
  enum RC dst_lo_rc = rc_class(dst_lo);

  assert(src_lo != OptoReg::Bad && dst_lo != OptoReg::Bad, "must move at least 1 register");

  if (src_hi != OptoReg::Bad) {
    assert((src_lo & 1) == 0 && src_lo + 1 == src_hi &&
           (dst_lo & 1) == 0 && dst_lo + 1 == dst_hi,
           "expected aligned-adjacent pairs");
  }

  if (src_lo == dst_lo && src_hi == dst_hi) {
    return 0;            // Self copy, no move.
  }

  bool is64 = (src_lo & 1) == 0 && src_lo + 1 == src_hi &&
              (dst_lo & 1) == 0 && dst_lo + 1 == dst_hi;
  int src_offset = ra_->reg2offset(src_lo);
  int dst_offset = ra_->reg2offset(dst_lo);

  if (bottom_type()->isa_vect() != NULL) {
    uint ireg = ideal_reg();
    if (ireg == Op_VecA && cbuf) {
      C2_MacroAssembler _masm(cbuf);
      int vector_reg_size_in_bytes = Matcher::scalable_vector_reg_size(T_BYTE);
      if (src_lo_rc == rc_stack && dst_lo_rc == rc_stack) {
        // stack to stack
        __ spill_copy_vector_stack_to_stack(src_offset, dst_offset,
                                            vector_reg_size_in_bytes);
      } else if (src_lo_rc == rc_vector && dst_lo_rc == rc_stack) {
        // vpr to stack
        __ spill(as_VectorRegister(Matcher::_regEncode[src_lo]), ra_->reg2offset(dst_lo));
      } else if (src_lo_rc == rc_stack && dst_lo_rc == rc_vector) {
        // stack to vpr
        __ unspill(as_VectorRegister(Matcher::_regEncode[dst_lo]), ra_->reg2offset(src_lo));
      } else if (src_lo_rc == rc_vector && dst_lo_rc == rc_vector) {
        // vpr to vpr
        __ vmv1r_v(as_VectorRegister(Matcher::_regEncode[dst_lo]), as_VectorRegister(Matcher::_regEncode[src_lo]));
      } else {
        ShouldNotReachHere();
      }
    }
  } else if (cbuf != NULL) {
    C2_MacroAssembler _masm(cbuf);
    switch (src_lo_rc) {
      case rc_int:
        if (dst_lo_rc == rc_int) {  // gpr --> gpr copy
          if (!is64 && this->ideal_reg() != Op_RegI) { // zero extended for narrow oop or klass
            __ zero_extend(as_Register(Matcher::_regEncode[dst_lo]), as_Register(Matcher::_regEncode[src_lo]), 32);
          } else {
            __ mv(as_Register(Matcher::_regEncode[dst_lo]), as_Register(Matcher::_regEncode[src_lo]));
          }
        } else if (dst_lo_rc == rc_float) { // gpr --> fpr copy
          if (is64) {
            __ fmv_d_x(as_FloatRegister(Matcher::_regEncode[dst_lo]),
                       as_Register(Matcher::_regEncode[src_lo]));
          } else {
            __ fmv_w_x(as_FloatRegister(Matcher::_regEncode[dst_lo]),
                       as_Register(Matcher::_regEncode[src_lo]));
          }
        } else {                    // gpr --> stack spill
          assert(dst_lo_rc == rc_stack, "spill to bad register class");
          __ spill(as_Register(Matcher::_regEncode[src_lo]), is64, dst_offset);
        }
        break;
      case rc_float:
        if (dst_lo_rc == rc_int) {  // fpr --> gpr copy
          if (is64) {
            __ fmv_x_d(as_Register(Matcher::_regEncode[dst_lo]),
                       as_FloatRegister(Matcher::_regEncode[src_lo]));
          } else {
            __ fmv_x_w(as_Register(Matcher::_regEncode[dst_lo]),
                       as_FloatRegister(Matcher::_regEncode[src_lo]));
          }
        } else if (dst_lo_rc == rc_float) { // fpr --> fpr copy
          if (is64) {
            __ fmv_d(as_FloatRegister(Matcher::_regEncode[dst_lo]),
                     as_FloatRegister(Matcher::_regEncode[src_lo]));
          } else {
            __ fmv_s(as_FloatRegister(Matcher::_regEncode[dst_lo]),
                     as_FloatRegister(Matcher::_regEncode[src_lo]));
          }
        } else {                    // fpr --> stack spill
          assert(dst_lo_rc == rc_stack, "spill to bad register class");
          __ spill(as_FloatRegister(Matcher::_regEncode[src_lo]),
                   is64, dst_offset);
        }
        break;
      case rc_stack:
        if (dst_lo_rc == rc_int) {  // stack --> gpr load
          if (this->ideal_reg() == Op_RegI) {
            __ unspill(as_Register(Matcher::_regEncode[dst_lo]), is64, src_offset);
          } else { // // zero extended for narrow oop or klass
            __ unspillu(as_Register(Matcher::_regEncode[dst_lo]), is64, src_offset);
          }
        } else if (dst_lo_rc == rc_float) { // stack --> fpr load
          __ unspill(as_FloatRegister(Matcher::_regEncode[dst_lo]),
                     is64, src_offset);
        } else {                    // stack --> stack copy
          assert(dst_lo_rc == rc_stack, "spill to bad register class");
          if (this->ideal_reg() == Op_RegI) {
            __ unspill(t0, is64, src_offset);
          } else { // zero extended for narrow oop or klass
            __ unspillu(t0, is64, src_offset);
          }
          __ spill(t0, is64, dst_offset);
        }
        break;
      default:
        ShouldNotReachHere();
    }
  }

  if (st != NULL) {
    st->print("spill ");
    if (src_lo_rc == rc_stack) {
      st->print("[sp, #%d] -> ", src_offset);
    } else {
      st->print("%s -> ", Matcher::regName[src_lo]);
    }
    if (dst_lo_rc == rc_stack) {
      st->print("[sp, #%d]", dst_offset);
    } else {
      st->print("%s", Matcher::regName[dst_lo]);
    }
    if (bottom_type()->isa_vect() != NULL) {
      int vsize = 0;
      if (ideal_reg() == Op_VecA) {
        vsize = Matcher::scalable_vector_reg_size(T_BYTE) * 8;
      } else {
        ShouldNotReachHere();
      }
      st->print("\t# vector spill size = %d", vsize);
    } else {
      st->print("\t# spill size = %d", is64 ? 64 : 32);
    }
  }

  return 0;
}

#ifndef PRODUCT
void MachSpillCopyNode::format(PhaseRegAlloc *ra_, outputStream *st) const {
  if (ra_ == NULL) {
    st->print("N%d = SpillCopy(N%d)", _idx, in(1)->_idx);
  } else {
    implementation(NULL, ra_, false, st);
  }
}
#endif

void MachSpillCopyNode::emit(CodeBuffer &cbuf, PhaseRegAlloc *ra_) const {
  implementation(&cbuf, ra_, false, NULL);
}

uint MachSpillCopyNode::size(PhaseRegAlloc *ra_) const {
  return MachNode::size(ra_);
}

//=============================================================================

#ifndef PRODUCT
void BoxLockNode::format(PhaseRegAlloc *ra_, outputStream *st) const {
  assert_cond(ra_ != NULL && st != NULL);
  int offset = ra_->reg2offset(in_RegMask(0).find_first_elem());
  int reg = ra_->get_reg_first(this);
  st->print("add %s, sp, #%d\t# box lock",
            Matcher::regName[reg], offset);
}
#endif

void BoxLockNode::emit(CodeBuffer &cbuf, PhaseRegAlloc *ra_) const {
  C2_MacroAssembler _masm(&cbuf);
  Assembler::IncompressibleRegion ir(&_masm);  // Fixed length: see BoxLockNode::size()

  assert_cond(ra_ != NULL);
  int offset = ra_->reg2offset(in_RegMask(0).find_first_elem());
  int reg    = ra_->get_encode(this);

  if (is_imm_in_range(offset, 12, 0)) {
    __ addi(as_Register(reg), sp, offset);
  } else if (is_imm_in_range(offset, 32, 0)) {
    __ li32(t0, offset);
    __ add(as_Register(reg), sp, t0);
  } else {
    ShouldNotReachHere();
  }
}

uint BoxLockNode::size(PhaseRegAlloc *ra_) const {
  // BoxLockNode is not a MachNode, so we can't just call MachNode::size(ra_).
  int offset = ra_->reg2offset(in_RegMask(0).find_first_elem());

  if (is_imm_in_range(offset, 12, 0)) {
    return NativeInstruction::instruction_size;
  } else {
    return 3 * NativeInstruction::instruction_size; // lui + addiw + add;
  }
}

//=============================================================================

#ifndef PRODUCT
void MachUEPNode::format(PhaseRegAlloc* ra_, outputStream* st) const
{
  assert_cond(st != NULL);
  st->print_cr("# MachUEPNode");
  if (UseCompressedClassPointers) {
    st->print_cr("\tlwu t0, [j_rarg0, oopDesc::klass_offset_in_bytes()]\t# compressed klass");
    if (CompressedKlassPointers::shift() != 0) {
      st->print_cr("\tdecode_klass_not_null t0, t0");
    }
  } else {
    st->print_cr("\tld t0, [j_rarg0, oopDesc::klass_offset_in_bytes()]\t# compressed klass");
  }
  st->print_cr("\tbeq t0, t1, ic_hit");
  st->print_cr("\tj, SharedRuntime::_ic_miss_stub\t # Inline cache check");
  st->print_cr("\tic_hit:");
}
#endif

void MachUEPNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const
{
  // This is the unverified entry point.
  C2_MacroAssembler _masm(&cbuf);

  Label skip;
  __ cmp_klass(j_rarg0, t1, t0, skip);
  __ far_jump(RuntimeAddress(SharedRuntime::get_ic_miss_stub()));
  __ bind(skip);

  // These NOPs are critical so that verified entry point is properly
  // 4 bytes aligned for patching by NativeJump::patch_verified_entry()
  __ align(NativeInstruction::instruction_size);
}

uint MachUEPNode::size(PhaseRegAlloc* ra_) const
{
  assert_cond(ra_ != NULL);
  return MachNode::size(ra_);
}

// REQUIRED EMIT CODE

//=============================================================================

// Emit exception handler code.
int HandlerImpl::emit_exception_handler(CodeBuffer& cbuf)
{
  // la_patchable t0, #exception_blob_entry_point
  // jr (offset)t0
  // or
  // j #exception_blob_entry_point
  // Note that the code buffer's insts_mark is always relative to insts.
  // That's why we must use the macroassembler to generate a handler.
  C2_MacroAssembler _masm(&cbuf);
  address base = __ start_a_stub(size_exception_handler());
  if (base == NULL) {
    ciEnv::current()->record_failure("CodeCache is full");
    return 0;  // CodeBuffer::expand failed
  }
  int offset = __ offset();
  __ far_jump(RuntimeAddress(OptoRuntime::exception_blob()->entry_point()));
  assert(__ offset() - offset <= (int) size_exception_handler(), "overflow");
  __ end_a_stub();
  return offset;
}

// Emit deopt handler code.
int HandlerImpl::emit_deopt_handler(CodeBuffer& cbuf)
{
  // Note that the code buffer's insts_mark is always relative to insts.
  // That's why we must use the macroassembler to generate a handler.
  C2_MacroAssembler _masm(&cbuf);
  address base = __ start_a_stub(size_deopt_handler());
  if (base == NULL) {
    ciEnv::current()->record_failure("CodeCache is full");
    return 0;  // CodeBuffer::expand failed
  }
  int offset = __ offset();

  __ auipc(ra, 0);
  __ far_jump(RuntimeAddress(SharedRuntime::deopt_blob()->unpack()));

  assert(__ offset() - offset <= (int) size_deopt_handler(), "overflow");
  __ end_a_stub();
  return offset;

}
// REQUIRED MATCHER CODE

//=============================================================================

const bool Matcher::match_rule_supported(int opcode) {
  if (!has_match_rule(opcode)) {
    return false;
  }

  switch (opcode) {
    case Op_CacheWB:           // fall through
    case Op_CacheWBPreSync:    // fall through
    case Op_CacheWBPostSync:
      if (!VM_Version::supports_data_cache_line_flush()) {
        return false;
      }
      break;

    case Op_StrCompressedCopy: // fall through
    case Op_StrInflatedCopy:   // fall through
    case Op_CountPositives:
      return UseRVV;

    case Op_EncodeISOArray:
      return UseRVV && SpecialEncodeISOArray;

    case Op_PopCountI:
    case Op_PopCountL:
      return UsePopCountInstruction;

    case Op_RotateRight:
    case Op_RotateLeft:
    case Op_CountLeadingZerosI:
    case Op_CountLeadingZerosL:
    case Op_CountTrailingZerosI:
    case Op_CountTrailingZerosL:
      return UseZbb;
  }

  return true; // Per default match rules are supported.
}

const bool Matcher::match_rule_supported_superword(int opcode, int vlen, BasicType bt) {
  return match_rule_supported_vector(opcode, vlen, bt);
}

// Identify extra cases that we might want to provide match rules for vector nodes and
// other intrinsics guarded with vector length (vlen) and element type (bt).
const bool Matcher::match_rule_supported_vector(int opcode, int vlen, BasicType bt) {
  if (!match_rule_supported(opcode) || !vector_size_supported(bt, vlen)) {
    return false;
  }

  return op_vec_supported(opcode);
}

const bool Matcher::match_rule_supported_vector_masked(int opcode, int vlen, BasicType bt) {
  switch (opcode) {
    case Op_AddVI:
      return UseRVV;
    default:
      return false;
  }
}

const bool Matcher::vector_needs_partial_operations(Node* node, const TypeVect* vt) {
  return false;
}

const RegMask* Matcher::predicate_reg_mask(void) {
  return &_PR_REG_mask;
}

const TypeVectMask* Matcher::predicate_reg_type(const Type* elemTy, int length) {
  return new TypeVectMask(elemTy, length);
}

// Vector calling convention not yet implemented.
const bool Matcher::supports_vector_calling_convention(void) {
  return false;
}

OptoRegPair Matcher::vector_return_value(uint ideal_reg) {
  Unimplemented();
  return OptoRegPair(0, 0);
}

// Is this branch offset short enough that a short branch can be used?
//
// NOTE: If the platform does not provide any short branch variants, then
//       this method should return false for offset 0.
// |---label(L1)-----|
// |-----------------|
// |-----------------|----------eq: float-------------------
// |-----------------| // far_cmpD_branch   |   cmpD_branch
// |------- ---------|    feq;              |      feq;
// |-far_cmpD_branch-|    beqz done;        |      bnez L;
// |-----------------|    j L;              |
// |-----------------|    bind(done);       |
// |-----------------|--------------------------------------
// |-----------------| // so shortBrSize = br_size - 4;
// |-----------------| // so offs = offset - shortBrSize + 4;
// |---label(L2)-----|
bool Matcher::is_short_branch_offset(int rule, int br_size, int offset) {
  // The passed offset is relative to address of the branch.
  int shortBrSize = br_size - 4;
  int offs = offset - shortBrSize + 4;
  return (-4096 <= offs && offs < 4096);
}

// Vector width in bytes.
const int Matcher::vector_width_in_bytes(BasicType bt) {
  if (UseRVV) {
    // The MaxVectorSize should have been set by detecting RVV max vector register size when check UseRVV.
    // MaxVectorSize == VM_Version::_initial_vector_length
    return MaxVectorSize;
  }
  return 0;
}

// Limits on vector size (number of elements) loaded into vector.
const int Matcher::max_vector_size(const BasicType bt) {
  return vector_width_in_bytes(bt) / type2aelembytes(bt);
}
const int Matcher::min_vector_size(const BasicType bt) {
  return max_vector_size(bt);
}

// Vector ideal reg.
const uint Matcher::vector_ideal_reg(int len) {
  assert(MaxVectorSize >= len, "");
  if (UseRVV) {
    return Op_VecA;
  }

  ShouldNotReachHere();
  return 0;
}

const int Matcher::scalable_vector_reg_size(const BasicType bt) {
  return Matcher::max_vector_size(bt);
}

MachOper* Matcher::pd_specialize_generic_vector_operand(MachOper* original_opnd, uint ideal_reg, bool is_temp) {
  ShouldNotReachHere(); // generic vector operands not supported
  return NULL;
}

bool Matcher::is_reg2reg_move(MachNode* m) {
  ShouldNotReachHere(); // generic vector operands not supported
  return false;
}

bool Matcher::is_generic_vector(MachOper* opnd) {
  ShouldNotReachHere(); // generic vector operands not supported
  return false;
}

// Return whether or not this register is ever used as an argument.
// This function is used on startup to build the trampoline stubs in
// generateOptoStub.  Registers not mentioned will be killed by the VM
// call in the trampoline, and arguments in those registers not be
// available to the callee.
bool Matcher::can_be_java_arg(int reg)
{
  return
    reg ==  R10_num || reg == R10_H_num ||
    reg ==  R11_num || reg == R11_H_num ||
    reg ==  R12_num || reg == R12_H_num ||
    reg ==  R13_num || reg == R13_H_num ||
    reg ==  R14_num || reg == R14_H_num ||
    reg ==  R15_num || reg == R15_H_num ||
    reg ==  R16_num || reg == R16_H_num ||
    reg ==  R17_num || reg == R17_H_num ||
    reg ==  F10_num || reg == F10_H_num ||
    reg ==  F11_num || reg == F11_H_num ||
    reg ==  F12_num || reg == F12_H_num ||
    reg ==  F13_num || reg == F13_H_num ||
    reg ==  F14_num || reg == F14_H_num ||
    reg ==  F15_num || reg == F15_H_num ||
    reg ==  F16_num || reg == F16_H_num ||
    reg ==  F17_num || reg == F17_H_num;
}

bool Matcher::is_spillable_arg(int reg)
{
  return can_be_java_arg(reg);
}

uint Matcher::int_pressure_limit()
{
  // A derived pointer is live at CallNode and then is flagged by RA
  // as a spilled LRG. Spilling heuristics(Spill-USE) explicitly skip
  // derived pointers and lastly fail to spill after reaching maximum
  // number of iterations. Lowering the default pressure threshold to
  // (_NO_SPECIAL_REG32_mask.Size() minus 1) forces CallNode to become
  // a high register pressure area of the code so that split_DEF can
  // generate DefinitionSpillCopy for the derived pointer.
  uint default_int_pressure_threshold = _NO_SPECIAL_REG32_mask.Size() - 1;
  if (!PreserveFramePointer) {
    // When PreserveFramePointer is off, frame pointer is allocatable,
    // but different from other SOC registers, it is excluded from
    // fatproj's mask because its save type is No-Save. Decrease 1 to
    // ensure high pressure at fatproj when PreserveFramePointer is off.
    // See check_pressure_at_fatproj().
    default_int_pressure_threshold--;
  }
  return (INTPRESSURE == -1) ? default_int_pressure_threshold : INTPRESSURE;
}

uint Matcher::float_pressure_limit()
{
  // _FLOAT_REG_mask is generated by adlc from the float_reg register class.
  return (FLOATPRESSURE == -1) ? _FLOAT_REG_mask.Size() : FLOATPRESSURE;
}

bool Matcher::use_asm_for_ldiv_by_con(jlong divisor) {
  return false;
}

RegMask Matcher::divI_proj_mask() {
  ShouldNotReachHere();
  return RegMask();
}

// Register for MODI projection of divmodI.
RegMask Matcher::modI_proj_mask() {
  ShouldNotReachHere();
  return RegMask();
}

// Register for DIVL projection of divmodL.
RegMask Matcher::divL_proj_mask() {
  ShouldNotReachHere();
  return RegMask();
}

// Register for MODL projection of divmodL.
RegMask Matcher::modL_proj_mask() {
  ShouldNotReachHere();
  return RegMask();
}

const RegMask Matcher::method_handle_invoke_SP_save_mask() {
  return FP_REG_mask();
}

bool size_fits_all_mem_uses(AddPNode* addp, int shift) {
  assert_cond(addp != NULL);
  for (DUIterator_Fast imax, i = addp->fast_outs(imax); i < imax; i++) {
    Node* u = addp->fast_out(i);
    if (u != NULL && u->is_Mem()) {
      int opsize = u->as_Mem()->memory_size();
      assert(opsize > 0, "unexpected memory operand size");
      if (u->as_Mem()->memory_size() != (1 << shift)) {
        return false;
      }
    }
  }
  return true;
}

// Should the Matcher clone input 'm' of node 'n'?
bool Matcher::pd_clone_node(Node* n, Node* m, Matcher::MStack& mstack) {
  assert_cond(m != NULL);
  if (is_vshift_con_pattern(n, m)) { // ShiftV src (ShiftCntV con)
    mstack.push(m, Visit);           // m = ShiftCntV
    return true;
  }
  return false;
}

// Should the Matcher clone shifts on addressing modes, expecting them
// to be subsumed into complex addressing expressions or compute them
// into registers?
bool Matcher::pd_clone_address_expressions(AddPNode* m, Matcher::MStack& mstack, VectorSet& address_visited) {
  return clone_base_plus_offset_address(m, mstack, address_visited);
}


#line 1117 "ad_riscv.cpp"


//SourceForm

#line 35 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"


  static void loadStore(C2_MacroAssembler masm, bool is_store,
                        VectorRegister reg, BasicType bt, Register base) {
    Assembler::SEW sew = Assembler::elemtype_to_sew(bt);
    masm.vsetvli(t0, x0, sew);
    if (is_store) {
      masm.vsex_v(reg, base, sew);
    } else {
      masm.vlex_v(reg, base, sew);
    }
  }

  bool op_vec_supported(int opcode) {
    switch (opcode) {
      // No multiply reduction instructions
      case Op_MulReductionVD:
      case Op_MulReductionVF:
      case Op_MulReductionVI:
      case Op_MulReductionVL:
      // Others
      case Op_Extract:
      case Op_ExtractB:
      case Op_ExtractC:
      case Op_ExtractD:
      case Op_ExtractF:
      case Op_ExtractI:
      case Op_ExtractL:
      case Op_ExtractS:
      case Op_ExtractUB:
      // Vector API specific
      case Op_LoadVectorGather:
      case Op_StoreVectorScatter:
      case Op_VectorBlend:
      case Op_VectorCast:
      case Op_VectorCastB2X:
      case Op_VectorCastD2X:
      case Op_VectorCastF2X:
      case Op_VectorCastI2X:
      case Op_VectorCastL2X:
      case Op_VectorCastS2X:
      case Op_VectorInsert:
      case Op_VectorLoadConst:
      case Op_VectorLoadMask:
      case Op_VectorLoadShuffle:
      case Op_VectorMaskCmp:
      case Op_VectorRearrange:
      case Op_VectorReinterpret:
      case Op_VectorStoreMask:
      case Op_VectorTest:
      case Op_PopCountVI:
      case Op_PopCountVL:
        return false;
      default:
        return UseRVV;
    }
  }


#line 1182 "ad_riscv.cpp"


//SourceForm

#line 33 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/gc/z/z_riscv64.ad"


static void z_load_barrier(MacroAssembler& _masm, const MachNode* node, Address ref_addr, Register ref, Register tmp, int barrier_data) {
  if (barrier_data == ZLoadBarrierElided) {
    return;
  }
  ZLoadBarrierStubC2* const stub = ZLoadBarrierStubC2::create(node, ref_addr, ref, tmp, barrier_data);
  __ ld(tmp, Address(xthread, ZThreadLocalData::address_bad_mask_offset()));
  __ andr(tmp, tmp, ref);
  __ bnez(tmp, *stub->entry(), true /* far */);
  __ bind(*stub->continuation());
}

static void z_load_barrier_slow_path(MacroAssembler& _masm, const MachNode* node, Address ref_addr, Register ref, Register tmp) {
  ZLoadBarrierStubC2* const stub = ZLoadBarrierStubC2::create(node, ref_addr, ref, tmp, ZLoadBarrierStrong);
  __ j(*stub->entry());
  __ bind(*stub->continuation());
}


#line 1208 "ad_riscv.cpp"


#ifndef PRODUCT
void Compile::adlc_verification() {

  // Following assertions generated from definition section
  assert( DEFAULT_COST == 100, "Expect (100) to equal 100");
  assert( ALU_COST == 100, "Expect (1 * DEFAULT_COST) to equal 100");
  assert( LOAD_COST == 300, "Expect (3 * DEFAULT_COST) to equal 300");
  assert( STORE_COST == 100, "Expect (1 * DEFAULT_COST) to equal 100");
  assert( XFER_COST == 300, "Expect (3 * DEFAULT_COST) to equal 300");
  assert( BRANCH_COST == 100, "Expect (1 * DEFAULT_COST) to equal 100");
  assert( IMUL_COST == 1000, "Expect (10 * DEFAULT_COST) to equal 1000");
  assert( IDIVSI_COST == 3400, "Expect (34 * DEFAULT_COST) to equal 3400");
  assert( IDIVDI_COST == 6600, "Expect (66 * DEFAULT_COST) to equal 6600");
  assert( FMUL_SINGLE_COST == 500, "Expect (5 * DEFAULT_COST) to equal 500");
  assert( FMUL_DOUBLE_COST == 700, "Expect (7 * DEFAULT_COST) to equal 700");
  assert( FDIV_COST == 2000, "Expect (20 * DEFAULT_COST) to equal 2000");
  assert( FSQRT_COST == 2500, "Expect (25 * DEFAULT_COST) to equal 2500");
  assert( VOLATILE_REF_COST == 1000, "Expect (10 * DEFAULT_COST) to equal 1000");
  assert( VEC_COST == 200, "Expect (200) to equal 200");
}
#endif

// Map from machine-independent register number to register_save_policy
const        char register_save_policy[] = {
  'C', // R7
  'C', // R7_H
  'C', // R28
  'C', // R28_H
  'C', // R29
  'C', // R29_H
  'C', // R30
  'C', // R30_H
  'C', // R31
  'C', // R31_H
  'C', // R10
  'C', // R10_H
  'C', // R11
  'C', // R11_H
  'C', // R12
  'C', // R12_H
  'C', // R13
  'C', // R13_H
  'C', // R14
  'C', // R14_H
  'C', // R15
  'C', // R15_H
  'C', // R16
  'C', // R16_H
  'C', // R17
  'C', // R17_H
  'C', // R9
  'C', // R9_H
  'C', // R18
  'C', // R18_H
  'C', // R19
  'C', // R19_H
  'C', // R20
  'C', // R20_H
  'C', // R21
  'C', // R21_H
  'C', // R22
  'C', // R22_H
  'C', // R24
  'C', // R24_H
  'C', // R25
  'C', // R25_H
  'C', // R26
  'C', // R26_H
  'N', // R23
  'N', // R23_H
  'C', // R27
  'C', // R27_H
  'N', // R4
  'N', // R4_H
  'N', // R8
  'N', // R8_H
  'N', // R0
  'N', // R0_H
  'N', // R1
  'N', // R1_H
  'N', // R2
  'N', // R2_H
  'N', // R3
  'N', // R3_H
  'C', // F0
  'C', // F0_H
  'C', // F1
  'C', // F1_H
  'C', // F2
  'C', // F2_H
  'C', // F3
  'C', // F3_H
  'C', // F4
  'C', // F4_H
  'C', // F5
  'C', // F5_H
  'C', // F6
  'C', // F6_H
  'C', // F7
  'C', // F7_H
  'C', // F28
  'C', // F28_H
  'C', // F29
  'C', // F29_H
  'C', // F30
  'C', // F30_H
  'C', // F31
  'C', // F31_H
  'C', // F10
  'C', // F10_H
  'C', // F11
  'C', // F11_H
  'C', // F12
  'C', // F12_H
  'C', // F13
  'C', // F13_H
  'C', // F14
  'C', // F14_H
  'C', // F15
  'C', // F15_H
  'C', // F16
  'C', // F16_H
  'C', // F17
  'C', // F17_H
  'C', // F8
  'C', // F8_H
  'C', // F9
  'C', // F9_H
  'C', // F18
  'C', // F18_H
  'C', // F19
  'C', // F19_H
  'C', // F20
  'C', // F20_H
  'C', // F21
  'C', // F21_H
  'C', // F22
  'C', // F22_H
  'C', // F23
  'C', // F23_H
  'C', // F24
  'C', // F24_H
  'C', // F25
  'C', // F25_H
  'C', // F26
  'C', // F26_H
  'C', // F27
  'C', // F27_H
  'C', // V0
  'C', // V0_H
  'C', // V0_J
  'C', // V0_K
  'C', // V1
  'C', // V1_H
  'C', // V1_J
  'C', // V1_K
  'C', // V2
  'C', // V2_H
  'C', // V2_J
  'C', // V2_K
  'C', // V3
  'C', // V3_H
  'C', // V3_J
  'C', // V3_K
  'C', // V4
  'C', // V4_H
  'C', // V4_J
  'C', // V4_K
  'C', // V5
  'C', // V5_H
  'C', // V5_J
  'C', // V5_K
  'C', // V6
  'C', // V6_H
  'C', // V6_J
  'C', // V6_K
  'C', // V7
  'C', // V7_H
  'C', // V7_J
  'C', // V7_K
  'C', // V8
  'C', // V8_H
  'C', // V8_J
  'C', // V8_K
  'C', // V9
  'C', // V9_H
  'C', // V9_J
  'C', // V9_K
  'C', // V10
  'C', // V10_H
  'C', // V10_J
  'C', // V10_K
  'C', // V11
  'C', // V11_H
  'C', // V11_J
  'C', // V11_K
  'C', // V12
  'C', // V12_H
  'C', // V12_J
  'C', // V12_K
  'C', // V13
  'C', // V13_H
  'C', // V13_J
  'C', // V13_K
  'C', // V14
  'C', // V14_H
  'C', // V14_J
  'C', // V14_K
  'C', // V15
  'C', // V15_H
  'C', // V15_J
  'C', // V15_K
  'C', // V16
  'C', // V16_H
  'C', // V16_J
  'C', // V16_K
  'C', // V17
  'C', // V17_H
  'C', // V17_J
  'C', // V17_K
  'C', // V18
  'C', // V18_H
  'C', // V18_J
  'C', // V18_K
  'C', // V19
  'C', // V19_H
  'C', // V19_J
  'C', // V19_K
  'C', // V20
  'C', // V20_H
  'C', // V20_J
  'C', // V20_K
  'C', // V21
  'C', // V21_H
  'C', // V21_J
  'C', // V21_K
  'C', // V22
  'C', // V22_H
  'C', // V22_J
  'C', // V22_K
  'C', // V23
  'C', // V23_H
  'C', // V23_J
  'C', // V23_K
  'C', // V24
  'C', // V24_H
  'C', // V24_J
  'C', // V24_K
  'C', // V25
  'C', // V25_H
  'C', // V25_J
  'C', // V25_K
  'C', // V26
  'C', // V26_H
  'C', // V26_J
  'C', // V26_K
  'C', // V27
  'C', // V27_H
  'C', // V27_J
  'C', // V27_K
  'C', // V28
  'C', // V28_H
  'C', // V28_J
  'C', // V28_K
  'C', // V29
  'C', // V29_H
  'C', // V29_J
  'C', // V29_K
  'C', // V30
  'C', // V30_H
  'C', // V30_J
  'C', // V30_K
  'C', // V31
  'C', // V31_H
  'C', // V31_J
  'C', // V31_K
  'C' // no trailing comma // RFLAGS
};

// Map from machine-independent register number to c_reg_save_policy
const        char c_reg_save_policy[] = {
  'C', // R7
  'C', // R7_H
  'C', // R28
  'C', // R28_H
  'C', // R29
  'C', // R29_H
  'C', // R30
  'C', // R30_H
  'C', // R31
  'C', // R31_H
  'C', // R10
  'C', // R10_H
  'C', // R11
  'C', // R11_H
  'C', // R12
  'C', // R12_H
  'C', // R13
  'C', // R13_H
  'C', // R14
  'C', // R14_H
  'C', // R15
  'C', // R15_H
  'C', // R16
  'C', // R16_H
  'C', // R17
  'C', // R17_H
  'E', // R9
  'E', // R9_H
  'E', // R18
  'E', // R18_H
  'E', // R19
  'E', // R19_H
  'E', // R20
  'E', // R20_H
  'E', // R21
  'E', // R21_H
  'E', // R22
  'E', // R22_H
  'E', // R24
  'E', // R24_H
  'E', // R25
  'E', // R25_H
  'E', // R26
  'E', // R26_H
  'E', // R23
  'E', // R23_H
  'E', // R27
  'E', // R27_H
  'N', // R4
  'N', // R4_H
  'E', // R8
  'E', // R8_H
  'N', // R0
  'N', // R0_H
  'C', // R1
  'C', // R1_H
  'E', // R2
  'E', // R2_H
  'N', // R3
  'N', // R3_H
  'C', // F0
  'C', // F0_H
  'C', // F1
  'C', // F1_H
  'C', // F2
  'C', // F2_H
  'C', // F3
  'C', // F3_H
  'C', // F4
  'C', // F4_H
  'C', // F5
  'C', // F5_H
  'C', // F6
  'C', // F6_H
  'C', // F7
  'C', // F7_H
  'C', // F28
  'C', // F28_H
  'C', // F29
  'C', // F29_H
  'C', // F30
  'C', // F30_H
  'C', // F31
  'C', // F31_H
  'C', // F10
  'C', // F10_H
  'C', // F11
  'C', // F11_H
  'C', // F12
  'C', // F12_H
  'C', // F13
  'C', // F13_H
  'C', // F14
  'C', // F14_H
  'C', // F15
  'C', // F15_H
  'C', // F16
  'C', // F16_H
  'C', // F17
  'C', // F17_H
  'E', // F8
  'E', // F8_H
  'E', // F9
  'E', // F9_H
  'E', // F18
  'E', // F18_H
  'E', // F19
  'E', // F19_H
  'E', // F20
  'E', // F20_H
  'E', // F21
  'E', // F21_H
  'E', // F22
  'E', // F22_H
  'E', // F23
  'E', // F23_H
  'E', // F24
  'E', // F24_H
  'E', // F25
  'E', // F25_H
  'E', // F26
  'E', // F26_H
  'E', // F27
  'E', // F27_H
  'C', // V0
  'C', // V0_H
  'C', // V0_J
  'C', // V0_K
  'C', // V1
  'C', // V1_H
  'C', // V1_J
  'C', // V1_K
  'C', // V2
  'C', // V2_H
  'C', // V2_J
  'C', // V2_K
  'C', // V3
  'C', // V3_H
  'C', // V3_J
  'C', // V3_K
  'C', // V4
  'C', // V4_H
  'C', // V4_J
  'C', // V4_K
  'C', // V5
  'C', // V5_H
  'C', // V5_J
  'C', // V5_K
  'C', // V6
  'C', // V6_H
  'C', // V6_J
  'C', // V6_K
  'C', // V7
  'C', // V7_H
  'C', // V7_J
  'C', // V7_K
  'C', // V8
  'C', // V8_H
  'C', // V8_J
  'C', // V8_K
  'C', // V9
  'C', // V9_H
  'C', // V9_J
  'C', // V9_K
  'C', // V10
  'C', // V10_H
  'C', // V10_J
  'C', // V10_K
  'C', // V11
  'C', // V11_H
  'C', // V11_J
  'C', // V11_K
  'C', // V12
  'C', // V12_H
  'C', // V12_J
  'C', // V12_K
  'C', // V13
  'C', // V13_H
  'C', // V13_J
  'C', // V13_K
  'C', // V14
  'C', // V14_H
  'C', // V14_J
  'C', // V14_K
  'C', // V15
  'C', // V15_H
  'C', // V15_J
  'C', // V15_K
  'C', // V16
  'C', // V16_H
  'C', // V16_J
  'C', // V16_K
  'C', // V17
  'C', // V17_H
  'C', // V17_J
  'C', // V17_K
  'C', // V18
  'C', // V18_H
  'C', // V18_J
  'C', // V18_K
  'C', // V19
  'C', // V19_H
  'C', // V19_J
  'C', // V19_K
  'C', // V20
  'C', // V20_H
  'C', // V20_J
  'C', // V20_K
  'C', // V21
  'C', // V21_H
  'C', // V21_J
  'C', // V21_K
  'C', // V22
  'C', // V22_H
  'C', // V22_J
  'C', // V22_K
  'C', // V23
  'C', // V23_H
  'C', // V23_J
  'C', // V23_K
  'C', // V24
  'C', // V24_H
  'C', // V24_J
  'C', // V24_K
  'C', // V25
  'C', // V25_H
  'C', // V25_J
  'C', // V25_K
  'C', // V26
  'C', // V26_H
  'C', // V26_J
  'C', // V26_K
  'C', // V27
  'C', // V27_H
  'C', // V27_J
  'C', // V27_K
  'C', // V28
  'C', // V28_H
  'C', // V28_J
  'C', // V28_K
  'C', // V29
  'C', // V29_H
  'C', // V29_J
  'C', // V29_K
  'C', // V30
  'C', // V30_H
  'C', // V30_J
  'C', // V30_K
  'C', // V31
  'C', // V31_H
  'C', // V31_J
  'C', // V31_K
  'C' // no trailing comma // RFLAGS
};

// Map from machine-independent register number to register_save_type
const        int register_save_type[] = {
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegI,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_RegF,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_VecA,
  Op_RegFlags // no trailing comma
};


const        int   reduceOp[] = {
  /*    0 */  0,
  /*    1 */  0,
  /*    2 */  0,
  /*    3 */  0,
  /*    4 */  0,
  /*    5 */  0,
  /*    6 */  0,
  /*    7 */  0,
  /*    8 */  immI_rule,
  /*    9 */  immI0_rule,
  /*   10 */  immI_1_rule,
  /*   11 */  immI_M1_rule,
  /*   12 */  uimmI6_ge32_rule,
  /*   13 */  immI_le_4_rule,
  /*   14 */  immI_16_rule,
  /*   15 */  immI_24_rule,
  /*   16 */  immI_31_rule,
  /*   17 */  immI_63_rule,
  /*   18 */  immIAdd_rule,
  /*   19 */  immISub_rule,
  /*   20 */  immI5_rule,
  /*   21 */  immL5_rule,
  /*   22 */  immL_rule,
  /*   23 */  immL0_rule,
  /*   24 */  immP_rule,
  /*   25 */  immP0_rule,
  /*   26 */  immP_1_rule,
  /*   27 */  immByteMapBase_rule,
  /*   28 */  immI_16bits_rule,
  /*   29 */  immL_32bits_rule,
  /*   30 */  immL_M1_rule,
  /*   31 */  immL_pc_off_rule,
  /*   32 */  immLAdd_rule,
  /*   33 */  immLSub_rule,
  /*   34 */  immN_rule,
  /*   35 */  immN0_rule,
  /*   36 */  immNKlass_rule,
  /*   37 */  immD_rule,
  /*   38 */  immD0_rule,
  /*   39 */  immF_rule,
  /*   40 */  immF0_rule,
  /*   41 */  immIOffset_rule,
  /*   42 */  immLOffset_rule,
  /*   43 */  immIScale_rule,
  /*   44 */  iRegI_rule,
  /*   45 */  iRegINoSp_rule,
  /*   46 */  iRegI_R10_rule,
  /*   47 */  iRegI_R12_rule,
  /*   48 */  iRegI_R13_rule,
  /*   49 */  iRegI_R14_rule,
  /*   50 */  iRegL_rule,
  /*   51 */  iRegLNoSp_rule,
  /*   52 */  iRegL_R28_rule,
  /*   53 */  iRegL_R29_rule,
  /*   54 */  iRegL_R30_rule,
  /*   55 */  iRegP_rule,
  /*   56 */  iRegPNoSp_rule,
  /*   57 */  iRegP_R10_rule,
  /*   58 */  iRegP_R11_rule,
  /*   59 */  iRegP_R12_rule,
  /*   60 */  iRegP_R13_rule,
  /*   61 */  iRegP_R14_rule,
  /*   62 */  iRegP_R15_rule,
  /*   63 */  iRegP_R16_rule,
  /*   64 */  iRegP_R28_rule,
  /*   65 */  iRegP_R30_rule,
  /*   66 */  iRegP_R31_rule,
  /*   67 */  iRegN_rule,
  /*   68 */  iRegNNoSp_rule,
  /*   69 */  iRegIHeapbase_rule,
  /*   70 */  iRegL_R10_rule,
  /*   71 */  fRegF_rule,
  /*   72 */  fRegD_rule,
  /*   73 */  vReg_rule,
  /*   74 */  vReg_V1_rule,
  /*   75 */  vReg_V2_rule,
  /*   76 */  vReg_V3_rule,
  /*   77 */  vReg_V4_rule,
  /*   78 */  vReg_V5_rule,
  /*   79 */  javaThread_RegP_rule,
  /*   80 */  indirect_rule,
  /*   81 */  indOffI_rule,
  /*   82 */  indOffL_rule,
  /*   83 */  indirectN_rule,
  /*   84 */  indOffIN_rule,
  /*   85 */  indOffLN_rule,
  /*   86 */  thread_anchor_pc_rule,
  /*   87 */  stackSlotI_rule,
  /*   88 */  stackSlotF_rule,
  /*   89 */  stackSlotD_rule,
  /*   90 */  stackSlotL_rule,
  /*   91 */  iRegL2I_rule,
  /*   92 */  cmpOp_rule,
  /*   93 */  cmpOpU_rule,
  /*   94 */  cmpOpEqNe_rule,
  /*   95 */  cmpOpULtGe_rule,
  /*   96 */  cmpOpUEqNeLeGt_rule,
  /*   97 */  rFlagsReg_rule,
  /*   98 */  inline_cache_RegP_rule,
  /*   99 */  pRegGov_rule,
  // last operand
  /*  100 */  memory_rule,
  /*  101 */  iRegIorL2I_rule,
  /*  102 */  iRegIorL_rule,
  /*  103 */  iRegNorP_rule,
  /*  104 */  iRegILNP_rule,
  /*  105 */  iRegILNPNoSp_rule,
  /*  106 */  immIorL_rule,
  /*  107 */  vmemA_rule,
  // last operand class
  /*  108 */  _DecodeN_iRegN__rule,
  /*  109 */  _LoadB_memory__rule,
  /*  110 */  _LoadUB_memory__rule,
  /*  111 */  _LoadS_memory__rule,
  /*  112 */  _LoadUS_memory__rule,
  /*  113 */  _LoadI_memory__rule,
  /*  114 */  _ConvI2L__LoadI_memory___rule,
  /*  115 */  _Binary_iRegI_R12_iRegI_R13_rule,
  /*  116 */  _Binary_iRegI_iRegI_rule,
  /*  117 */  _Binary_iRegL_iRegL_rule,
  /*  118 */  _Binary_iRegP_iRegP_rule,
  /*  119 */  _Binary_iRegN_iRegN_rule,
  /*  120 */  _ConvL2I_iRegL__rule,
  /*  121 */  _ConvI2L_iRegI__rule,
  /*  122 */  _RShiftI_iRegIorL2I_immI_31_rule,
  /*  123 */  _RShiftL_iRegL_immI_63_rule,
  /*  124 */  _CastP2X_iRegP__rule,
  /*  125 */  _Binary_fRegF_fRegF_rule,
  /*  126 */  _Binary_fRegD_fRegD_rule,
  /*  127 */  _NegF_fRegF__rule,
  /*  128 */  _NegD_fRegD__rule,
  /*  129 */  _Binary__NegF_fRegF__fRegF_rule,
  /*  130 */  _Binary_fRegF__NegF_fRegF__rule,
  /*  131 */  _Binary__NegD_fRegD__fRegD_rule,
  /*  132 */  _Binary_fRegD__NegD_fRegD__rule,
  /*  133 */  _ConvF2D_fRegF__rule,
  /*  134 */  _SqrtD__ConvF2D_fRegF___rule,
  /*  135 */  _ConvI2L_iRegIorL2I__rule,
  /*  136 */  _CastP2X__DecodeN_iRegN___rule,
  /*  137 */  _CmpI_iRegI_iRegI_rule,
  /*  138 */  _CmpU_iRegI_iRegI_rule,
  /*  139 */  _CmpL_iRegL_iRegL_rule,
  /*  140 */  _CmpUL_iRegL_iRegL_rule,
  /*  141 */  _CmpP_iRegP_iRegP_rule,
  /*  142 */  _CmpN_iRegN_iRegN_rule,
  /*  143 */  _CmpF_fRegF_fRegF_rule,
  /*  144 */  _CmpD_fRegD_fRegD_rule,
  /*  145 */  _CmpI_iRegI_immI0_rule,
  /*  146 */  _CmpU_iRegI_immI0_rule,
  /*  147 */  _CmpL_iRegL_immL0_rule,
  /*  148 */  _CmpUL_iRegL_immL0_rule,
  /*  149 */  _CmpP_iRegP_immP0_rule,
  /*  150 */  _CmpN_iRegN_immN0_rule,
  /*  151 */  _CmpP__DecodeN_iRegN__immP0_rule,
  /*  152 */  _Binary_cmpOp__CmpI_iRegI_iRegI_rule,
  /*  153 */  _Binary_iRegINoSp_iRegI_rule,
  /*  154 */  _Binary_cmpOpU__CmpU_iRegI_iRegI_rule,
  /*  155 */  _Binary_cmpOp__CmpL_iRegL_iRegL_rule,
  /*  156 */  _Binary_iRegLNoSp_iRegL_rule,
  /*  157 */  _Binary_cmpOpU__CmpUL_iRegL_iRegL_rule,
  /*  158 */  _PartialSubtypeCheck_iRegP_R14_iRegP_R10_rule,
  /*  159 */  _Binary_iRegP_R11_iRegI_R12_rule,
  /*  160 */  _Binary_iRegP_R13_iRegI_R14_rule,
  /*  161 */  _Binary_iRegP_R13_immI_le_4_rule,
  /*  162 */  _Binary_iRegP_R13_immI_1_rule,
  /*  163 */  _Binary_iRegP_R11_iRegP_R13_rule,
  /*  164 */  _Binary_vReg_vReg_rule,
  /*  165 */  _NegVF_vReg__rule,
  /*  166 */  _Binary__NegVF_vReg__vReg_rule,
  /*  167 */  _Binary_vReg__NegVF_vReg__rule,
  /*  168 */  _NegVD_vReg__rule,
  /*  169 */  _Binary__NegVD_vReg__vReg_rule,
  /*  170 */  _Binary_vReg__NegVD_vReg__rule,
  /*  171 */  _MulVB_vReg_vReg_rule,
  /*  172 */  _MulVS_vReg_vReg_rule,
  /*  173 */  _MulVI_vReg_vReg_rule,
  /*  174 */  _MulVL_vReg_vReg_rule,
  /*  175 */  _RShiftCntV_immI__rule,
  /*  176 */  _LShiftCntV_immI__rule,
  /*  177 */  _Binary_iRegP_R11_iRegI_R13_rule,
  /*  178 */  _LShiftI_iRegIorL2I_immI_24_rule,
  /*  179 */  _LShiftI_iRegIorL2I_immI_16_rule,
  /*  180 */  _LShiftL_iRegL_immIScale_rule,
  /*  181 */  _LShiftL__ConvI2L_iRegI__immIScale_rule,
  /*  182 */  _XorI_iRegI_immI_M1_rule,
  /*  183 */  _XorL_iRegL_immL_M1_rule,
  // last internally defined operand
  /*  184 */  iRegINoSp_rule,
  /*  185 */  iRegLNoSp_rule,
  /*  186 */  iRegPNoSp_rule,
  /*  187 */  iRegPNoSp_rule,
  /*  188 */  iRegPNoSp_rule,
  /*  189 */  iRegPNoSp_rule,
  /*  190 */  iRegNNoSp_rule,
  /*  191 */  iRegNNoSp_rule,
  /*  192 */  iRegNNoSp_rule,
  /*  193 */  fRegF_rule,
  /*  194 */  fRegF_rule,
  /*  195 */  fRegD_rule,
  /*  196 */  fRegD_rule,
  /*  197 */  iRegINoSp_rule,
  /*  198 */  iRegINoSp_rule,
  /*  199 */  iRegINoSp_rule,
  /*  200 */  iRegINoSp_rule,
  /*  201 */  fRegF_rule,
  /*  202 */  fRegD_rule,
  /*  203 */  iRegINoSp_rule,
  /*  204 */  iRegLNoSp_rule,
  /*  205 */  fRegF_rule,
  /*  206 */  fRegD_rule,
  /*  207 */  iRegPNoSp_rule,
  /*  208 */  iRegLNoSp_rule,
  /*  209 */  iRegPNoSp_rule,
  /*  210 */  iRegL_rule,
  /*  211 */  iRegI_rule,
  /*  212 */  iRegPNoSp_rule,
  /*  213 */  fRegF_rule,
  /*  214 */  fRegD_rule,
  /*  215 */  vReg_rule,
  /*  216 */  iRegINoSp_rule,
  /*  217 */  iRegINoSp_rule,
  /*  218 */  iRegINoSp_rule,
  /*  219 */  fRegF_rule,
  /*  220 */  iRegLNoSp_rule,
  /*  221 */  fRegD_rule,
  /*  222 */  iRegINoSp_rule,
  /*  223 */  fRegF_rule,
  /*  224 */  iRegLNoSp_rule,
  /*  225 */  fRegD_rule,
  /*  226 */  rFlagsReg_rule,
  /*  227 */  javaThread_RegP_rule,
  /*  228 */  rFlagsReg_rule,
  /*  229 */  rFlagsReg_rule,
  /*  230 */  vReg_rule,
  /*  231 */  vReg_rule,
  /*  232 */  vReg_rule,
  /*  233 */  vReg_rule,
  /*  234 */  vReg_rule,
  /*  235 */  vReg_rule,
  /*  236 */  vReg_rule,
  /*  237 */  vReg_rule,
  /*  238 */  vReg_rule,
  /*  239 */  vReg_rule,
  /*  240 */  vReg_rule,
  /*  241 */  vReg_rule,
  /*  242 */  vReg_rule,
  /*  243 */  vReg_rule,
  /*  244 */  vReg_rule,
  /*  245 */  vReg_rule,
  /*  246 */  vReg_rule,
  /*  247 */  vReg_rule,
  /*  248 */  vReg_rule,
  /*  249 */  vReg_rule,
  /*  250 */  vReg_rule,
  /*  251 */  vReg_rule,
  /*  252 */  vReg_rule,
  /*  253 */  vReg_rule,
  /*  254 */  vReg_rule,
  /*  255 */  vReg_rule,
  /*  256 */  iRegINoSp_rule,
  /*  257 */  iRegINoSp_rule,
  /*  258 */  iRegINoSp_rule,
  /*  259 */  iRegINoSp_rule,
  /*  260 */  iRegINoSp_rule,
  /*  261 */  iRegINoSp_rule,
  /*  262 */  iRegINoSp_rule,
  /*  263 */  iRegLNoSp_rule,
  /*  264 */  iRegINoSp_rule,
  /*  265 */  iRegLNoSp_rule,
  /*  266 */  iRegINoSp_rule,
  /*  267 */  iRegLNoSp_rule,
  /*  268 */  iRegINoSp_rule,
  /*  269 */  iRegLNoSp_rule,
  /*  270 */  iRegINoSp_rule,
  /*  271 */  iRegLNoSp_rule,
  /*  272 */  iRegINoSp_rule,
  /*  273 */  iRegLNoSp_rule,
  /*  274 */  iRegLNoSp_rule,
  /*  275 */  iRegLNoSp_rule,
  /*  276 */  iRegINoSp_rule,
  /*  277 */  iRegPNoSp_rule,
  /*  278 */  iRegNNoSp_rule,
  /*  279 */  iRegPNoSp_rule,
  /*  280 */  iRegNNoSp_rule,
  /*  281 */  fRegF_rule,
  /*  282 */  fRegD_rule,
  /*  283 */  Universe_rule,
  /*  284 */  Universe_rule,
  /*  285 */  Universe_rule,
  /*  286 */  Universe_rule,
  /*  287 */  Universe_rule,
  /*  288 */  Universe_rule,
  /*  289 */  Universe_rule,
  /*  290 */  Universe_rule,
  /*  291 */  Universe_rule,
  /*  292 */  Universe_rule,
  /*  293 */  Universe_rule,
  /*  294 */  Universe_rule,
  /*  295 */  Universe_rule,
  /*  296 */  Universe_rule,
  /*  297 */  Universe_rule,
  /*  298 */  Universe_rule,
  /*  299 */  Universe_rule,
  /*  300 */  iRegINoSp_rule,
  /*  301 */  iRegINoSp_rule,
  /*  302 */  iRegINoSp_rule,
  /*  303 */  iRegINoSp_rule,
  /*  304 */  iRegINoSp_rule,
  /*  305 */  iRegINoSp_rule,
  /*  306 */  iRegINoSp_rule,
  /*  307 */  iRegINoSp_rule,
  /*  308 */  iRegINoSp_rule,
  /*  309 */  iRegINoSp_rule,
  /*  310 */  iRegINoSp_rule,
  /*  311 */  iRegINoSp_rule,
  /*  312 */  iRegINoSp_rule,
  /*  313 */  iRegINoSp_rule,
  /*  314 */  iRegINoSp_rule,
  /*  315 */  iRegLNoSp_rule,
  /*  316 */  iRegNNoSp_rule,
  /*  317 */  iRegPNoSp_rule,
  /*  318 */  iRegINoSp_rule,
  /*  319 */  iRegINoSp_rule,
  /*  320 */  iRegINoSp_rule,
  /*  321 */  iRegLNoSp_rule,
  /*  322 */  iRegNNoSp_rule,
  /*  323 */  iRegPNoSp_rule,
  /*  324 */  iRegINoSp_rule,
  /*  325 */  iRegINoSp_rule,
  /*  326 */  iRegINoSp_rule,
  /*  327 */  iRegINoSp_rule,
  /*  328 */  iRegINoSp_rule,
  /*  329 */  iRegINoSp_rule,
  /*  330 */  iRegINoSp_rule,
  /*  331 */  iRegINoSp_rule,
  /*  332 */  iRegINoSp_rule,
  /*  333 */  iRegINoSp_rule,
  /*  334 */  iRegINoSp_rule,
  /*  335 */  iRegINoSp_rule,
  /*  336 */  iRegINoSp_rule,
  /*  337 */  iRegLNoSp_rule,
  /*  338 */  iRegINoSp_rule,
  /*  339 */  iRegPNoSp_rule,
  /*  340 */  iRegINoSp_rule,
  /*  341 */  iRegLNoSp_rule,
  /*  342 */  iRegINoSp_rule,
  /*  343 */  iRegPNoSp_rule,
  /*  344 */  iRegLNoSp_rule,
  /*  345 */  Universe_rule,
  /*  346 */  iRegLNoSp_rule,
  /*  347 */  Universe_rule,
  /*  348 */  iRegINoSp_rule,
  /*  349 */  Universe_rule,
  /*  350 */  iRegINoSp_rule,
  /*  351 */  Universe_rule,
  /*  352 */  iRegLNoSp_rule,
  /*  353 */  Universe_rule,
  /*  354 */  iRegLNoSp_rule,
  /*  355 */  Universe_rule,
  /*  356 */  iRegINoSp_rule,
  /*  357 */  Universe_rule,
  /*  358 */  iRegINoSp_rule,
  /*  359 */  Universe_rule,
  /*  360 */  iRegINoSp_rule,
  /*  361 */  iRegINoSp_rule,
  /*  362 */  iRegINoSp_rule,
  /*  363 */  iRegPNoSp_rule,
  /*  364 */  iRegLNoSp_rule,
  /*  365 */  iRegPNoSp_rule,
  /*  366 */  iRegLNoSp_rule,
  /*  367 */  iRegLNoSp_rule,
  /*  368 */  iRegINoSp_rule,
  /*  369 */  iRegINoSp_rule,
  /*  370 */  iRegLNoSp_rule,
  /*  371 */  iRegLNoSp_rule,
  /*  372 */  iRegINoSp_rule,
  /*  373 */  iRegLNoSp_rule,
  /*  374 */  iRegINoSp_rule,
  /*  375 */  iRegLNoSp_rule,
  /*  376 */  iRegLNoSp_rule,
  /*  377 */  iRegINoSp_rule,
  /*  378 */  iRegINoSp_rule,
  /*  379 */  iRegLNoSp_rule,
  /*  380 */  iRegLNoSp_rule,
  /*  381 */  iRegINoSp_rule,
  /*  382 */  iRegLNoSp_rule,
  /*  383 */  iRegINoSp_rule,
  /*  384 */  iRegINoSp_rule,
  /*  385 */  iRegINoSp_rule,
  /*  386 */  iRegINoSp_rule,
  /*  387 */  iRegINoSp_rule,
  /*  388 */  iRegINoSp_rule,
  /*  389 */  iRegLNoSp_rule,
  /*  390 */  iRegLNoSp_rule,
  /*  391 */  iRegLNoSp_rule,
  /*  392 */  iRegLNoSp_rule,
  /*  393 */  iRegLNoSp_rule,
  /*  394 */  iRegLNoSp_rule,
  /*  395 */  iRegLNoSp_rule,
  /*  396 */  iRegINoSp_rule,
  /*  397 */  iRegLNoSp_rule,
  /*  398 */  fRegF_rule,
  /*  399 */  fRegD_rule,
  /*  400 */  fRegF_rule,
  /*  401 */  fRegD_rule,
  /*  402 */  fRegF_rule,
  /*  403 */  fRegD_rule,
  /*  404 */  fRegF_rule,
  /*  405 */  fRegD_rule,
  /*  406 */  fRegF_rule,
  /*  407 */  fRegD_rule,
  /*  408 */  fRegF_rule,
  /*  409 */  fRegF_rule,
  /*  410 */  fRegD_rule,
  /*  411 */  fRegD_rule,
  /*  412 */  fRegF_rule,
  /*  413 */  fRegF_rule,
  /*  414 */  fRegD_rule,
  /*  415 */  fRegD_rule,
  /*  416 */  fRegF_rule,
  /*  417 */  fRegF_rule,
  /*  418 */  fRegD_rule,
  /*  419 */  fRegD_rule,
  /*  420 */  fRegF_rule,
  /*  421 */  fRegD_rule,
  /*  422 */  fRegF_rule,
  /*  423 */  fRegD_rule,
  /*  424 */  iRegINoSp_rule,
  /*  425 */  iRegINoSp_rule,
  /*  426 */  iRegINoSp_rule,
  /*  427 */  iRegINoSp_rule,
  /*  428 */  iRegINoSp_rule,
  /*  429 */  iRegINoSp_rule,
  /*  430 */  iRegLNoSp_rule,
  /*  431 */  iRegLNoSp_rule,
  /*  432 */  iRegLNoSp_rule,
  /*  433 */  iRegLNoSp_rule,
  /*  434 */  iRegLNoSp_rule,
  /*  435 */  iRegLNoSp_rule,
  /*  436 */  iRegINoSp_rule,
  /*  437 */  iRegLNoSp_rule,
  /*  438 */  iRegINoSp_rule,
  /*  439 */  iRegINoSp_rule,
  /*  440 */  Universe_rule,
  /*  441 */  Universe_rule,
  /*  442 */  Universe_rule,
  /*  443 */  Universe_rule,
  /*  444 */  Universe_rule,
  /*  445 */  Universe_rule,
  /*  446 */  Universe_rule,
  /*  447 */  Universe_rule,
  /*  448 */  Universe_rule,
  /*  449 */  iRegLNoSp_rule,
  /*  450 */  iRegINoSp_rule,
  /*  451 */  iRegLNoSp_rule,
  /*  452 */  fRegD_rule,
  /*  453 */  fRegF_rule,
  /*  454 */  iRegINoSp_rule,
  /*  455 */  fRegF_rule,
  /*  456 */  iRegLNoSp_rule,
  /*  457 */  fRegF_rule,
  /*  458 */  iRegINoSp_rule,
  /*  459 */  fRegD_rule,
  /*  460 */  iRegLNoSp_rule,
  /*  461 */  fRegD_rule,
  /*  462 */  iRegINoSp_rule,
  /*  463 */  iRegINoSp_rule,
  /*  464 */  iRegNNoSp_rule,
  /*  465 */  iRegPNoSp_rule,
  /*  466 */  iRegPNoSp_rule,
  /*  467 */  iRegNNoSp_rule,
  /*  468 */  iRegPNoSp_rule,
  /*  469 */  stackSlotI_rule,
  /*  470 */  stackSlotF_rule,
  /*  471 */  stackSlotL_rule,
  /*  472 */  stackSlotD_rule,
  /*  473 */  iRegINoSp_rule,
  /*  474 */  iRegINoSp_rule,
  /*  475 */  iRegINoSp_rule,
  /*  476 */  iRegINoSp_rule,
  /*  477 */  iRegINoSp_rule,
  /*  478 */  iRegINoSp_rule,
  /*  479 */  iRegINoSp_rule,
  /*  480 */  Universe_rule,
  /*  481 */  Universe_rule,
  /*  482 */  Universe_rule,
  /*  483 */  Universe_rule,
  /*  484 */  Universe_rule,
  /*  485 */  Universe_rule,
  /*  486 */  Universe_rule,
  /*  487 */  Universe_rule,
  /*  488 */  Universe_rule,
  /*  489 */  Universe_rule,
  /*  490 */  Universe_rule,
  /*  491 */  Universe_rule,
  /*  492 */  Universe_rule,
  /*  493 */  Universe_rule,
  /*  494 */  Universe_rule,
  /*  495 */  Universe_rule,
  /*  496 */  Universe_rule,
  /*  497 */  Universe_rule,
  /*  498 */  Universe_rule,
  /*  499 */  Universe_rule,
  /*  500 */  Universe_rule,
  /*  501 */  Universe_rule,
  /*  502 */  Universe_rule,
  /*  503 */  Universe_rule,
  /*  504 */  Universe_rule,
  /*  505 */  Universe_rule,
  /*  506 */  Universe_rule,
  /*  507 */  Universe_rule,
  /*  508 */  Universe_rule,
  /*  509 */  Universe_rule,
  /*  510 */  Universe_rule,
  /*  511 */  Universe_rule,
  /*  512 */  Universe_rule,
  /*  513 */  Universe_rule,
  /*  514 */  Universe_rule,
  /*  515 */  Universe_rule,
  /*  516 */  Universe_rule,
  /*  517 */  Universe_rule,
  /*  518 */  Universe_rule,
  /*  519 */  Universe_rule,
  /*  520 */  Universe_rule,
  /*  521 */  Universe_rule,
  /*  522 */  Universe_rule,
  /*  523 */  Universe_rule,
  /*  524 */  Universe_rule,
  /*  525 */  Universe_rule,
  /*  526 */  Universe_rule,
  /*  527 */  Universe_rule,
  /*  528 */  Universe_rule,
  /*  529 */  Universe_rule,
  /*  530 */  Universe_rule,
  /*  531 */  Universe_rule,
  /*  532 */  Universe_rule,
  /*  533 */  Universe_rule,
  /*  534 */  Universe_rule,
  /*  535 */  Universe_rule,
  /*  536 */  Universe_rule,
  /*  537 */  Universe_rule,
  /*  538 */  Universe_rule,
  /*  539 */  Universe_rule,
  /*  540 */  Universe_rule,
  /*  541 */  Universe_rule,
  /*  542 */  Universe_rule,
  /*  543 */  Universe_rule,
  /*  544 */  Universe_rule,
  /*  545 */  Universe_rule,
  /*  546 */  Universe_rule,
  /*  547 */  iRegINoSp_rule,
  /*  548 */  iRegINoSp_rule,
  /*  549 */  iRegINoSp_rule,
  /*  550 */  iRegLNoSp_rule,
  /*  551 */  iRegLNoSp_rule,
  /*  552 */  iRegINoSp_rule,
  /*  553 */  Universe_rule,
  /*  554 */  Universe_rule,
  /*  555 */  Universe_rule,
  /*  556 */  Universe_rule,
  /*  557 */  Universe_rule,
  /*  558 */  iRegP_R15_rule,
  /*  559 */  iRegI_R10_rule,
  /*  560 */  iRegI_R10_rule,
  /*  561 */  iRegI_R10_rule,
  /*  562 */  iRegI_R10_rule,
  /*  563 */  iRegI_R10_rule,
  /*  564 */  iRegI_R10_rule,
  /*  565 */  iRegI_R10_rule,
  /*  566 */  iRegI_R10_rule,
  /*  567 */  iRegI_R10_rule,
  /*  568 */  iRegI_R10_rule,
  /*  569 */  iRegI_R10_rule,
  /*  570 */  iRegI_R10_rule,
  /*  571 */  Universe_rule,
  /*  572 */  Universe_rule,
  /*  573 */  iRegI_R10_rule,
  /*  574 */  iRegI_R10_rule,
  /*  575 */  iRegI_R10_rule,
  /*  576 */  iRegI_R10_rule,
  /*  577 */  Universe_rule,
  /*  578 */  Universe_rule,
  /*  579 */  Universe_rule,
  /*  580 */  iRegP_R10_rule,
  /*  581 */  Universe_rule,
  /*  582 */  Universe_rule,
  /*  583 */  Universe_rule,
  /*  584 */  vReg_rule,
  /*  585 */  Universe_rule,
  /*  586 */  vReg_rule,
  /*  587 */  vReg_rule,
  /*  588 */  vReg_rule,
  /*  589 */  vReg_rule,
  /*  590 */  vReg_rule,
  /*  591 */  vReg_rule,
  /*  592 */  vReg_rule,
  /*  593 */  vReg_rule,
  /*  594 */  vReg_rule,
  /*  595 */  vReg_rule,
  /*  596 */  vReg_rule,
  /*  597 */  vReg_rule,
  /*  598 */  vReg_rule,
  /*  599 */  vReg_rule,
  /*  600 */  vReg_rule,
  /*  601 */  vReg_rule,
  /*  602 */  vReg_rule,
  /*  603 */  vReg_rule,
  /*  604 */  vReg_rule,
  /*  605 */  vReg_rule,
  /*  606 */  vReg_rule,
  /*  607 */  vReg_rule,
  /*  608 */  vReg_rule,
  /*  609 */  vReg_rule,
  /*  610 */  vReg_rule,
  /*  611 */  vReg_rule,
  /*  612 */  vReg_rule,
  /*  613 */  vReg_rule,
  /*  614 */  vReg_rule,
  /*  615 */  vReg_rule,
  /*  616 */  vReg_rule,
  /*  617 */  vReg_rule,
  /*  618 */  vReg_rule,
  /*  619 */  vReg_rule,
  /*  620 */  vReg_rule,
  /*  621 */  vReg_rule,
  /*  622 */  vReg_rule,
  /*  623 */  vReg_rule,
  /*  624 */  vReg_rule,
  /*  625 */  vReg_rule,
  /*  626 */  vReg_rule,
  /*  627 */  vReg_rule,
  /*  628 */  vReg_rule,
  /*  629 */  vReg_rule,
  /*  630 */  vReg_rule,
  /*  631 */  vReg_rule,
  /*  632 */  vReg_rule,
  /*  633 */  vReg_rule,
  /*  634 */  vReg_rule,
  /*  635 */  vReg_rule,
  /*  636 */  vReg_rule,
  /*  637 */  vReg_rule,
  /*  638 */  iRegINoSp_rule,
  /*  639 */  iRegLNoSp_rule,
  /*  640 */  iRegINoSp_rule,
  /*  641 */  iRegLNoSp_rule,
  /*  642 */  iRegINoSp_rule,
  /*  643 */  iRegLNoSp_rule,
  /*  644 */  iRegINoSp_rule,
  /*  645 */  iRegLNoSp_rule,
  /*  646 */  fRegF_rule,
  /*  647 */  fRegD_rule,
  /*  648 */  iRegINoSp_rule,
  /*  649 */  iRegLNoSp_rule,
  /*  650 */  iRegINoSp_rule,
  /*  651 */  iRegLNoSp_rule,
  /*  652 */  fRegF_rule,
  /*  653 */  fRegD_rule,
  /*  654 */  fRegF_rule,
  /*  655 */  fRegD_rule,
  /*  656 */  vReg_rule,
  /*  657 */  vReg_rule,
  /*  658 */  vReg_rule,
  /*  659 */  vReg_rule,
  /*  660 */  vReg_rule,
  /*  661 */  vReg_rule,
  /*  662 */  vReg_rule,
  /*  663 */  vReg_rule,
  /*  664 */  vReg_rule,
  /*  665 */  vReg_rule,
  /*  666 */  vReg_rule,
  /*  667 */  vReg_rule,
  /*  668 */  vReg_rule,
  /*  669 */  vReg_rule,
  /*  670 */  vReg_rule,
  /*  671 */  vReg_rule,
  /*  672 */  vReg_rule,
  /*  673 */  vReg_rule,
  /*  674 */  vReg_rule,
  /*  675 */  vReg_rule,
  /*  676 */  vReg_rule,
  /*  677 */  vReg_rule,
  /*  678 */  vReg_rule,
  /*  679 */  vReg_rule,
  /*  680 */  vReg_rule,
  /*  681 */  vReg_rule,
  /*  682 */  vReg_rule,
  /*  683 */  vReg_rule,
  /*  684 */  vReg_rule,
  /*  685 */  vReg_rule,
  /*  686 */  vReg_rule,
  /*  687 */  iRegI_R10_rule,
  /*  688 */  iRegI_R10_rule,
  /*  689 */  iRegI_R10_rule,
  /*  690 */  iRegI_R10_rule,
  /*  691 */  iRegI_R10_rule,
  /*  692 */  iRegI_R10_rule,
  /*  693 */  iRegI_R10_rule,
  /*  694 */  iRegI_R10_rule,
  /*  695 */  Universe_rule,
  /*  696 */  iRegI_R10_rule,
  /*  697 */  iRegI_R10_rule,
  /*  698 */  iRegI_R10_rule,
  /*  699 */  iRegI_R10_rule,
  /*  700 */  iRegI_R10_rule,
  /*  701 */  Universe_rule,
  /*  702 */  iRegINoSp_rule,
  /*  703 */  iRegLNoSp_rule,
  /*  704 */  iRegINoSp_rule,
  /*  705 */  iRegLNoSp_rule,
  /*  706 */  iRegINoSp_rule,
  /*  707 */  iRegLNoSp_rule,
  /*  708 */  iRegINoSp_rule,
  /*  709 */  iRegINoSp_rule,
  /*  710 */  iRegINoSp_rule,
  /*  711 */  iRegINoSp_rule,
  /*  712 */  iRegLNoSp_rule,
  /*  713 */  iRegINoSp_rule,
  /*  714 */  iRegLNoSp_rule,
  /*  715 */  iRegINoSp_rule,
  /*  716 */  iRegINoSp_rule,
  /*  717 */  iRegPNoSp_rule,
  /*  718 */  iRegPNoSp_rule,
  /*  719 */  iRegLNoSp_rule,
  /*  720 */  iRegLNoSp_rule,
  /*  721 */  iRegLNoSp_rule,
  /*  722 */  iRegLNoSp_rule,
  /*  723 */  iRegINoSp_rule,
  /*  724 */  iRegINoSp_rule,
  /*  725 */  iRegINoSp_rule,
  /*  726 */  iRegINoSp_rule,
  /*  727 */  iRegLNoSp_rule,
  /*  728 */  iRegLNoSp_rule,
  /*  729 */  iRegINoSp_rule,
  /*  730 */  iRegINoSp_rule,
  /*  731 */  iRegLNoSp_rule,
  /*  732 */  iRegLNoSp_rule,
  /*  733 */  iRegINoSp_rule,
  /*  734 */  iRegINoSp_rule,
  /*  735 */  iRegINoSp_rule,
  /*  736 */  iRegINoSp_rule,
  /*  737 */  iRegNNoSp_rule,
  /*  738 */  iRegPNoSp_rule,
  /*  739 */  iRegINoSp_rule,
  /*  740 */  iRegNNoSp_rule,
  /*  741 */  iRegPNoSp_rule,
  /*  742 */  iRegINoSp_rule,
  /*  743 */  iRegINoSp_rule,
  /*  744 */  iRegINoSp_rule,
  /*  745 */  iRegPNoSp_rule,
  /*  746 */  iRegINoSp_rule,
  /*  747 */  iRegINoSp_rule,
  /*  748 */  iRegINoSp_rule,
  /*  749 */  iRegINoSp_rule,
  /*  750 */  iRegPNoSp_rule,
  /*  751 */  iRegPNoSp_rule,
  /*  752 */  iRegPNoSp_rule,
  /*  753 */  iRegPNoSp_rule,
  // last instruction
  0 // no trailing comma
};

const        int   leftOp[] = {
  /*    0 */  0,
  /*    1 */  0,
  /*    2 */  0,
  /*    3 */  0,
  /*    4 */  0,
  /*    5 */  0,
  /*    6 */  0,
  /*    7 */  0,
  /*    8 */  0,
  /*    9 */  0,
  /*   10 */  0,
  /*   11 */  0,
  /*   12 */  0,
  /*   13 */  0,
  /*   14 */  0,
  /*   15 */  0,
  /*   16 */  0,
  /*   17 */  0,
  /*   18 */  0,
  /*   19 */  0,
  /*   20 */  0,
  /*   21 */  0,
  /*   22 */  0,
  /*   23 */  0,
  /*   24 */  0,
  /*   25 */  0,
  /*   26 */  0,
  /*   27 */  0,
  /*   28 */  0,
  /*   29 */  0,
  /*   30 */  0,
  /*   31 */  0,
  /*   32 */  0,
  /*   33 */  0,
  /*   34 */  0,
  /*   35 */  0,
  /*   36 */  0,
  /*   37 */  0,
  /*   38 */  0,
  /*   39 */  0,
  /*   40 */  0,
  /*   41 */  0,
  /*   42 */  0,
  /*   43 */  0,
  /*   44 */  0,
  /*   45 */  0,
  /*   46 */  0,
  /*   47 */  0,
  /*   48 */  0,
  /*   49 */  0,
  /*   50 */  0,
  /*   51 */  0,
  /*   52 */  0,
  /*   53 */  0,
  /*   54 */  0,
  /*   55 */  0,
  /*   56 */  0,
  /*   57 */  0,
  /*   58 */  0,
  /*   59 */  0,
  /*   60 */  0,
  /*   61 */  0,
  /*   62 */  0,
  /*   63 */  0,
  /*   64 */  0,
  /*   65 */  0,
  /*   66 */  0,
  /*   67 */  0,
  /*   68 */  0,
  /*   69 */  0,
  /*   70 */  0,
  /*   71 */  0,
  /*   72 */  0,
  /*   73 */  0,
  /*   74 */  0,
  /*   75 */  0,
  /*   76 */  0,
  /*   77 */  0,
  /*   78 */  0,
  /*   79 */  0,
  /*   80 */  0,
  /*   81 */  iRegP_rule,
  /*   82 */  iRegP_rule,
  /*   83 */  iRegN_rule,
  /*   84 */  _DecodeN_iRegN__rule,
  /*   85 */  _DecodeN_iRegN__rule,
  /*   86 */  javaThread_RegP_rule,
  /*   87 */  0,
  /*   88 */  0,
  /*   89 */  0,
  /*   90 */  0,
  /*   91 */  iRegL_rule,
  /*   92 */  0,
  /*   93 */  0,
  /*   94 */  0,
  /*   95 */  0,
  /*   96 */  0,
  /*   97 */  0,
  /*   98 */  0,
  /*   99 */  0,
  // last operand
  /*  100 */  0,
  /*  101 */  0,
  /*  102 */  0,
  /*  103 */  0,
  /*  104 */  0,
  /*  105 */  0,
  /*  106 */  0,
  /*  107 */  0,
  // last operand class
  /*  108 */  iRegN_rule,
  /*  109 */  memory_rule,
  /*  110 */  memory_rule,
  /*  111 */  memory_rule,
  /*  112 */  memory_rule,
  /*  113 */  memory_rule,
  /*  114 */  _LoadI_memory__rule,
  /*  115 */  iRegI_R12_rule,
  /*  116 */  iRegI_rule,
  /*  117 */  iRegL_rule,
  /*  118 */  iRegP_rule,
  /*  119 */  iRegN_rule,
  /*  120 */  iRegL_rule,
  /*  121 */  iRegI_rule,
  /*  122 */  iRegIorL2I_rule,
  /*  123 */  iRegL_rule,
  /*  124 */  iRegP_rule,
  /*  125 */  fRegF_rule,
  /*  126 */  fRegD_rule,
  /*  127 */  fRegF_rule,
  /*  128 */  fRegD_rule,
  /*  129 */  _NegF_fRegF__rule,
  /*  130 */  fRegF_rule,
  /*  131 */  _NegD_fRegD__rule,
  /*  132 */  fRegD_rule,
  /*  133 */  fRegF_rule,
  /*  134 */  _ConvF2D_fRegF__rule,
  /*  135 */  iRegIorL2I_rule,
  /*  136 */  _DecodeN_iRegN__rule,
  /*  137 */  iRegI_rule,
  /*  138 */  iRegI_rule,
  /*  139 */  iRegL_rule,
  /*  140 */  iRegL_rule,
  /*  141 */  iRegP_rule,
  /*  142 */  iRegN_rule,
  /*  143 */  fRegF_rule,
  /*  144 */  fRegD_rule,
  /*  145 */  iRegI_rule,
  /*  146 */  iRegI_rule,
  /*  147 */  iRegL_rule,
  /*  148 */  iRegL_rule,
  /*  149 */  iRegP_rule,
  /*  150 */  iRegN_rule,
  /*  151 */  _DecodeN_iRegN__rule,
  /*  152 */  cmpOp_rule,
  /*  153 */  iRegINoSp_rule,
  /*  154 */  cmpOpU_rule,
  /*  155 */  cmpOp_rule,
  /*  156 */  iRegLNoSp_rule,
  /*  157 */  cmpOpU_rule,
  /*  158 */  iRegP_R14_rule,
  /*  159 */  iRegP_R11_rule,
  /*  160 */  iRegP_R13_rule,
  /*  161 */  iRegP_R13_rule,
  /*  162 */  iRegP_R13_rule,
  /*  163 */  iRegP_R11_rule,
  /*  164 */  vReg_rule,
  /*  165 */  vReg_rule,
  /*  166 */  _NegVF_vReg__rule,
  /*  167 */  vReg_rule,
  /*  168 */  vReg_rule,
  /*  169 */  _NegVD_vReg__rule,
  /*  170 */  vReg_rule,
  /*  171 */  vReg_rule,
  /*  172 */  vReg_rule,
  /*  173 */  vReg_rule,
  /*  174 */  vReg_rule,
  /*  175 */  immI_rule,
  /*  176 */  immI_rule,
  /*  177 */  iRegP_R11_rule,
  /*  178 */  iRegIorL2I_rule,
  /*  179 */  iRegIorL2I_rule,
  /*  180 */  iRegL_rule,
  /*  181 */  _ConvI2L_iRegI__rule,
  /*  182 */  iRegI_rule,
  /*  183 */  iRegL_rule,
  // last internally defined operand
  /*  184 */  immI_rule,
  /*  185 */  immL_rule,
  /*  186 */  immP_rule,
  /*  187 */  immP0_rule,
  /*  188 */  immP_1_rule,
  /*  189 */  immByteMapBase_rule,
  /*  190 */  immN_rule,
  /*  191 */  immN0_rule,
  /*  192 */  immNKlass_rule,
  /*  193 */  immF_rule,
  /*  194 */  immF0_rule,
  /*  195 */  immD_rule,
  /*  196 */  immD0_rule,
  /*  197 */  fRegF_rule,
  /*  198 */  fRegD_rule,
  /*  199 */  fRegF_rule,
  /*  200 */  fRegD_rule,
  /*  201 */  fRegF_rule,
  /*  202 */  fRegD_rule,
  /*  203 */  iRegIorL2I_rule,
  /*  204 */  iRegL_rule,
  /*  205 */  fRegF_rule,
  /*  206 */  fRegD_rule,
  /*  207 */  iRegL_rule,
  /*  208 */  iRegP_rule,
  /*  209 */  iRegPNoSp_rule,
  /*  210 */  iRegL_rule,
  /*  211 */  iRegI_rule,
  /*  212 */  iRegPNoSp_rule,
  /*  213 */  fRegF_rule,
  /*  214 */  fRegD_rule,
  /*  215 */  vReg_rule,
  /*  216 */  iRegI_rule,
  /*  217 */  iRegP_rule,
  /*  218 */  stackSlotF_rule,
  /*  219 */  stackSlotI_rule,
  /*  220 */  stackSlotD_rule,
  /*  221 */  stackSlotL_rule,
  /*  222 */  fRegF_rule,
  /*  223 */  iRegI_rule,
  /*  224 */  fRegD_rule,
  /*  225 */  iRegL_rule,
  /*  226 */  _PartialSubtypeCheck_iRegP_R14_iRegP_R10_rule,
  /*  227 */  0,
  /*  228 */  iRegP_rule,
  /*  229 */  iRegP_rule,
  /*  230 */  vReg_rule,
  /*  231 */  vReg_rule,
  /*  232 */  vReg_rule,
  /*  233 */  vReg_rule,
  /*  234 */  vReg_rule,
  /*  235 */  vReg_rule,
  /*  236 */  iRegIorL2I_rule,
  /*  237 */  iRegIorL2I_rule,
  /*  238 */  iRegIorL2I_rule,
  /*  239 */  iRegL_rule,
  /*  240 */  immI5_rule,
  /*  241 */  immI5_rule,
  /*  242 */  immI5_rule,
  /*  243 */  immL5_rule,
  /*  244 */  fRegF_rule,
  /*  245 */  fRegD_rule,
  /*  246 */  iRegIorL2I_rule,
  /*  247 */  iRegIorL2I_rule,
  /*  248 */  iRegIorL2I_rule,
  /*  249 */  iRegIorL2I_rule,
  /*  250 */  iRegIorL2I_rule,
  /*  251 */  iRegIorL2I_rule,
  /*  252 */  iRegIorL2I_rule,
  /*  253 */  iRegIorL2I_rule,
  /*  254 */  vReg_rule,
  /*  255 */  vReg_rule,
  /*  256 */  iRegIorL2I_rule,
  /*  257 */  iRegL_rule,
  /*  258 */  iRegIorL2I_rule,
  /*  259 */  iRegL_rule,
  /*  260 */  iRegIorL2I_rule,
  /*  261 */  iRegL_rule,
  /*  262 */  iRegI_rule,
  /*  263 */  iRegL_rule,
  /*  264 */  memory_rule,
  /*  265 */  _LoadB_memory__rule,
  /*  266 */  memory_rule,
  /*  267 */  _LoadUB_memory__rule,
  /*  268 */  memory_rule,
  /*  269 */  _LoadS_memory__rule,
  /*  270 */  memory_rule,
  /*  271 */  _LoadUS_memory__rule,
  /*  272 */  memory_rule,
  /*  273 */  _LoadI_memory__rule,
  /*  274 */  _ConvI2L__LoadI_memory___rule,
  /*  275 */  memory_rule,
  /*  276 */  memory_rule,
  /*  277 */  memory_rule,
  /*  278 */  memory_rule,
  /*  279 */  memory_rule,
  /*  280 */  memory_rule,
  /*  281 */  memory_rule,
  /*  282 */  memory_rule,
  /*  283 */  memory_rule,
  /*  284 */  memory_rule,
  /*  285 */  memory_rule,
  /*  286 */  memory_rule,
  /*  287 */  memory_rule,
  /*  288 */  memory_rule,
  /*  289 */  memory_rule,
  /*  290 */  memory_rule,
  /*  291 */  memory_rule,
  /*  292 */  memory_rule,
  /*  293 */  memory_rule,
  /*  294 */  memory_rule,
  /*  295 */  memory_rule,
  /*  296 */  memory_rule,
  /*  297 */  memory_rule,
  /*  298 */  memory_rule,
  /*  299 */  memory_rule,
  /*  300 */  indirect_rule,
  /*  301 */  indirect_rule,
  /*  302 */  indirect_rule,
  /*  303 */  indirect_rule,
  /*  304 */  indirect_rule,
  /*  305 */  indirect_rule,
  /*  306 */  indirect_rule,
  /*  307 */  indirect_rule,
  /*  308 */  indirect_rule,
  /*  309 */  indirect_rule,
  /*  310 */  indirect_rule,
  /*  311 */  indirect_rule,
  /*  312 */  indirect_rule,
  /*  313 */  indirect_rule,
  /*  314 */  indirect_rule,
  /*  315 */  indirect_rule,
  /*  316 */  indirect_rule,
  /*  317 */  indirect_rule,
  /*  318 */  indirect_rule,
  /*  319 */  indirect_rule,
  /*  320 */  indirect_rule,
  /*  321 */  indirect_rule,
  /*  322 */  indirect_rule,
  /*  323 */  indirect_rule,
  /*  324 */  indirect_rule,
  /*  325 */  indirect_rule,
  /*  326 */  indirect_rule,
  /*  327 */  indirect_rule,
  /*  328 */  indirect_rule,
  /*  329 */  indirect_rule,
  /*  330 */  indirect_rule,
  /*  331 */  indirect_rule,
  /*  332 */  indirect_rule,
  /*  333 */  indirect_rule,
  /*  334 */  indirect_rule,
  /*  335 */  indirect_rule,
  /*  336 */  indirect_rule,
  /*  337 */  indirect_rule,
  /*  338 */  indirect_rule,
  /*  339 */  indirect_rule,
  /*  340 */  indirect_rule,
  /*  341 */  indirect_rule,
  /*  342 */  indirect_rule,
  /*  343 */  indirect_rule,
  /*  344 */  indirect_rule,
  /*  345 */  indirect_rule,
  /*  346 */  indirect_rule,
  /*  347 */  indirect_rule,
  /*  348 */  indirect_rule,
  /*  349 */  indirect_rule,
  /*  350 */  indirect_rule,
  /*  351 */  indirect_rule,
  /*  352 */  indirect_rule,
  /*  353 */  indirect_rule,
  /*  354 */  indirect_rule,
  /*  355 */  indirect_rule,
  /*  356 */  indirect_rule,
  /*  357 */  indirect_rule,
  /*  358 */  indirect_rule,
  /*  359 */  indirect_rule,
  /*  360 */  iRegIorL2I_rule,
  /*  361 */  iRegIorL2I_rule,
  /*  362 */  _ConvL2I_iRegL__rule,
  /*  363 */  iRegP_rule,
  /*  364 */  _ConvI2L_iRegI__rule,
  /*  365 */  iRegP_rule,
  /*  366 */  iRegL_rule,
  /*  367 */  iRegL_rule,
  /*  368 */  iRegIorL2I_rule,
  /*  369 */  iRegIorL2I_rule,
  /*  370 */  iRegL_rule,
  /*  371 */  iRegL_rule,
  /*  372 */  immI0_rule,
  /*  373 */  immL0_rule,
  /*  374 */  iRegIorL2I_rule,
  /*  375 */  iRegL_rule,
  /*  376 */  iRegL_rule,
  /*  377 */  iRegIorL2I_rule,
  /*  378 */  _RShiftI_iRegIorL2I_immI_31_rule,
  /*  379 */  iRegL_rule,
  /*  380 */  _RShiftL_iRegL_immI_63_rule,
  /*  381 */  iRegIorL2I_rule,
  /*  382 */  iRegL_rule,
  /*  383 */  iRegIorL2I_rule,
  /*  384 */  iRegIorL2I_rule,
  /*  385 */  iRegIorL2I_rule,
  /*  386 */  iRegIorL2I_rule,
  /*  387 */  iRegIorL2I_rule,
  /*  388 */  iRegIorL2I_rule,
  /*  389 */  iRegL_rule,
  /*  390 */  iRegL_rule,
  /*  391 */  iRegL_rule,
  /*  392 */  iRegL_rule,
  /*  393 */  _CastP2X_iRegP__rule,
  /*  394 */  iRegL_rule,
  /*  395 */  iRegL_rule,
  /*  396 */  iRegI_rule,
  /*  397 */  iRegL_rule,
  /*  398 */  fRegF_rule,
  /*  399 */  fRegD_rule,
  /*  400 */  fRegF_rule,
  /*  401 */  fRegD_rule,
  /*  402 */  fRegF_rule,
  /*  403 */  fRegD_rule,
  /*  404 */  fRegF_rule,
  /*  405 */  fRegD_rule,
  /*  406 */  _NegF_fRegF__rule,
  /*  407 */  _NegD_fRegD__rule,
  /*  408 */  fRegF_rule,
  /*  409 */  fRegF_rule,
  /*  410 */  fRegD_rule,
  /*  411 */  fRegD_rule,
  /*  412 */  _NegF_fRegF__rule,
  /*  413 */  _NegF_fRegF__rule,
  /*  414 */  _NegD_fRegD__rule,
  /*  415 */  _NegD_fRegD__rule,
  /*  416 */  fRegF_rule,
  /*  417 */  fRegF_rule,
  /*  418 */  fRegD_rule,
  /*  419 */  fRegD_rule,
  /*  420 */  fRegF_rule,
  /*  421 */  fRegD_rule,
  /*  422 */  _SqrtD__ConvF2D_fRegF___rule,
  /*  423 */  fRegD_rule,
  /*  424 */  iRegI_rule,
  /*  425 */  iRegI_rule,
  /*  426 */  iRegI_rule,
  /*  427 */  iRegI_rule,
  /*  428 */  iRegI_rule,
  /*  429 */  iRegI_rule,
  /*  430 */  iRegL_rule,
  /*  431 */  iRegL_rule,
  /*  432 */  iRegL_rule,
  /*  433 */  iRegL_rule,
  /*  434 */  iRegL_rule,
  /*  435 */  iRegL_rule,
  /*  436 */  iRegIorL2I_rule,
  /*  437 */  iRegL_rule,
  /*  438 */  iRegIorL2I_rule,
  /*  439 */  iRegIorL2I_rule,
  /*  440 */  0,
  /*  441 */  0,
  /*  442 */  0,
  /*  443 */  0,
  /*  444 */  0,
  /*  445 */  0,
  /*  446 */  0,
  /*  447 */  0,
  /*  448 */  0,
  /*  449 */  iRegIorL2I_rule,
  /*  450 */  iRegL_rule,
  /*  451 */  _ConvI2L_iRegIorL2I__rule,
  /*  452 */  fRegF_rule,
  /*  453 */  fRegD_rule,
  /*  454 */  fRegF_rule,
  /*  455 */  iRegIorL2I_rule,
  /*  456 */  fRegF_rule,
  /*  457 */  iRegL_rule,
  /*  458 */  fRegD_rule,
  /*  459 */  iRegIorL2I_rule,
  /*  460 */  fRegD_rule,
  /*  461 */  iRegL_rule,
  /*  462 */  _CastP2X_iRegP__rule,
  /*  463 */  _CastP2X__DecodeN_iRegN___rule,
  /*  464 */  iRegP_rule,
  /*  465 */  iRegN_rule,
  /*  466 */  iRegN_rule,
  /*  467 */  iRegP_rule,
  /*  468 */  iRegN_rule,
  /*  469 */  fRegF_rule,
  /*  470 */  iRegI_rule,
  /*  471 */  fRegD_rule,
  /*  472 */  iRegL_rule,
  /*  473 */  fRegF_rule,
  /*  474 */  fRegD_rule,
  /*  475 */  iRegL_rule,
  /*  476 */  iRegI_rule,
  /*  477 */  iRegIorL2I_rule,
  /*  478 */  iRegI_rule,
  /*  479 */  iRegI_rule,
  /*  480 */  0,
  /*  481 */  cmpOpEqNe_rule,
  /*  482 */  cmpOp_rule,
  /*  483 */  cmpOp_rule,
  /*  484 */  cmpOpU_rule,
  /*  485 */  cmpOpU_rule,
  /*  486 */  cmpOp_rule,
  /*  487 */  cmpOp_rule,
  /*  488 */  cmpOpU_rule,
  /*  489 */  cmpOpU_rule,
  /*  490 */  cmpOpU_rule,
  /*  491 */  cmpOpU_rule,
  /*  492 */  cmpOpU_rule,
  /*  493 */  cmpOpU_rule,
  /*  494 */  cmpOp_rule,
  /*  495 */  cmpOp_rule,
  /*  496 */  cmpOp_rule,
  /*  497 */  cmpOp_rule,
  /*  498 */  cmpOp_rule,
  /*  499 */  cmpOp_rule,
  /*  500 */  cmpOpUEqNeLeGt_rule,
  /*  501 */  cmpOpUEqNeLeGt_rule,
  /*  502 */  cmpOp_rule,
  /*  503 */  cmpOp_rule,
  /*  504 */  cmpOpUEqNeLeGt_rule,
  /*  505 */  cmpOpUEqNeLeGt_rule,
  /*  506 */  cmpOpEqNe_rule,
  /*  507 */  cmpOpEqNe_rule,
  /*  508 */  cmpOpEqNe_rule,
  /*  509 */  cmpOpEqNe_rule,
  /*  510 */  cmpOpEqNe_rule,
  /*  511 */  cmpOpEqNe_rule,
  /*  512 */  cmpOp_rule,
  /*  513 */  cmpOp_rule,
  /*  514 */  cmpOp_rule,
  /*  515 */  cmpOpU_rule,
  /*  516 */  cmpOpU_rule,
  /*  517 */  cmpOp_rule,
  /*  518 */  cmpOp_rule,
  /*  519 */  cmpOpU_rule,
  /*  520 */  cmpOpU_rule,
  /*  521 */  cmpOpU_rule,
  /*  522 */  cmpOpU_rule,
  /*  523 */  cmpOpU_rule,
  /*  524 */  cmpOpU_rule,
  /*  525 */  cmpOp_rule,
  /*  526 */  cmpOp_rule,
  /*  527 */  cmpOp_rule,
  /*  528 */  cmpOp_rule,
  /*  529 */  cmpOp_rule,
  /*  530 */  cmpOp_rule,
  /*  531 */  cmpOpUEqNeLeGt_rule,
  /*  532 */  cmpOpUEqNeLeGt_rule,
  /*  533 */  cmpOpULtGe_rule,
  /*  534 */  cmpOpULtGe_rule,
  /*  535 */  cmpOp_rule,
  /*  536 */  cmpOp_rule,
  /*  537 */  cmpOpUEqNeLeGt_rule,
  /*  538 */  cmpOpUEqNeLeGt_rule,
  /*  539 */  cmpOpULtGe_rule,
  /*  540 */  cmpOpULtGe_rule,
  /*  541 */  cmpOpEqNe_rule,
  /*  542 */  cmpOpEqNe_rule,
  /*  543 */  cmpOpEqNe_rule,
  /*  544 */  cmpOpEqNe_rule,
  /*  545 */  cmpOpEqNe_rule,
  /*  546 */  cmpOpEqNe_rule,
  /*  547 */  _Binary_cmpOp__CmpI_iRegI_iRegI_rule,
  /*  548 */  _Binary_cmpOpU__CmpU_iRegI_iRegI_rule,
  /*  549 */  _Binary_cmpOp__CmpL_iRegL_iRegL_rule,
  /*  550 */  _Binary_cmpOp__CmpL_iRegL_iRegL_rule,
  /*  551 */  _Binary_cmpOpU__CmpUL_iRegL_iRegL_rule,
  /*  552 */  _Binary_cmpOpU__CmpUL_iRegL_iRegL_rule,
  /*  553 */  0,
  /*  554 */  0,
  /*  555 */  0,
  /*  556 */  0,
  /*  557 */  0,
  /*  558 */  iRegP_R14_rule,
  /*  559 */  _Binary_iRegP_R11_iRegI_R12_rule,
  /*  560 */  _Binary_iRegP_R11_iRegI_R12_rule,
  /*  561 */  _Binary_iRegP_R11_iRegI_R12_rule,
  /*  562 */  _Binary_iRegP_R11_iRegI_R12_rule,
  /*  563 */  _Binary_iRegP_R11_iRegI_R12_rule,
  /*  564 */  _Binary_iRegP_R11_iRegI_R12_rule,
  /*  565 */  _Binary_iRegP_R11_iRegI_R12_rule,
  /*  566 */  _Binary_iRegP_R11_iRegI_R12_rule,
  /*  567 */  _Binary_iRegP_R11_iRegI_R12_rule,
  /*  568 */  _Binary_iRegP_R11_iRegI_R12_rule,
  /*  569 */  _Binary_iRegP_R11_iRegI_R12_rule,
  /*  570 */  _Binary_iRegP_R11_iRegI_R12_rule,
  /*  571 */  iRegL_R29_rule,
  /*  572 */  immL_rule,
  /*  573 */  _Binary_iRegP_R11_iRegP_R13_rule,
  /*  574 */  _Binary_iRegP_R11_iRegP_R13_rule,
  /*  575 */  iRegP_R11_rule,
  /*  576 */  iRegP_R11_rule,
  /*  577 */  iRegP_rule,
  /*  578 */  iRegPNoSp_rule,
  /*  579 */  iRegPNoSp_rule,
  /*  580 */  0,
  /*  581 */  0,
  /*  582 */  0,
  /*  583 */  0,
  /*  584 */  vmemA_rule,
  /*  585 */  vmemA_rule,
  /*  586 */  vReg_rule,
  /*  587 */  vReg_rule,
  /*  588 */  vReg_rule,
  /*  589 */  vReg_rule,
  /*  590 */  vReg_rule,
  /*  591 */  vReg_rule,
  /*  592 */  vReg_rule,
  /*  593 */  _Binary_vReg_vReg_rule,
  /*  594 */  vReg_rule,
  /*  595 */  vReg_rule,
  /*  596 */  vReg_rule,
  /*  597 */  vReg_rule,
  /*  598 */  vReg_rule,
  /*  599 */  vReg_rule,
  /*  600 */  vReg_rule,
  /*  601 */  vReg_rule,
  /*  602 */  vReg_rule,
  /*  603 */  vReg_rule,
  /*  604 */  vReg_rule,
  /*  605 */  vReg_rule,
  /*  606 */  vReg_rule,
  /*  607 */  vReg_rule,
  /*  608 */  vReg_rule,
  /*  609 */  vReg_rule,
  /*  610 */  vReg_rule,
  /*  611 */  vReg_rule,
  /*  612 */  vReg_rule,
  /*  613 */  vReg_rule,
  /*  614 */  _NegVF_vReg__rule,
  /*  615 */  _NegVF_vReg__rule,
  /*  616 */  _NegVD_vReg__rule,
  /*  617 */  _NegVD_vReg__rule,
  /*  618 */  _NegVF_vReg__rule,
  /*  619 */  _NegVD_vReg__rule,
  /*  620 */  vReg_rule,
  /*  621 */  _MulVB_vReg_vReg_rule,
  /*  622 */  vReg_rule,
  /*  623 */  _MulVS_vReg_vReg_rule,
  /*  624 */  vReg_rule,
  /*  625 */  _MulVI_vReg_vReg_rule,
  /*  626 */  vReg_rule,
  /*  627 */  _MulVL_vReg_vReg_rule,
  /*  628 */  vReg_rule,
  /*  629 */  vReg_rule,
  /*  630 */  vReg_rule,
  /*  631 */  vReg_rule,
  /*  632 */  vReg_rule,
  /*  633 */  vReg_rule,
  /*  634 */  vReg_rule,
  /*  635 */  vReg_rule,
  /*  636 */  vReg_rule,
  /*  637 */  vReg_rule,
  /*  638 */  iRegIorL2I_rule,
  /*  639 */  iRegL_rule,
  /*  640 */  iRegIorL2I_rule,
  /*  641 */  iRegL_rule,
  /*  642 */  iRegIorL2I_rule,
  /*  643 */  iRegL_rule,
  /*  644 */  iRegIorL2I_rule,
  /*  645 */  iRegL_rule,
  /*  646 */  fRegF_rule,
  /*  647 */  fRegD_rule,
  /*  648 */  iRegIorL2I_rule,
  /*  649 */  iRegL_rule,
  /*  650 */  iRegIorL2I_rule,
  /*  651 */  iRegL_rule,
  /*  652 */  fRegF_rule,
  /*  653 */  fRegD_rule,
  /*  654 */  fRegF_rule,
  /*  655 */  fRegD_rule,
  /*  656 */  vReg_rule,
  /*  657 */  vReg_rule,
  /*  658 */  vReg_rule,
  /*  659 */  vReg_rule,
  /*  660 */  vReg_rule,
  /*  661 */  vReg_rule,
  /*  662 */  vReg_rule,
  /*  663 */  vReg_rule,
  /*  664 */  vReg_rule,
  /*  665 */  vReg_rule,
  /*  666 */  vReg_rule,
  /*  667 */  vReg_rule,
  /*  668 */  vReg_rule,
  /*  669 */  vReg_rule,
  /*  670 */  vReg_rule,
  /*  671 */  vReg_rule,
  /*  672 */  vReg_rule,
  /*  673 */  vReg_rule,
  /*  674 */  vReg_rule,
  /*  675 */  vReg_rule,
  /*  676 */  vReg_rule,
  /*  677 */  vReg_rule,
  /*  678 */  vReg_rule,
  /*  679 */  vReg_rule,
  /*  680 */  vReg_rule,
  /*  681 */  vReg_rule,
  /*  682 */  vReg_rule,
  /*  683 */  vReg_rule,
  /*  684 */  vReg_rule,
  /*  685 */  vReg_rule,
  /*  686 */  vReg_rule,
  /*  687 */  _Binary_iRegP_R11_iRegP_R13_rule,
  /*  688 */  _Binary_iRegP_R11_iRegP_R13_rule,
  /*  689 */  iRegP_R11_rule,
  /*  690 */  iRegP_R11_rule,
  /*  691 */  _Binary_iRegP_R11_iRegI_R12_rule,
  /*  692 */  _Binary_iRegP_R11_iRegI_R12_rule,
  /*  693 */  _Binary_iRegP_R11_iRegI_R12_rule,
  /*  694 */  _Binary_iRegP_R11_iRegI_R12_rule,
  /*  695 */  iRegP_R10_rule,
  /*  696 */  iRegP_R12_rule,
  /*  697 */  iRegP_R12_rule,
  /*  698 */  iRegP_R11_rule,
  /*  699 */  _Binary_iRegP_R11_iRegI_R12_rule,
  /*  700 */  _Binary_iRegP_R11_iRegI_R12_rule,
  /*  701 */  iRegL_R29_rule,
  /*  702 */  iRegI_rule,
  /*  703 */  iRegL_rule,
  /*  704 */  iRegI_rule,
  /*  705 */  iRegL_rule,
  /*  706 */  iRegI_rule,
  /*  707 */  iRegL_rule,
  /*  708 */  _CastP2X_iRegP__rule,
  /*  709 */  _LShiftI_iRegIorL2I_immI_24_rule,
  /*  710 */  _LShiftI_iRegIorL2I_immI_16_rule,
  /*  711 */  iRegIorL2I_rule,
  /*  712 */  _ConvI2L_iRegIorL2I__rule,
  /*  713 */  iRegIorL2I_rule,
  /*  714 */  iRegL_rule,
  /*  715 */  iRegIorL2I_rule,
  /*  716 */  iRegIorL2I_rule,
  /*  717 */  iRegP_rule,
  /*  718 */  iRegP_rule,
  /*  719 */  iRegL_rule,
  /*  720 */  _LShiftL_iRegL_immIScale_rule,
  /*  721 */  iRegL_rule,
  /*  722 */  _LShiftL__ConvI2L_iRegI__immIScale_rule,
  /*  723 */  iRegI_rule,
  /*  724 */  iRegI_rule,
  /*  725 */  iRegI_rule,
  /*  726 */  _XorI_iRegI_immI_M1_rule,
  /*  727 */  iRegL_rule,
  /*  728 */  _XorL_iRegL_immL_M1_rule,
  /*  729 */  iRegI_rule,
  /*  730 */  _XorI_iRegI_immI_M1_rule,
  /*  731 */  iRegL_rule,
  /*  732 */  _XorL_iRegL_immL_M1_rule,
  /*  733 */  indirect_rule,
  /*  734 */  indirect_rule,
  /*  735 */  indirect_rule,
  /*  736 */  indirect_rule,
  /*  737 */  indirect_rule,
  /*  738 */  indirect_rule,
  /*  739 */  indirect_rule,
  /*  740 */  indirect_rule,
  /*  741 */  indirect_rule,
  /*  742 */  indirect_rule,
  /*  743 */  indirect_rule,
  /*  744 */  indirect_rule,
  /*  745 */  memory_rule,
  /*  746 */  indirect_rule,
  /*  747 */  indirect_rule,
  /*  748 */  indirect_rule,
  /*  749 */  indirect_rule,
  /*  750 */  indirect_rule,
  /*  751 */  indirect_rule,
  /*  752 */  indirect_rule,
  /*  753 */  indirect_rule,
  // last instruction
  0 // no trailing comma
};

const        int   rightOp[] = {
  /*    0 */  0,
  /*    1 */  0,
  /*    2 */  0,
  /*    3 */  0,
  /*    4 */  0,
  /*    5 */  0,
  /*    6 */  0,
  /*    7 */  0,
  /*    8 */  0,
  /*    9 */  0,
  /*   10 */  0,
  /*   11 */  0,
  /*   12 */  0,
  /*   13 */  0,
  /*   14 */  0,
  /*   15 */  0,
  /*   16 */  0,
  /*   17 */  0,
  /*   18 */  0,
  /*   19 */  0,
  /*   20 */  0,
  /*   21 */  0,
  /*   22 */  0,
  /*   23 */  0,
  /*   24 */  0,
  /*   25 */  0,
  /*   26 */  0,
  /*   27 */  0,
  /*   28 */  0,
  /*   29 */  0,
  /*   30 */  0,
  /*   31 */  0,
  /*   32 */  0,
  /*   33 */  0,
  /*   34 */  0,
  /*   35 */  0,
  /*   36 */  0,
  /*   37 */  0,
  /*   38 */  0,
  /*   39 */  0,
  /*   40 */  0,
  /*   41 */  0,
  /*   42 */  0,
  /*   43 */  0,
  /*   44 */  0,
  /*   45 */  0,
  /*   46 */  0,
  /*   47 */  0,
  /*   48 */  0,
  /*   49 */  0,
  /*   50 */  0,
  /*   51 */  0,
  /*   52 */  0,
  /*   53 */  0,
  /*   54 */  0,
  /*   55 */  0,
  /*   56 */  0,
  /*   57 */  0,
  /*   58 */  0,
  /*   59 */  0,
  /*   60 */  0,
  /*   61 */  0,
  /*   62 */  0,
  /*   63 */  0,
  /*   64 */  0,
  /*   65 */  0,
  /*   66 */  0,
  /*   67 */  0,
  /*   68 */  0,
  /*   69 */  0,
  /*   70 */  0,
  /*   71 */  0,
  /*   72 */  0,
  /*   73 */  0,
  /*   74 */  0,
  /*   75 */  0,
  /*   76 */  0,
  /*   77 */  0,
  /*   78 */  0,
  /*   79 */  0,
  /*   80 */  0,
  /*   81 */  immIOffset_rule,
  /*   82 */  immLOffset_rule,
  /*   83 */  0,
  /*   84 */  immIOffset_rule,
  /*   85 */  immLOffset_rule,
  /*   86 */  immL_pc_off_rule,
  /*   87 */  0,
  /*   88 */  0,
  /*   89 */  0,
  /*   90 */  0,
  /*   91 */  0,
  /*   92 */  0,
  /*   93 */  0,
  /*   94 */  0,
  /*   95 */  0,
  /*   96 */  0,
  /*   97 */  0,
  /*   98 */  0,
  /*   99 */  0,
  // last operand
  /*  100 */  0,
  /*  101 */  0,
  /*  102 */  0,
  /*  103 */  0,
  /*  104 */  0,
  /*  105 */  0,
  /*  106 */  0,
  /*  107 */  0,
  // last operand class
  /*  108 */  0,
  /*  109 */  0,
  /*  110 */  0,
  /*  111 */  0,
  /*  112 */  0,
  /*  113 */  0,
  /*  114 */  0,
  /*  115 */  iRegI_R13_rule,
  /*  116 */  iRegI_rule,
  /*  117 */  iRegL_rule,
  /*  118 */  iRegP_rule,
  /*  119 */  iRegN_rule,
  /*  120 */  0,
  /*  121 */  0,
  /*  122 */  immI_31_rule,
  /*  123 */  immI_63_rule,
  /*  124 */  0,
  /*  125 */  fRegF_rule,
  /*  126 */  fRegD_rule,
  /*  127 */  0,
  /*  128 */  0,
  /*  129 */  fRegF_rule,
  /*  130 */  _NegF_fRegF__rule,
  /*  131 */  fRegD_rule,
  /*  132 */  _NegD_fRegD__rule,
  /*  133 */  0,
  /*  134 */  0,
  /*  135 */  0,
  /*  136 */  0,
  /*  137 */  iRegI_rule,
  /*  138 */  iRegI_rule,
  /*  139 */  iRegL_rule,
  /*  140 */  iRegL_rule,
  /*  141 */  iRegP_rule,
  /*  142 */  iRegN_rule,
  /*  143 */  fRegF_rule,
  /*  144 */  fRegD_rule,
  /*  145 */  immI0_rule,
  /*  146 */  immI0_rule,
  /*  147 */  immL0_rule,
  /*  148 */  immL0_rule,
  /*  149 */  immP0_rule,
  /*  150 */  immN0_rule,
  /*  151 */  immP0_rule,
  /*  152 */  _CmpI_iRegI_iRegI_rule,
  /*  153 */  iRegI_rule,
  /*  154 */  _CmpU_iRegI_iRegI_rule,
  /*  155 */  _CmpL_iRegL_iRegL_rule,
  /*  156 */  iRegL_rule,
  /*  157 */  _CmpUL_iRegL_iRegL_rule,
  /*  158 */  iRegP_R10_rule,
  /*  159 */  iRegI_R12_rule,
  /*  160 */  iRegI_R14_rule,
  /*  161 */  immI_le_4_rule,
  /*  162 */  immI_1_rule,
  /*  163 */  iRegP_R13_rule,
  /*  164 */  vReg_rule,
  /*  165 */  0,
  /*  166 */  vReg_rule,
  /*  167 */  _NegVF_vReg__rule,
  /*  168 */  0,
  /*  169 */  vReg_rule,
  /*  170 */  _NegVD_vReg__rule,
  /*  171 */  vReg_rule,
  /*  172 */  vReg_rule,
  /*  173 */  vReg_rule,
  /*  174 */  vReg_rule,
  /*  175 */  0,
  /*  176 */  0,
  /*  177 */  iRegI_R13_rule,
  /*  178 */  immI_24_rule,
  /*  179 */  immI_16_rule,
  /*  180 */  immIScale_rule,
  /*  181 */  immIScale_rule,
  /*  182 */  immI_M1_rule,
  /*  183 */  immL_M1_rule,
  // last internally defined operand
  /*  184 */  0,
  /*  185 */  0,
  /*  186 */  0,
  /*  187 */  0,
  /*  188 */  0,
  /*  189 */  0,
  /*  190 */  0,
  /*  191 */  0,
  /*  192 */  0,
  /*  193 */  0,
  /*  194 */  0,
  /*  195 */  0,
  /*  196 */  0,
  /*  197 */  0,
  /*  198 */  0,
  /*  199 */  0,
  /*  200 */  0,
  /*  201 */  0,
  /*  202 */  0,
  /*  203 */  0,
  /*  204 */  0,
  /*  205 */  0,
  /*  206 */  0,
  /*  207 */  0,
  /*  208 */  0,
  /*  209 */  0,
  /*  210 */  0,
  /*  211 */  0,
  /*  212 */  0,
  /*  213 */  0,
  /*  214 */  0,
  /*  215 */  0,
  /*  216 */  0,
  /*  217 */  0,
  /*  218 */  0,
  /*  219 */  0,
  /*  220 */  0,
  /*  221 */  0,
  /*  222 */  0,
  /*  223 */  0,
  /*  224 */  0,
  /*  225 */  0,
  /*  226 */  immP0_rule,
  /*  227 */  0,
  /*  228 */  iRegP_rule,
  /*  229 */  iRegP_rule,
  /*  230 */  0,
  /*  231 */  0,
  /*  232 */  0,
  /*  233 */  0,
  /*  234 */  0,
  /*  235 */  0,
  /*  236 */  0,
  /*  237 */  0,
  /*  238 */  0,
  /*  239 */  0,
  /*  240 */  0,
  /*  241 */  0,
  /*  242 */  0,
  /*  243 */  0,
  /*  244 */  0,
  /*  245 */  0,
  /*  246 */  0,
  /*  247 */  0,
  /*  248 */  0,
  /*  249 */  0,
  /*  250 */  0,
  /*  251 */  0,
  /*  252 */  0,
  /*  253 */  0,
  /*  254 */  0,
  /*  255 */  0,
  /*  256 */  0,
  /*  257 */  0,
  /*  258 */  0,
  /*  259 */  0,
  /*  260 */  0,
  /*  261 */  0,
  /*  262 */  0,
  /*  263 */  0,
  /*  264 */  0,
  /*  265 */  0,
  /*  266 */  0,
  /*  267 */  0,
  /*  268 */  0,
  /*  269 */  0,
  /*  270 */  0,
  /*  271 */  0,
  /*  272 */  0,
  /*  273 */  0,
  /*  274 */  immL_32bits_rule,
  /*  275 */  0,
  /*  276 */  0,
  /*  277 */  0,
  /*  278 */  0,
  /*  279 */  0,
  /*  280 */  0,
  /*  281 */  0,
  /*  282 */  0,
  /*  283 */  immI0_rule,
  /*  284 */  immI0_rule,
  /*  285 */  iRegIorL2I_rule,
  /*  286 */  immI0_rule,
  /*  287 */  iRegIorL2I_rule,
  /*  288 */  immI0_rule,
  /*  289 */  iRegIorL2I_rule,
  /*  290 */  immI0_rule,
  /*  291 */  iRegL_rule,
  /*  292 */  immL0_rule,
  /*  293 */  iRegP_rule,
  /*  294 */  immP0_rule,
  /*  295 */  iRegN_rule,
  /*  296 */  immN0_rule,
  /*  297 */  fRegF_rule,
  /*  298 */  fRegD_rule,
  /*  299 */  iRegN_rule,
  /*  300 */  _Binary_iRegI_R12_iRegI_R13_rule,
  /*  301 */  _Binary_iRegI_R12_iRegI_R13_rule,
  /*  302 */  _Binary_iRegI_iRegI_rule,
  /*  303 */  _Binary_iRegL_iRegL_rule,
  /*  304 */  _Binary_iRegP_iRegP_rule,
  /*  305 */  _Binary_iRegN_iRegN_rule,
  /*  306 */  _Binary_iRegI_R12_iRegI_R13_rule,
  /*  307 */  _Binary_iRegI_R12_iRegI_R13_rule,
  /*  308 */  _Binary_iRegI_iRegI_rule,
  /*  309 */  _Binary_iRegL_iRegL_rule,
  /*  310 */  _Binary_iRegP_iRegP_rule,
  /*  311 */  _Binary_iRegN_iRegN_rule,
  /*  312 */  _Binary_iRegI_R12_iRegI_R13_rule,
  /*  313 */  _Binary_iRegI_R12_iRegI_R13_rule,
  /*  314 */  _Binary_iRegI_iRegI_rule,
  /*  315 */  _Binary_iRegL_iRegL_rule,
  /*  316 */  _Binary_iRegN_iRegN_rule,
  /*  317 */  _Binary_iRegP_iRegP_rule,
  /*  318 */  _Binary_iRegI_R12_iRegI_R13_rule,
  /*  319 */  _Binary_iRegI_R12_iRegI_R13_rule,
  /*  320 */  _Binary_iRegI_iRegI_rule,
  /*  321 */  _Binary_iRegL_iRegL_rule,
  /*  322 */  _Binary_iRegN_iRegN_rule,
  /*  323 */  _Binary_iRegP_iRegP_rule,
  /*  324 */  _Binary_iRegI_R12_iRegI_R13_rule,
  /*  325 */  _Binary_iRegI_R12_iRegI_R13_rule,
  /*  326 */  _Binary_iRegI_iRegI_rule,
  /*  327 */  _Binary_iRegL_iRegL_rule,
  /*  328 */  _Binary_iRegN_iRegN_rule,
  /*  329 */  _Binary_iRegP_iRegP_rule,
  /*  330 */  _Binary_iRegI_R12_iRegI_R13_rule,
  /*  331 */  _Binary_iRegI_R12_iRegI_R13_rule,
  /*  332 */  _Binary_iRegI_iRegI_rule,
  /*  333 */  _Binary_iRegL_iRegL_rule,
  /*  334 */  _Binary_iRegN_iRegN_rule,
  /*  335 */  _Binary_iRegP_iRegP_rule,
  /*  336 */  iRegI_rule,
  /*  337 */  iRegL_rule,
  /*  338 */  iRegN_rule,
  /*  339 */  iRegP_rule,
  /*  340 */  iRegI_rule,
  /*  341 */  iRegL_rule,
  /*  342 */  iRegN_rule,
  /*  343 */  iRegP_rule,
  /*  344 */  iRegL_rule,
  /*  345 */  iRegL_rule,
  /*  346 */  immLAdd_rule,
  /*  347 */  immLAdd_rule,
  /*  348 */  iRegIorL2I_rule,
  /*  349 */  iRegIorL2I_rule,
  /*  350 */  immIAdd_rule,
  /*  351 */  immIAdd_rule,
  /*  352 */  iRegL_rule,
  /*  353 */  iRegL_rule,
  /*  354 */  immLAdd_rule,
  /*  355 */  immLAdd_rule,
  /*  356 */  iRegIorL2I_rule,
  /*  357 */  iRegIorL2I_rule,
  /*  358 */  immIAdd_rule,
  /*  359 */  immIAdd_rule,
  /*  360 */  iRegIorL2I_rule,
  /*  361 */  immIAdd_rule,
  /*  362 */  immIAdd_rule,
  /*  363 */  iRegL_rule,
  /*  364 */  uimmI6_ge32_rule,
  /*  365 */  immLAdd_rule,
  /*  366 */  iRegL_rule,
  /*  367 */  immLAdd_rule,
  /*  368 */  iRegIorL2I_rule,
  /*  369 */  immISub_rule,
  /*  370 */  iRegL_rule,
  /*  371 */  immLSub_rule,
  /*  372 */  iRegIorL2I_rule,
  /*  373 */  iRegL_rule,
  /*  374 */  iRegIorL2I_rule,
  /*  375 */  iRegL_rule,
  /*  376 */  iRegL_rule,
  /*  377 */  iRegIorL2I_rule,
  /*  378 */  immI_31_rule,
  /*  379 */  iRegL_rule,
  /*  380 */  immI_63_rule,
  /*  381 */  iRegIorL2I_rule,
  /*  382 */  iRegL_rule,
  /*  383 */  iRegIorL2I_rule,
  /*  384 */  immI_rule,
  /*  385 */  iRegIorL2I_rule,
  /*  386 */  immI_rule,
  /*  387 */  iRegIorL2I_rule,
  /*  388 */  immI_rule,
  /*  389 */  iRegIorL2I_rule,
  /*  390 */  immI_rule,
  /*  391 */  iRegIorL2I_rule,
  /*  392 */  immI_rule,
  /*  393 */  immI_rule,
  /*  394 */  iRegIorL2I_rule,
  /*  395 */  immI_rule,
  /*  396 */  immI_M1_rule,
  /*  397 */  immL_M1_rule,
  /*  398 */  fRegF_rule,
  /*  399 */  fRegD_rule,
  /*  400 */  fRegF_rule,
  /*  401 */  fRegD_rule,
  /*  402 */  fRegF_rule,
  /*  403 */  fRegD_rule,
  /*  404 */  _Binary_fRegF_fRegF_rule,
  /*  405 */  _Binary_fRegD_fRegD_rule,
  /*  406 */  _Binary_fRegF_fRegF_rule,
  /*  407 */  _Binary_fRegD_fRegD_rule,
  /*  408 */  _Binary__NegF_fRegF__fRegF_rule,
  /*  409 */  _Binary_fRegF__NegF_fRegF__rule,
  /*  410 */  _Binary__NegD_fRegD__fRegD_rule,
  /*  411 */  _Binary_fRegD__NegD_fRegD__rule,
  /*  412 */  _Binary__NegF_fRegF__fRegF_rule,
  /*  413 */  _Binary_fRegF__NegF_fRegF__rule,
  /*  414 */  _Binary__NegD_fRegD__fRegD_rule,
  /*  415 */  _Binary_fRegD__NegD_fRegD__rule,
  /*  416 */  fRegF_rule,
  /*  417 */  fRegF_rule,
  /*  418 */  fRegD_rule,
  /*  419 */  fRegD_rule,
  /*  420 */  fRegF_rule,
  /*  421 */  fRegD_rule,
  /*  422 */  0,
  /*  423 */  0,
  /*  424 */  iRegI_rule,
  /*  425 */  immIAdd_rule,
  /*  426 */  iRegI_rule,
  /*  427 */  immIAdd_rule,
  /*  428 */  iRegI_rule,
  /*  429 */  immIAdd_rule,
  /*  430 */  iRegL_rule,
  /*  431 */  immLAdd_rule,
  /*  432 */  iRegL_rule,
  /*  433 */  immLAdd_rule,
  /*  434 */  iRegL_rule,
  /*  435 */  immLAdd_rule,
  /*  436 */  0,
  /*  437 */  0,
  /*  438 */  0,
  /*  439 */  0,
  /*  440 */  0,
  /*  441 */  0,
  /*  442 */  0,
  /*  443 */  0,
  /*  444 */  0,
  /*  445 */  0,
  /*  446 */  0,
  /*  447 */  0,
  /*  448 */  0,
  /*  449 */  0,
  /*  450 */  0,
  /*  451 */  immL_32bits_rule,
  /*  452 */  0,
  /*  453 */  0,
  /*  454 */  0,
  /*  455 */  0,
  /*  456 */  0,
  /*  457 */  0,
  /*  458 */  0,
  /*  459 */  0,
  /*  460 */  0,
  /*  461 */  0,
  /*  462 */  0,
  /*  463 */  0,
  /*  464 */  0,
  /*  465 */  0,
  /*  466 */  0,
  /*  467 */  0,
  /*  468 */  0,
  /*  469 */  0,
  /*  470 */  0,
  /*  471 */  0,
  /*  472 */  0,
  /*  473 */  fRegF_rule,
  /*  474 */  fRegD_rule,
  /*  475 */  iRegL_rule,
  /*  476 */  iRegI_rule,
  /*  477 */  immI0_rule,
  /*  478 */  iRegI_rule,
  /*  479 */  iRegI_rule,
  /*  480 */  0,
  /*  481 */  rFlagsReg_rule,
  /*  482 */  _CmpI_iRegI_iRegI_rule,
  /*  483 */  _CmpI_iRegI_iRegI_rule,
  /*  484 */  _CmpU_iRegI_iRegI_rule,
  /*  485 */  _CmpU_iRegI_iRegI_rule,
  /*  486 */  _CmpL_iRegL_iRegL_rule,
  /*  487 */  _CmpL_iRegL_iRegL_rule,
  /*  488 */  _CmpUL_iRegL_iRegL_rule,
  /*  489 */  _CmpUL_iRegL_iRegL_rule,
  /*  490 */  _CmpP_iRegP_iRegP_rule,
  /*  491 */  _CmpP_iRegP_iRegP_rule,
  /*  492 */  _CmpN_iRegN_iRegN_rule,
  /*  493 */  _CmpN_iRegN_iRegN_rule,
  /*  494 */  _CmpF_fRegF_fRegF_rule,
  /*  495 */  _CmpF_fRegF_fRegF_rule,
  /*  496 */  _CmpD_fRegD_fRegD_rule,
  /*  497 */  _CmpD_fRegD_fRegD_rule,
  /*  498 */  _CmpI_iRegI_immI0_rule,
  /*  499 */  _CmpI_iRegI_immI0_rule,
  /*  500 */  _CmpU_iRegI_immI0_rule,
  /*  501 */  _CmpU_iRegI_immI0_rule,
  /*  502 */  _CmpL_iRegL_immL0_rule,
  /*  503 */  _CmpL_iRegL_immL0_rule,
  /*  504 */  _CmpUL_iRegL_immL0_rule,
  /*  505 */  _CmpUL_iRegL_immL0_rule,
  /*  506 */  _CmpP_iRegP_immP0_rule,
  /*  507 */  _CmpP_iRegP_immP0_rule,
  /*  508 */  _CmpN_iRegN_immN0_rule,
  /*  509 */  _CmpN_iRegN_immN0_rule,
  /*  510 */  _CmpP__DecodeN_iRegN__immP0_rule,
  /*  511 */  _CmpP__DecodeN_iRegN__immP0_rule,
  /*  512 */  rFlagsReg_rule,
  /*  513 */  _CmpI_iRegI_iRegI_rule,
  /*  514 */  _CmpI_iRegI_iRegI_rule,
  /*  515 */  _CmpU_iRegI_iRegI_rule,
  /*  516 */  _CmpU_iRegI_iRegI_rule,
  /*  517 */  _CmpL_iRegL_iRegL_rule,
  /*  518 */  _CmpL_iRegL_iRegL_rule,
  /*  519 */  _CmpUL_iRegL_iRegL_rule,
  /*  520 */  _CmpUL_iRegL_iRegL_rule,
  /*  521 */  _CmpP_iRegP_iRegP_rule,
  /*  522 */  _CmpP_iRegP_iRegP_rule,
  /*  523 */  _CmpN_iRegN_iRegN_rule,
  /*  524 */  _CmpN_iRegN_iRegN_rule,
  /*  525 */  _CmpF_fRegF_fRegF_rule,
  /*  526 */  _CmpF_fRegF_fRegF_rule,
  /*  527 */  _CmpD_fRegD_fRegD_rule,
  /*  528 */  _CmpD_fRegD_fRegD_rule,
  /*  529 */  _CmpI_iRegI_immI0_rule,
  /*  530 */  _CmpI_iRegI_immI0_rule,
  /*  531 */  _CmpU_iRegI_immI0_rule,
  /*  532 */  _CmpU_iRegI_immI0_rule,
  /*  533 */  _CmpU_iRegI_immI0_rule,
  /*  534 */  _CmpU_iRegI_immI0_rule,
  /*  535 */  _CmpL_iRegL_immL0_rule,
  /*  536 */  _CmpL_iRegL_immL0_rule,
  /*  537 */  _CmpUL_iRegL_immL0_rule,
  /*  538 */  _CmpUL_iRegL_immL0_rule,
  /*  539 */  _CmpUL_iRegL_immL0_rule,
  /*  540 */  _CmpUL_iRegL_immL0_rule,
  /*  541 */  _CmpP_iRegP_immP0_rule,
  /*  542 */  _CmpP_iRegP_immP0_rule,
  /*  543 */  _CmpN_iRegN_immN0_rule,
  /*  544 */  _CmpN_iRegN_immN0_rule,
  /*  545 */  _CmpP__DecodeN_iRegN__immP0_rule,
  /*  546 */  _CmpP__DecodeN_iRegN__immP0_rule,
  /*  547 */  _Binary_iRegINoSp_iRegI_rule,
  /*  548 */  _Binary_iRegINoSp_iRegI_rule,
  /*  549 */  _Binary_iRegINoSp_iRegI_rule,
  /*  550 */  _Binary_iRegLNoSp_iRegL_rule,
  /*  551 */  _Binary_iRegLNoSp_iRegL_rule,
  /*  552 */  _Binary_iRegINoSp_iRegI_rule,
  /*  553 */  0,
  /*  554 */  0,
  /*  555 */  0,
  /*  556 */  0,
  /*  557 */  0,
  /*  558 */  iRegP_R10_rule,
  /*  559 */  _Binary_iRegP_R13_iRegI_R14_rule,
  /*  560 */  _Binary_iRegP_R13_iRegI_R14_rule,
  /*  561 */  _Binary_iRegP_R13_iRegI_R14_rule,
  /*  562 */  _Binary_iRegP_R13_iRegI_R14_rule,
  /*  563 */  _Binary_iRegP_R13_iRegI_R14_rule,
  /*  564 */  _Binary_iRegP_R13_iRegI_R14_rule,
  /*  565 */  _Binary_iRegP_R13_iRegI_R14_rule,
  /*  566 */  _Binary_iRegP_R13_immI_le_4_rule,
  /*  567 */  _Binary_iRegP_R13_immI_le_4_rule,
  /*  568 */  _Binary_iRegP_R13_immI_1_rule,
  /*  569 */  iRegI_R13_rule,
  /*  570 */  iRegI_R13_rule,
  /*  571 */  iRegP_R28_rule,
  /*  572 */  iRegP_R28_rule,
  /*  573 */  iRegI_R14_rule,
  /*  574 */  iRegI_R14_rule,
  /*  575 */  iRegP_R12_rule,
  /*  576 */  iRegP_R12_rule,
  /*  577 */  0,
  /*  578 */  inline_cache_RegP_rule,
  /*  579 */  iRegP_R10_rule,
  /*  580 */  0,
  /*  581 */  0,
  /*  582 */  0,
  /*  583 */  0,
  /*  584 */  0,
  /*  585 */  vReg_rule,
  /*  586 */  0,
  /*  587 */  0,
  /*  588 */  0,
  /*  589 */  0,
  /*  590 */  vReg_rule,
  /*  591 */  vReg_rule,
  /*  592 */  vReg_rule,
  /*  593 */  pRegGov_rule,
  /*  594 */  vReg_rule,
  /*  595 */  vReg_rule,
  /*  596 */  vReg_rule,
  /*  597 */  vReg_rule,
  /*  598 */  vReg_rule,
  /*  599 */  vReg_rule,
  /*  600 */  vReg_rule,
  /*  601 */  vReg_rule,
  /*  602 */  vReg_rule,
  /*  603 */  vReg_rule,
  /*  604 */  vReg_rule,
  /*  605 */  vReg_rule,
  /*  606 */  vReg_rule,
  /*  607 */  vReg_rule,
  /*  608 */  _Binary_vReg_vReg_rule,
  /*  609 */  _Binary_vReg_vReg_rule,
  /*  610 */  _Binary__NegVF_vReg__vReg_rule,
  /*  611 */  _Binary_vReg__NegVF_vReg__rule,
  /*  612 */  _Binary__NegVD_vReg__vReg_rule,
  /*  613 */  _Binary_vReg__NegVD_vReg__rule,
  /*  614 */  _Binary__NegVF_vReg__vReg_rule,
  /*  615 */  _Binary_vReg__NegVF_vReg__rule,
  /*  616 */  _Binary__NegVD_vReg__vReg_rule,
  /*  617 */  _Binary_vReg__NegVD_vReg__rule,
  /*  618 */  _Binary_vReg_vReg_rule,
  /*  619 */  _Binary_vReg_vReg_rule,
  /*  620 */  _MulVB_vReg_vReg_rule,
  /*  621 */  vReg_rule,
  /*  622 */  _MulVS_vReg_vReg_rule,
  /*  623 */  vReg_rule,
  /*  624 */  _MulVI_vReg_vReg_rule,
  /*  625 */  vReg_rule,
  /*  626 */  _MulVL_vReg_vReg_rule,
  /*  627 */  vReg_rule,
  /*  628 */  _MulVB_vReg_vReg_rule,
  /*  629 */  _MulVS_vReg_vReg_rule,
  /*  630 */  _MulVI_vReg_vReg_rule,
  /*  631 */  _MulVL_vReg_vReg_rule,
  /*  632 */  vReg_rule,
  /*  633 */  vReg_rule,
  /*  634 */  vReg_rule,
  /*  635 */  vReg_rule,
  /*  636 */  vReg_rule,
  /*  637 */  vReg_rule,
  /*  638 */  vReg_rule,
  /*  639 */  vReg_rule,
  /*  640 */  vReg_rule,
  /*  641 */  vReg_rule,
  /*  642 */  vReg_rule,
  /*  643 */  vReg_rule,
  /*  644 */  vReg_rule,
  /*  645 */  vReg_rule,
  /*  646 */  vReg_rule,
  /*  647 */  vReg_rule,
  /*  648 */  vReg_rule,
  /*  649 */  vReg_rule,
  /*  650 */  vReg_rule,
  /*  651 */  vReg_rule,
  /*  652 */  vReg_rule,
  /*  653 */  vReg_rule,
  /*  654 */  vReg_rule,
  /*  655 */  vReg_rule,
  /*  656 */  immI_rule,
  /*  657 */  vReg_rule,
  /*  658 */  vReg_rule,
  /*  659 */  vReg_rule,
  /*  660 */  vReg_rule,
  /*  661 */  vReg_rule,
  /*  662 */  vReg_rule,
  /*  663 */  vReg_rule,
  /*  664 */  vReg_rule,
  /*  665 */  vReg_rule,
  /*  666 */  vReg_rule,
  /*  667 */  vReg_rule,
  /*  668 */  vReg_rule,
  /*  669 */  _RShiftCntV_immI__rule,
  /*  670 */  _RShiftCntV_immI__rule,
  /*  671 */  _RShiftCntV_immI__rule,
  /*  672 */  _RShiftCntV_immI__rule,
  /*  673 */  _RShiftCntV_immI__rule,
  /*  674 */  _RShiftCntV_immI__rule,
  /*  675 */  _RShiftCntV_immI__rule,
  /*  676 */  _RShiftCntV_immI__rule,
  /*  677 */  _LShiftCntV_immI__rule,
  /*  678 */  _LShiftCntV_immI__rule,
  /*  679 */  _LShiftCntV_immI__rule,
  /*  680 */  _LShiftCntV_immI__rule,
  /*  681 */  vReg_rule,
  /*  682 */  vReg_rule,
  /*  683 */  vReg_rule,
  /*  684 */  vReg_rule,
  /*  685 */  vReg_rule,
  /*  686 */  vReg_rule,
  /*  687 */  iRegI_R14_rule,
  /*  688 */  iRegI_R14_rule,
  /*  689 */  iRegP_R12_rule,
  /*  690 */  iRegP_R12_rule,
  /*  691 */  _Binary_iRegP_R13_iRegI_R14_rule,
  /*  692 */  _Binary_iRegP_R13_iRegI_R14_rule,
  /*  693 */  _Binary_iRegP_R13_iRegI_R14_rule,
  /*  694 */  _Binary_iRegP_R13_iRegI_R14_rule,
  /*  695 */  _Binary_iRegP_R11_iRegI_R12_rule,
  /*  696 */  _Binary_iRegP_R11_iRegI_R13_rule,
  /*  697 */  _Binary_iRegP_R11_iRegI_R13_rule,
  /*  698 */  iRegI_R12_rule,
  /*  699 */  iRegI_R13_rule,
  /*  700 */  iRegI_R13_rule,
  /*  701 */  iRegP_R28_rule,
  /*  702 */  immI_rule,
  /*  703 */  immI_rule,
  /*  704 */  iRegI_rule,
  /*  705 */  iRegI_rule,
  /*  706 */  iRegI_rule,
  /*  707 */  iRegI_rule,
  /*  708 */  0,
  /*  709 */  immI_24_rule,
  /*  710 */  immI_16_rule,
  /*  711 */  immI_16bits_rule,
  /*  712 */  immL_32bits_rule,
  /*  713 */  0,
  /*  714 */  0,
  /*  715 */  0,
  /*  716 */  0,
  /*  717 */  _LShiftL_iRegL_immIScale_rule,
  /*  718 */  _LShiftL__ConvI2L_iRegI__immIScale_rule,
  /*  719 */  _LShiftL_iRegL_immIScale_rule,
  /*  720 */  iRegL_rule,
  /*  721 */  _LShiftL__ConvI2L_iRegI__immIScale_rule,
  /*  722 */  iRegL_rule,
  /*  723 */  iRegI_rule,
  /*  724 */  iRegI_rule,
  /*  725 */  _XorI_iRegI_immI_M1_rule,
  /*  726 */  iRegI_rule,
  /*  727 */  _XorL_iRegL_immL_M1_rule,
  /*  728 */  iRegL_rule,
  /*  729 */  _XorI_iRegI_immI_M1_rule,
  /*  730 */  iRegI_rule,
  /*  731 */  _XorL_iRegL_immL_M1_rule,
  /*  732 */  iRegL_rule,
  /*  733 */  _Binary_iRegP_iRegP_rule,
  /*  734 */  _Binary_iRegN_iRegN_rule,
  /*  735 */  _Binary_iRegP_iRegP_rule,
  /*  736 */  _Binary_iRegN_iRegN_rule,
  /*  737 */  _Binary_iRegN_iRegN_rule,
  /*  738 */  _Binary_iRegP_iRegP_rule,
  /*  739 */  _Binary_iRegN_iRegN_rule,
  /*  740 */  _Binary_iRegN_iRegN_rule,
  /*  741 */  _Binary_iRegP_iRegP_rule,
  /*  742 */  _Binary_iRegP_iRegP_rule,
  /*  743 */  _Binary_iRegN_iRegN_rule,
  /*  744 */  _Binary_iRegP_iRegP_rule,
  /*  745 */  0,
  /*  746 */  _Binary_iRegP_iRegP_rule,
  /*  747 */  _Binary_iRegP_iRegP_rule,
  /*  748 */  _Binary_iRegP_iRegP_rule,
  /*  749 */  _Binary_iRegP_iRegP_rule,
  /*  750 */  _Binary_iRegP_iRegP_rule,
  /*  751 */  _Binary_iRegP_iRegP_rule,
  /*  752 */  iRegP_rule,
  /*  753 */  iRegP_rule,
  // last instruction
  0 // no trailing comma
};

const char        *ruleName[] = {
  /*    0 */  "UNIVERSE",
  /*    1 */  "LABEL",
  /*    2 */  "SREGI",
  /*    3 */  "SREGP",
  /*    4 */  "SREGF",
  /*    5 */  "SREGD",
  /*    6 */  "SREGL",
  /*    7 */  "METHOD",
  /*    8 */  "IMMI",
  /*    9 */  "IMMI0",
  /*   10 */  "IMMI_1",
  /*   11 */  "IMMI_M1",
  /*   12 */  "UIMMI6_GE32",
  /*   13 */  "IMMI_LE_4",
  /*   14 */  "IMMI_16",
  /*   15 */  "IMMI_24",
  /*   16 */  "IMMI_31",
  /*   17 */  "IMMI_63",
  /*   18 */  "IMMIADD",
  /*   19 */  "IMMISUB",
  /*   20 */  "IMMI5",
  /*   21 */  "IMML5",
  /*   22 */  "IMML",
  /*   23 */  "IMML0",
  /*   24 */  "IMMP",
  /*   25 */  "IMMP0",
  /*   26 */  "IMMP_1",
  /*   27 */  "IMMBYTEMAPBASE",
  /*   28 */  "IMMI_16BITS",
  /*   29 */  "IMML_32BITS",
  /*   30 */  "IMML_M1",
  /*   31 */  "IMML_PC_OFF",
  /*   32 */  "IMMLADD",
  /*   33 */  "IMMLSUB",
  /*   34 */  "IMMN",
  /*   35 */  "IMMN0",
  /*   36 */  "IMMNKLASS",
  /*   37 */  "IMMD",
  /*   38 */  "IMMD0",
  /*   39 */  "IMMF",
  /*   40 */  "IMMF0",
  /*   41 */  "IMMIOFFSET",
  /*   42 */  "IMMLOFFSET",
  /*   43 */  "IMMISCALE",
  /*   44 */  "IREGI",
  /*   45 */  "IREGINOSP",
  /*   46 */  "IREGI_R10",
  /*   47 */  "IREGI_R12",
  /*   48 */  "IREGI_R13",
  /*   49 */  "IREGI_R14",
  /*   50 */  "IREGL",
  /*   51 */  "IREGLNOSP",
  /*   52 */  "IREGL_R28",
  /*   53 */  "IREGL_R29",
  /*   54 */  "IREGL_R30",
  /*   55 */  "IREGP",
  /*   56 */  "IREGPNOSP",
  /*   57 */  "IREGP_R10",
  /*   58 */  "IREGP_R11",
  /*   59 */  "IREGP_R12",
  /*   60 */  "IREGP_R13",
  /*   61 */  "IREGP_R14",
  /*   62 */  "IREGP_R15",
  /*   63 */  "IREGP_R16",
  /*   64 */  "IREGP_R28",
  /*   65 */  "IREGP_R30",
  /*   66 */  "IREGP_R31",
  /*   67 */  "IREGN",
  /*   68 */  "IREGNNOSP",
  /*   69 */  "IREGIHEAPBASE",
  /*   70 */  "IREGL_R10",
  /*   71 */  "FREGF",
  /*   72 */  "FREGD",
  /*   73 */  "VREG",
  /*   74 */  "VREG_V1",
  /*   75 */  "VREG_V2",
  /*   76 */  "VREG_V3",
  /*   77 */  "VREG_V4",
  /*   78 */  "VREG_V5",
  /*   79 */  "JAVATHREAD_REGP",
  /*   80 */  "INDIRECT",
  /*   81 */  "INDOFFI",
  /*   82 */  "INDOFFL",
  /*   83 */  "INDIRECTN",
  /*   84 */  "INDOFFIN",
  /*   85 */  "INDOFFLN",
  /*   86 */  "THREAD_ANCHOR_PC",
  /*   87 */  "STACKSLOTI",
  /*   88 */  "STACKSLOTF",
  /*   89 */  "STACKSLOTD",
  /*   90 */  "STACKSLOTL",
  /*   91 */  "IREGL2I",
  /*   92 */  "CMPOP",
  /*   93 */  "CMPOPU",
  /*   94 */  "CMPOPEQNE",
  /*   95 */  "CMPOPULTGE",
  /*   96 */  "CMPOPUEQNELEGT",
  /*   97 */  "RFLAGSREG",
  /*   98 */  "INLINE_CACHE_REGP",
  /*   99 */  "PREGGOV",
  // last operand
  /*  100 */  "MEMORY",
  /*  101 */  "IREGIORL2I",
  /*  102 */  "IREGIORL",
  /*  103 */  "IREGNORP",
  /*  104 */  "IREGILNP",
  /*  105 */  "IREGILNPNOSP",
  /*  106 */  "IMMIORL",
  /*  107 */  "VMEMA",
  // last operand class
  /*  108 */  "_DecodeN_iRegN_",
  /*  109 */  "_LoadB_memory_",
  /*  110 */  "_LoadUB_memory_",
  /*  111 */  "_LoadS_memory_",
  /*  112 */  "_LoadUS_memory_",
  /*  113 */  "_LoadI_memory_",
  /*  114 */  "_ConvI2L__LoadI_memory__",
  /*  115 */  "_Binary_iRegI_R12_iRegI_R13",
  /*  116 */  "_Binary_iRegI_iRegI",
  /*  117 */  "_Binary_iRegL_iRegL",
  /*  118 */  "_Binary_iRegP_iRegP",
  /*  119 */  "_Binary_iRegN_iRegN",
  /*  120 */  "_ConvL2I_iRegL_",
  /*  121 */  "_ConvI2L_iRegI_",
  /*  122 */  "_RShiftI_iRegIorL2I_immI_31",
  /*  123 */  "_RShiftL_iRegL_immI_63",
  /*  124 */  "_CastP2X_iRegP_",
  /*  125 */  "_Binary_fRegF_fRegF",
  /*  126 */  "_Binary_fRegD_fRegD",
  /*  127 */  "_NegF_fRegF_",
  /*  128 */  "_NegD_fRegD_",
  /*  129 */  "_Binary__NegF_fRegF__fRegF",
  /*  130 */  "_Binary_fRegF__NegF_fRegF_",
  /*  131 */  "_Binary__NegD_fRegD__fRegD",
  /*  132 */  "_Binary_fRegD__NegD_fRegD_",
  /*  133 */  "_ConvF2D_fRegF_",
  /*  134 */  "_SqrtD__ConvF2D_fRegF__",
  /*  135 */  "_ConvI2L_iRegIorL2I_",
  /*  136 */  "_CastP2X__DecodeN_iRegN__",
  /*  137 */  "_CmpI_iRegI_iRegI",
  /*  138 */  "_CmpU_iRegI_iRegI",
  /*  139 */  "_CmpL_iRegL_iRegL",
  /*  140 */  "_CmpUL_iRegL_iRegL",
  /*  141 */  "_CmpP_iRegP_iRegP",
  /*  142 */  "_CmpN_iRegN_iRegN",
  /*  143 */  "_CmpF_fRegF_fRegF",
  /*  144 */  "_CmpD_fRegD_fRegD",
  /*  145 */  "_CmpI_iRegI_immI0",
  /*  146 */  "_CmpU_iRegI_immI0",
  /*  147 */  "_CmpL_iRegL_immL0",
  /*  148 */  "_CmpUL_iRegL_immL0",
  /*  149 */  "_CmpP_iRegP_immP0",
  /*  150 */  "_CmpN_iRegN_immN0",
  /*  151 */  "_CmpP__DecodeN_iRegN__immP0",
  /*  152 */  "_Binary_cmpOp__CmpI_iRegI_iRegI",
  /*  153 */  "_Binary_iRegINoSp_iRegI",
  /*  154 */  "_Binary_cmpOpU__CmpU_iRegI_iRegI",
  /*  155 */  "_Binary_cmpOp__CmpL_iRegL_iRegL",
  /*  156 */  "_Binary_iRegLNoSp_iRegL",
  /*  157 */  "_Binary_cmpOpU__CmpUL_iRegL_iRegL",
  /*  158 */  "_PartialSubtypeCheck_iRegP_R14_iRegP_R10",
  /*  159 */  "_Binary_iRegP_R11_iRegI_R12",
  /*  160 */  "_Binary_iRegP_R13_iRegI_R14",
  /*  161 */  "_Binary_iRegP_R13_immI_le_4",
  /*  162 */  "_Binary_iRegP_R13_immI_1",
  /*  163 */  "_Binary_iRegP_R11_iRegP_R13",
  /*  164 */  "_Binary_vReg_vReg",
  /*  165 */  "_NegVF_vReg_",
  /*  166 */  "_Binary__NegVF_vReg__vReg",
  /*  167 */  "_Binary_vReg__NegVF_vReg_",
  /*  168 */  "_NegVD_vReg_",
  /*  169 */  "_Binary__NegVD_vReg__vReg",
  /*  170 */  "_Binary_vReg__NegVD_vReg_",
  /*  171 */  "_MulVB_vReg_vReg",
  /*  172 */  "_MulVS_vReg_vReg",
  /*  173 */  "_MulVI_vReg_vReg",
  /*  174 */  "_MulVL_vReg_vReg",
  /*  175 */  "_RShiftCntV_immI_",
  /*  176 */  "_LShiftCntV_immI_",
  /*  177 */  "_Binary_iRegP_R11_iRegI_R13",
  /*  178 */  "_LShiftI_iRegIorL2I_immI_24",
  /*  179 */  "_LShiftI_iRegIorL2I_immI_16",
  /*  180 */  "_LShiftL_iRegL_immIScale",
  /*  181 */  "_LShiftL__ConvI2L_iRegI__immIScale",
  /*  182 */  "_XorI_iRegI_immI_M1",
  /*  183 */  "_XorL_iRegL_immL_M1",
  // last internally defined operand
  /*  184 */  "loadConI",
  /*  185 */  "loadConL",
  /*  186 */  "loadConP",
  /*  187 */  "loadConP0",
  /*  188 */  "loadConP1",
  /*  189 */  "loadByteMapBase",
  /*  190 */  "loadConN",
  /*  191 */  "loadConN0",
  /*  192 */  "loadConNKlass",
  /*  193 */  "loadConF",
  /*  194 */  "loadConF0",
  /*  195 */  "loadConD",
  /*  196 */  "loadConD0",
  /*  197 */  "isIniniteF_reg_reg",
  /*  198 */  "isInfiniteD_reg_reg",
  /*  199 */  "isFiniteF_reg_reg",
  /*  200 */  "isFiniteD_reg_reg",
  /*  201 */  "negF_reg_reg",
  /*  202 */  "negD_reg_reg",
  /*  203 */  "absI_reg",
  /*  204 */  "absL_reg",
  /*  205 */  "absF_reg",
  /*  206 */  "absD_reg",
  /*  207 */  "castX2P",
  /*  208 */  "castP2X",
  /*  209 */  "castPP",
  /*  210 */  "castLL",
  /*  211 */  "castII",
  /*  212 */  "checkCastPP",
  /*  213 */  "castFF",
  /*  214 */  "castDD",
  /*  215 */  "castVV",
  /*  216 */  "convI2Bool",
  /*  217 */  "convP2Bool",
  /*  218 */  "MoveF2I_stack_reg",
  /*  219 */  "MoveI2F_stack_reg",
  /*  220 */  "MoveD2L_stack_reg",
  /*  221 */  "MoveL2D_stack_reg",
  /*  222 */  "MoveF2I_reg_reg",
  /*  223 */  "MoveI2F_reg_reg",
  /*  224 */  "MoveD2L_reg_reg",
  /*  225 */  "MoveL2D_reg_reg",
  /*  226 */  "partialSubtypeCheckVsZero",
  /*  227 */  "tlsLoadP",
  /*  228 */  "cmpFastLock",
  /*  229 */  "cmpFastUnlock",
  /*  230 */  "vabsF",
  /*  231 */  "vabsD",
  /*  232 */  "vnegI",
  /*  233 */  "vnegL",
  /*  234 */  "vnegF",
  /*  235 */  "vnegD",
  /*  236 */  "replicateB",
  /*  237 */  "replicateS",
  /*  238 */  "replicateI",
  /*  239 */  "replicateL",
  /*  240 */  "replicateB_imm5",
  /*  241 */  "replicateS_imm5",
  /*  242 */  "replicateI_imm5",
  /*  243 */  "replicateL_imm5",
  /*  244 */  "replicateF",
  /*  245 */  "replicateD",
  /*  246 */  "vshiftcntB",
  /*  247 */  "vshiftcntB_0",
  /*  248 */  "vshiftcntS",
  /*  249 */  "vshiftcntS_0",
  /*  250 */  "vshiftcntI",
  /*  251 */  "vshiftcntI_0",
  /*  252 */  "vshiftcntL",
  /*  253 */  "vshiftcntL_0",
  /*  254 */  "vsqrtF",
  /*  255 */  "vsqrtD",
  /*  256 */  "countLeadingZerosI_b",
  /*  257 */  "countLeadingZerosL_b",
  /*  258 */  "countTrailingZerosI_b",
  /*  259 */  "countTrailingZerosL_b",
  /*  260 */  "popCountI_b",
  /*  261 */  "popCountL_b",
  /*  262 */  "absI_reg_b",
  /*  263 */  "absL_reg_b",
  /*  264 */  "loadB",
  /*  265 */  "loadB2L",
  /*  266 */  "loadUB",
  /*  267 */  "loadUB2L",
  /*  268 */  "loadS",
  /*  269 */  "loadS2L",
  /*  270 */  "loadUS",
  /*  271 */  "loadUS2L",
  /*  272 */  "loadI",
  /*  273 */  "loadI2L",
  /*  274 */  "loadUI2L",
  /*  275 */  "loadL",
  /*  276 */  "loadRange",
  /*  277 */  "loadP",
  /*  278 */  "loadN",
  /*  279 */  "loadKlass",
  /*  280 */  "loadNKlass",
  /*  281 */  "loadF",
  /*  282 */  "loadD",
  /*  283 */  "storeimmCM0",
  /*  284 */  "storeimmCM0_ordered",
  /*  285 */  "storeB",
  /*  286 */  "storeimmB0",
  /*  287 */  "storeC",
  /*  288 */  "storeimmC0",
  /*  289 */  "storeI",
  /*  290 */  "storeimmI0",
  /*  291 */  "storeL",
  /*  292 */  "storeimmL0",
  /*  293 */  "storeP",
  /*  294 */  "storeimmP0",
  /*  295 */  "storeN",
  /*  296 */  "storeImmN0",
  /*  297 */  "storeF",
  /*  298 */  "storeD",
  /*  299 */  "storeNKlass",
  /*  300 */  "compareAndSwapB",
  /*  301 */  "compareAndSwapS",
  /*  302 */  "compareAndSwapI",
  /*  303 */  "compareAndSwapL",
  /*  304 */  "compareAndSwapP",
  /*  305 */  "compareAndSwapN",
  /*  306 */  "compareAndSwapBAcq",
  /*  307 */  "compareAndSwapSAcq",
  /*  308 */  "compareAndSwapIAcq",
  /*  309 */  "compareAndSwapLAcq",
  /*  310 */  "compareAndSwapPAcq",
  /*  311 */  "compareAndSwapNAcq",
  /*  312 */  "compareAndExchangeB",
  /*  313 */  "compareAndExchangeS",
  /*  314 */  "compareAndExchangeI",
  /*  315 */  "compareAndExchangeL",
  /*  316 */  "compareAndExchangeN",
  /*  317 */  "compareAndExchangeP",
  /*  318 */  "compareAndExchangeBAcq",
  /*  319 */  "compareAndExchangeSAcq",
  /*  320 */  "compareAndExchangeIAcq",
  /*  321 */  "compareAndExchangeLAcq",
  /*  322 */  "compareAndExchangeNAcq",
  /*  323 */  "compareAndExchangePAcq",
  /*  324 */  "weakCompareAndSwapB",
  /*  325 */  "weakCompareAndSwapS",
  /*  326 */  "weakCompareAndSwapI",
  /*  327 */  "weakCompareAndSwapL",
  /*  328 */  "weakCompareAndSwapN",
  /*  329 */  "weakCompareAndSwapP",
  /*  330 */  "weakCompareAndSwapBAcq",
  /*  331 */  "weakCompareAndSwapSAcq",
  /*  332 */  "weakCompareAndSwapIAcq",
  /*  333 */  "weakCompareAndSwapLAcq",
  /*  334 */  "weakCompareAndSwapNAcq",
  /*  335 */  "weakCompareAndSwapPAcq",
  /*  336 */  "get_and_setI",
  /*  337 */  "get_and_setL",
  /*  338 */  "get_and_setN",
  /*  339 */  "get_and_setP",
  /*  340 */  "get_and_setIAcq",
  /*  341 */  "get_and_setLAcq",
  /*  342 */  "get_and_setNAcq",
  /*  343 */  "get_and_setPAcq",
  /*  344 */  "get_and_addL",
  /*  345 */  "get_and_addL_no_res",
  /*  346 */  "get_and_addLi",
  /*  347 */  "get_and_addLi_no_res",
  /*  348 */  "get_and_addI",
  /*  349 */  "get_and_addI_no_res",
  /*  350 */  "get_and_addIi",
  /*  351 */  "get_and_addIi_no_res",
  /*  352 */  "get_and_addLAcq",
  /*  353 */  "get_and_addL_no_resAcq",
  /*  354 */  "get_and_addLiAcq",
  /*  355 */  "get_and_addLi_no_resAcq",
  /*  356 */  "get_and_addIAcq",
  /*  357 */  "get_and_addI_no_resAcq",
  /*  358 */  "get_and_addIiAcq",
  /*  359 */  "get_and_addIi_no_resAcq",
  /*  360 */  "addI_reg_reg",
  /*  361 */  "addI_reg_imm",
  /*  362 */  "addI_reg_imm_l2i",
  /*  363 */  "addP_reg_reg",
  /*  364 */  "lShiftL_regI_immGE32",
  /*  365 */  "addP_reg_imm",
  /*  366 */  "addL_reg_reg",
  /*  367 */  "addL_reg_imm",
  /*  368 */  "subI_reg_reg",
  /*  369 */  "subI_reg_imm",
  /*  370 */  "subL_reg_reg",
  /*  371 */  "subL_reg_imm",
  /*  372 */  "negI_reg",
  /*  373 */  "negL_reg",
  /*  374 */  "mulI",
  /*  375 */  "mulL",
  /*  376 */  "mulHiL_rReg",
  /*  377 */  "divI",
  /*  378 */  "signExtract",
  /*  379 */  "divL",
  /*  380 */  "signExtractL",
  /*  381 */  "modI",
  /*  382 */  "modL",
  /*  383 */  "lShiftI_reg_reg",
  /*  384 */  "lShiftI_reg_imm",
  /*  385 */  "urShiftI_reg_reg",
  /*  386 */  "urShiftI_reg_imm",
  /*  387 */  "rShiftI_reg_reg",
  /*  388 */  "rShiftI_reg_imm",
  /*  389 */  "lShiftL_reg_reg",
  /*  390 */  "lShiftL_reg_imm",
  /*  391 */  "urShiftL_reg_reg",
  /*  392 */  "urShiftL_reg_imm",
  /*  393 */  "urShiftP_reg_imm",
  /*  394 */  "rShiftL_reg_reg",
  /*  395 */  "rShiftL_reg_imm",
  /*  396 */  "regI_not_reg",
  /*  397 */  "regL_not_reg",
  /*  398 */  "addF_reg_reg",
  /*  399 */  "addD_reg_reg",
  /*  400 */  "subF_reg_reg",
  /*  401 */  "subD_reg_reg",
  /*  402 */  "mulF_reg_reg",
  /*  403 */  "mulD_reg_reg",
  /*  404 */  "maddF_reg_reg",
  /*  405 */  "maddD_reg_reg",
  /*  406 */  "msubF_reg_reg",
  /*  407 */  "msubD_reg_reg",
  /*  408 */  "nmsubF_reg_reg",
  /*  409 */  "nmsubF_reg_reg_0",
  /*  410 */  "nmsubD_reg_reg",
  /*  411 */  "nmsubD_reg_reg_0",
  /*  412 */  "nmaddF_reg_reg",
  /*  413 */  "nmaddF_reg_reg_0",
  /*  414 */  "nmaddD_reg_reg",
  /*  415 */  "nmaddD_reg_reg_0",
  /*  416 */  "maxF_reg_reg",
  /*  417 */  "minF_reg_reg",
  /*  418 */  "maxD_reg_reg",
  /*  419 */  "minD_reg_reg",
  /*  420 */  "divF_reg_reg",
  /*  421 */  "divD_reg_reg",
  /*  422 */  "sqrtF_reg",
  /*  423 */  "sqrtD_reg",
  /*  424 */  "andI_reg_reg",
  /*  425 */  "andI_reg_imm",
  /*  426 */  "orI_reg_reg",
  /*  427 */  "orI_reg_imm",
  /*  428 */  "xorI_reg_reg",
  /*  429 */  "xorI_reg_imm",
  /*  430 */  "andL_reg_reg",
  /*  431 */  "andL_reg_imm",
  /*  432 */  "orL_reg_reg",
  /*  433 */  "orL_reg_imm",
  /*  434 */  "xorL_reg_reg",
  /*  435 */  "xorL_reg_imm",
  /*  436 */  "bytes_reverse_int",
  /*  437 */  "bytes_reverse_long",
  /*  438 */  "bytes_reverse_unsigned_short",
  /*  439 */  "bytes_reverse_short",
  /*  440 */  "load_fence",
  /*  441 */  "membar_acquire",
  /*  442 */  "membar_acquire_lock",
  /*  443 */  "store_fence",
  /*  444 */  "membar_release",
  /*  445 */  "membar_storestore",
  /*  446 */  "membar_storestore_0",
  /*  447 */  "membar_release_lock",
  /*  448 */  "membar_volatile",
  /*  449 */  "convI2L_reg_reg",
  /*  450 */  "convL2I_reg",
  /*  451 */  "convI2UL_reg_reg",
  /*  452 */  "convF2D_reg",
  /*  453 */  "convD2F_reg",
  /*  454 */  "convF2I_reg_reg",
  /*  455 */  "convI2F_reg_reg",
  /*  456 */  "convF2L_reg_reg",
  /*  457 */  "convL2F_reg_reg",
  /*  458 */  "convD2I_reg_reg",
  /*  459 */  "convI2D_reg_reg",
  /*  460 */  "convD2L_reg_reg",
  /*  461 */  "convL2D_reg_reg",
  /*  462 */  "convP2I",
  /*  463 */  "convN2I",
  /*  464 */  "encodeHeapOop",
  /*  465 */  "decodeHeapOop",
  /*  466 */  "decodeHeapOop_not_null",
  /*  467 */  "encodeKlass_not_null",
  /*  468 */  "decodeKlass_not_null",
  /*  469 */  "MoveF2I_reg_stack",
  /*  470 */  "MoveI2F_reg_stack",
  /*  471 */  "MoveD2L_reg_stack",
  /*  472 */  "MoveL2D_reg_stack",
  /*  473 */  "cmpF3_reg_reg",
  /*  474 */  "cmpD3_reg_reg",
  /*  475 */  "cmpL3_reg_reg",
  /*  476 */  "cmpLTMask_reg_reg",
  /*  477 */  "cmpLTMask_reg_zero",
  /*  478 */  "minI_rReg",
  /*  479 */  "maxI_rReg",
  /*  480 */  "branch",
  /*  481 */  "cmpFlag_branch",
  /*  482 */  "cmpI_branch",
  /*  483 */  "cmpI_loop",
  /*  484 */  "cmpU_branch",
  /*  485 */  "cmpU_loop",
  /*  486 */  "cmpL_branch",
  /*  487 */  "cmpL_loop",
  /*  488 */  "cmpUL_branch",
  /*  489 */  "cmpUL_loop",
  /*  490 */  "cmpP_branch",
  /*  491 */  "cmpP_loop",
  /*  492 */  "cmpN_branch",
  /*  493 */  "cmpN_loop",
  /*  494 */  "cmpF_branch",
  /*  495 */  "cmpF_loop",
  /*  496 */  "cmpD_branch",
  /*  497 */  "cmpD_loop",
  /*  498 */  "cmpI_reg_imm0_branch",
  /*  499 */  "cmpI_reg_imm0_loop",
  /*  500 */  "cmpUEqNeLeGt_reg_imm0_branch",
  /*  501 */  "cmpUEqNeLeGt_reg_imm0_loop",
  /*  502 */  "cmpL_reg_imm0_branch",
  /*  503 */  "cmpL_reg_imm0_loop",
  /*  504 */  "cmpULEqNeLeGt_reg_imm0_branch",
  /*  505 */  "cmpULEqNeLeGt_reg_imm0_loop",
  /*  506 */  "cmpP_imm0_branch",
  /*  507 */  "cmpP_imm0_loop",
  /*  508 */  "cmpN_imm0_branch",
  /*  509 */  "cmpN_imm0_loop",
  /*  510 */  "cmpP_narrowOop_imm0_branch",
  /*  511 */  "cmpP_narrowOop_imm0_loop",
  /*  512 */  "far_cmpFlag_branch",
  /*  513 */  "far_cmpI_branch",
  /*  514 */  "far_cmpI_loop",
  /*  515 */  "far_cmpU_branch",
  /*  516 */  "far_cmpU_loop",
  /*  517 */  "far_cmpL_branch",
  /*  518 */  "far_cmpLloop",
  /*  519 */  "far_cmpUL_branch",
  /*  520 */  "far_cmpUL_loop",
  /*  521 */  "far_cmpP_branch",
  /*  522 */  "far_cmpP_loop",
  /*  523 */  "far_cmpN_branch",
  /*  524 */  "far_cmpN_loop",
  /*  525 */  "far_cmpF_branch",
  /*  526 */  "far_cmpF_loop",
  /*  527 */  "far_cmpD_branch",
  /*  528 */  "far_cmpD_loop",
  /*  529 */  "far_cmpI_reg_imm0_branch",
  /*  530 */  "far_cmpI_reg_imm0_loop",
  /*  531 */  "far_cmpUEqNeLeGt_imm0_branch",
  /*  532 */  "far_cmpUEqNeLeGt_reg_imm0_loop",
  /*  533 */  "far_cmpULtGe_reg_imm0_branch",
  /*  534 */  "far_cmpULtGe_reg_imm0_loop",
  /*  535 */  "far_cmpL_reg_imm0_branch",
  /*  536 */  "far_cmpL_reg_imm0_loop",
  /*  537 */  "far_cmpULEqNeLeGt_reg_imm0_branch",
  /*  538 */  "far_cmpULEqNeLeGt_reg_imm0_loop",
  /*  539 */  "far_cmpULLtGe_reg_imm0_branch",
  /*  540 */  "far_cmpULLtGe_reg_imm0_loop",
  /*  541 */  "far_cmpP_imm0_branch",
  /*  542 */  "far_cmpP_imm0_loop",
  /*  543 */  "far_cmpN_imm0_branch",
  /*  544 */  "far_cmpN_imm0_loop",
  /*  545 */  "far_cmpP_narrowOop_imm0_branch",
  /*  546 */  "far_cmpP_narrowOop_imm0_loop",
  /*  547 */  "cmovI_cmpI",
  /*  548 */  "cmovI_cmpU",
  /*  549 */  "cmovI_cmpL",
  /*  550 */  "cmovL_cmpL",
  /*  551 */  "cmovL_cmpUL",
  /*  552 */  "cmovI_cmpUL",
  /*  553 */  "CallStaticJavaDirect",
  /*  554 */  "CallDynamicJavaDirect",
  /*  555 */  "CallRuntimeDirect",
  /*  556 */  "CallLeafDirect",
  /*  557 */  "CallLeafNoFPDirect",
  /*  558 */  "partialSubtypeCheck",
  /*  559 */  "string_compareU",
  /*  560 */  "string_compareL",
  /*  561 */  "string_compareUL",
  /*  562 */  "string_compareLU",
  /*  563 */  "string_indexofUU",
  /*  564 */  "string_indexofLL",
  /*  565 */  "string_indexofUL",
  /*  566 */  "string_indexof_conUU",
  /*  567 */  "string_indexof_conLL",
  /*  568 */  "string_indexof_conUL",
  /*  569 */  "stringU_indexof_char",
  /*  570 */  "stringL_indexof_char",
  /*  571 */  "clearArray_reg_reg",
  /*  572 */  "clearArray_imm_reg",
  /*  573 */  "string_equalsL",
  /*  574 */  "string_equalsU",
  /*  575 */  "array_equalsB",
  /*  576 */  "array_equalsC",
  /*  577 */  "safePoint",
  /*  578 */  "TailCalljmpInd",
  /*  579 */  "TailjmpInd",
  /*  580 */  "CreateException",
  /*  581 */  "RethrowException",
  /*  582 */  "Ret",
  /*  583 */  "ShouldNotReachHere",
  /*  584 */  "loadV",
  /*  585 */  "storeV",
  /*  586 */  "vabsB",
  /*  587 */  "vabsS",
  /*  588 */  "vabsI",
  /*  589 */  "vabsL",
  /*  590 */  "vaddB",
  /*  591 */  "vaddS",
  /*  592 */  "vaddI",
  /*  593 */  "vaddI_masked",
  /*  594 */  "vaddL",
  /*  595 */  "vaddF",
  /*  596 */  "vaddD",
  /*  597 */  "vand",
  /*  598 */  "vor",
  /*  599 */  "vxor",
  /*  600 */  "vdivF",
  /*  601 */  "vdivD",
  /*  602 */  "vmax",
  /*  603 */  "vmin",
  /*  604 */  "vmaxF",
  /*  605 */  "vmaxD",
  /*  606 */  "vminF",
  /*  607 */  "vminD",
  /*  608 */  "vfmlaF",
  /*  609 */  "vfmlaD",
  /*  610 */  "vfmlsF",
  /*  611 */  "vfmlsF_0",
  /*  612 */  "vfmlsD",
  /*  613 */  "vfmlsD_0",
  /*  614 */  "vfnmlaF",
  /*  615 */  "vfnmlaF_0",
  /*  616 */  "vfnmlaD",
  /*  617 */  "vfnmlaD_0",
  /*  618 */  "vfnmlsF",
  /*  619 */  "vfnmlsD",
  /*  620 */  "vmlaB",
  /*  621 */  "vmlaB_0",
  /*  622 */  "vmlaS",
  /*  623 */  "vmlaS_0",
  /*  624 */  "vmlaI",
  /*  625 */  "vmlaI_0",
  /*  626 */  "vmlaL",
  /*  627 */  "vmlaL_0",
  /*  628 */  "vmlsB",
  /*  629 */  "vmlsS",
  /*  630 */  "vmlsI",
  /*  631 */  "vmlsL",
  /*  632 */  "vmulB",
  /*  633 */  "vmulS",
  /*  634 */  "vmulI",
  /*  635 */  "vmulL",
  /*  636 */  "vmulF",
  /*  637 */  "vmulD",
  /*  638 */  "reduce_andI",
  /*  639 */  "reduce_andL",
  /*  640 */  "reduce_orI",
  /*  641 */  "reduce_orL",
  /*  642 */  "reduce_xorI",
  /*  643 */  "reduce_xorL",
  /*  644 */  "reduce_addI",
  /*  645 */  "reduce_addL",
  /*  646 */  "reduce_addF",
  /*  647 */  "reduce_addD",
  /*  648 */  "vreduce_maxI",
  /*  649 */  "vreduce_maxL",
  /*  650 */  "vreduce_minI",
  /*  651 */  "vreduce_minL",
  /*  652 */  "vreduce_maxF",
  /*  653 */  "vreduce_maxD",
  /*  654 */  "vreduce_minF",
  /*  655 */  "vreduce_minD",
  /*  656 */  "vroundD",
  /*  657 */  "vasrB",
  /*  658 */  "vasrS",
  /*  659 */  "vasrI",
  /*  660 */  "vasrL",
  /*  661 */  "vlslB",
  /*  662 */  "vlslS",
  /*  663 */  "vlslI",
  /*  664 */  "vlslL",
  /*  665 */  "vlsrB",
  /*  666 */  "vlsrS",
  /*  667 */  "vlsrI",
  /*  668 */  "vlsrL",
  /*  669 */  "vasrB_imm",
  /*  670 */  "vasrS_imm",
  /*  671 */  "vasrI_imm",
  /*  672 */  "vasrL_imm",
  /*  673 */  "vlsrB_imm",
  /*  674 */  "vlsrS_imm",
  /*  675 */  "vlsrI_imm",
  /*  676 */  "vlsrL_imm",
  /*  677 */  "vlslB_imm",
  /*  678 */  "vlslS_imm",
  /*  679 */  "vlslI_imm",
  /*  680 */  "vlslL_imm",
  /*  681 */  "vsubB",
  /*  682 */  "vsubS",
  /*  683 */  "vsubI",
  /*  684 */  "vsubL",
  /*  685 */  "vsubF",
  /*  686 */  "vsubD",
  /*  687 */  "vstring_equalsL",
  /*  688 */  "vstring_equalsU",
  /*  689 */  "varray_equalsB",
  /*  690 */  "varray_equalsC",
  /*  691 */  "vstring_compareU",
  /*  692 */  "vstring_compareL",
  /*  693 */  "vstring_compareUL",
  /*  694 */  "vstring_compareLU",
  /*  695 */  "vstring_inflate",
  /*  696 */  "vencode_iso_array",
  /*  697 */  "vstring_compress",
  /*  698 */  "vcount_positives",
  /*  699 */  "vstringU_indexof_char",
  /*  700 */  "vstringL_indexof_char",
  /*  701 */  "vclearArray_reg_reg",
  /*  702 */  "rorI_imm_b",
  /*  703 */  "rorL_imm_b",
  /*  704 */  "rorI_reg_b",
  /*  705 */  "rorL_reg_b",
  /*  706 */  "rolI_reg_b",
  /*  707 */  "rolL_reg_b",
  /*  708 */  "convP2I_b",
  /*  709 */  "convB2I_reg_reg_b",
  /*  710 */  "convI2S_reg_reg_b",
  /*  711 */  "convS2UI_reg_reg_b",
  /*  712 */  "convI2UL_reg_reg_b",
  /*  713 */  "bytes_reverse_int_b",
  /*  714 */  "bytes_reverse_long_b",
  /*  715 */  "bytes_reverse_unsigned_short_b",
  /*  716 */  "bytes_reverse_short_b",
  /*  717 */  "shaddP_reg_reg_b",
  /*  718 */  "shaddP_reg_reg_ext_b",
  /*  719 */  "shaddL_reg_reg_b",
  /*  720 */  "shaddL_reg_reg_b_0",
  /*  721 */  "shaddL_reg_reg_ext_b",
  /*  722 */  "shaddL_reg_reg_ext_b_0",
  /*  723 */  "minI_reg_b",
  /*  724 */  "maxI_reg_b",
  /*  725 */  "andnI_reg_reg_b",
  /*  726 */  "andnI_reg_reg_b_0",
  /*  727 */  "andnL_reg_reg_b",
  /*  728 */  "andnL_reg_reg_b_0",
  /*  729 */  "ornI_reg_reg_b",
  /*  730 */  "ornI_reg_reg_b_0",
  /*  731 */  "ornL_reg_reg_b",
  /*  732 */  "ornL_reg_reg_b_0",
  /*  733 */  "compareAndSwapP_shenandoah",
  /*  734 */  "compareAndSwapN_shenandoah",
  /*  735 */  "compareAndSwapPAcq_shenandoah",
  /*  736 */  "compareAndSwapNAcq_shenandoah",
  /*  737 */  "compareAndExchangeN_shenandoah",
  /*  738 */  "compareAndExchangeP_shenandoah",
  /*  739 */  "weakCompareAndSwapN_shenandoah",
  /*  740 */  "compareAndExchangeNAcq_shenandoah",
  /*  741 */  "compareAndExchangePAcq_shenandoah",
  /*  742 */  "weakCompareAndSwapP_shenandoah",
  /*  743 */  "weakCompareAndSwapNAcq_shenandoah",
  /*  744 */  "weakCompareAndSwapPAcq_shenandoah",
  /*  745 */  "zLoadP",
  /*  746 */  "zCompareAndSwapP",
  /*  747 */  "zCompareAndSwapP_0",
  /*  748 */  "zCompareAndSwapPAcq",
  /*  749 */  "zCompareAndSwapPAcq_0",
  /*  750 */  "zCompareAndExchangeP",
  /*  751 */  "zCompareAndExchangePAcq",
  /*  752 */  "zGetAndSetP",
  /*  753 */  "zGetAndSetPAcq",
  // last instruction
  "invalid rule name" // no trailing comma
};

const        bool  swallowed[] = {
  /*    0 */  false,
  /*    1 */  false,
  /*    2 */  false,
  /*    3 */  false,
  /*    4 */  false,
  /*    5 */  false,
  /*    6 */  false,
  /*    7 */  false,
  /*    8 */  true,
  /*    9 */  true,
  /*   10 */  true,
  /*   11 */  true,
  /*   12 */  true,
  /*   13 */  true,
  /*   14 */  true,
  /*   15 */  true,
  /*   16 */  true,
  /*   17 */  true,
  /*   18 */  true,
  /*   19 */  true,
  /*   20 */  true,
  /*   21 */  true,
  /*   22 */  true,
  /*   23 */  true,
  /*   24 */  true,
  /*   25 */  true,
  /*   26 */  true,
  /*   27 */  true,
  /*   28 */  true,
  /*   29 */  true,
  /*   30 */  true,
  /*   31 */  true,
  /*   32 */  true,
  /*   33 */  true,
  /*   34 */  true,
  /*   35 */  true,
  /*   36 */  true,
  /*   37 */  true,
  /*   38 */  true,
  /*   39 */  true,
  /*   40 */  true,
  /*   41 */  true,
  /*   42 */  true,
  /*   43 */  true,
  /*   44 */  false,
  /*   45 */  false,
  /*   46 */  false,
  /*   47 */  false,
  /*   48 */  false,
  /*   49 */  false,
  /*   50 */  false,
  /*   51 */  false,
  /*   52 */  false,
  /*   53 */  false,
  /*   54 */  false,
  /*   55 */  false,
  /*   56 */  false,
  /*   57 */  false,
  /*   58 */  false,
  /*   59 */  false,
  /*   60 */  false,
  /*   61 */  false,
  /*   62 */  false,
  /*   63 */  false,
  /*   64 */  false,
  /*   65 */  false,
  /*   66 */  false,
  /*   67 */  false,
  /*   68 */  false,
  /*   69 */  false,
  /*   70 */  false,
  /*   71 */  false,
  /*   72 */  false,
  /*   73 */  false,
  /*   74 */  false,
  /*   75 */  false,
  /*   76 */  false,
  /*   77 */  false,
  /*   78 */  false,
  /*   79 */  false,
  /*   80 */  false,
  /*   81 */  false,
  /*   82 */  false,
  /*   83 */  false,
  /*   84 */  false,
  /*   85 */  false,
  /*   86 */  false,
  /*   87 */  false,
  /*   88 */  false,
  /*   89 */  false,
  /*   90 */  false,
  /*   91 */  false,
  /*   92 */  true,
  /*   93 */  true,
  /*   94 */  true,
  /*   95 */  true,
  /*   96 */  true,
  /*   97 */  false,
  /*   98 */  false,
  /*   99 */  false,
  // last operand
  /*  100 */  false,
  /*  101 */  false,
  /*  102 */  false,
  /*  103 */  false,
  /*  104 */  false,
  /*  105 */  false,
  /*  106 */  false,
  /*  107 */  false,
  // last operand class
  /*  108 */  false,
  /*  109 */  false,
  /*  110 */  false,
  /*  111 */  false,
  /*  112 */  false,
  /*  113 */  false,
  /*  114 */  false,
  /*  115 */  false,
  /*  116 */  false,
  /*  117 */  false,
  /*  118 */  false,
  /*  119 */  false,
  /*  120 */  false,
  /*  121 */  false,
  /*  122 */  false,
  /*  123 */  false,
  /*  124 */  false,
  /*  125 */  false,
  /*  126 */  false,
  /*  127 */  false,
  /*  128 */  false,
  /*  129 */  false,
  /*  130 */  false,
  /*  131 */  false,
  /*  132 */  false,
  /*  133 */  false,
  /*  134 */  false,
  /*  135 */  false,
  /*  136 */  false,
  /*  137 */  false,
  /*  138 */  false,
  /*  139 */  false,
  /*  140 */  false,
  /*  141 */  false,
  /*  142 */  false,
  /*  143 */  false,
  /*  144 */  false,
  /*  145 */  false,
  /*  146 */  false,
  /*  147 */  false,
  /*  148 */  false,
  /*  149 */  false,
  /*  150 */  false,
  /*  151 */  false,
  /*  152 */  false,
  /*  153 */  false,
  /*  154 */  false,
  /*  155 */  false,
  /*  156 */  false,
  /*  157 */  false,
  /*  158 */  false,
  /*  159 */  false,
  /*  160 */  false,
  /*  161 */  false,
  /*  162 */  false,
  /*  163 */  false,
  /*  164 */  false,
  /*  165 */  false,
  /*  166 */  false,
  /*  167 */  false,
  /*  168 */  false,
  /*  169 */  false,
  /*  170 */  false,
  /*  171 */  false,
  /*  172 */  false,
  /*  173 */  false,
  /*  174 */  false,
  /*  175 */  false,
  /*  176 */  false,
  /*  177 */  false,
  /*  178 */  false,
  /*  179 */  false,
  /*  180 */  false,
  /*  181 */  false,
  /*  182 */  false,
  /*  183 */  false,
  // last internally defined operand
  /*  184 */  false,
  /*  185 */  false,
  /*  186 */  false,
  /*  187 */  false,
  /*  188 */  false,
  /*  189 */  false,
  /*  190 */  false,
  /*  191 */  false,
  /*  192 */  false,
  /*  193 */  false,
  /*  194 */  false,
  /*  195 */  false,
  /*  196 */  false,
  /*  197 */  false,
  /*  198 */  false,
  /*  199 */  false,
  /*  200 */  false,
  /*  201 */  false,
  /*  202 */  false,
  /*  203 */  false,
  /*  204 */  false,
  /*  205 */  false,
  /*  206 */  false,
  /*  207 */  false,
  /*  208 */  false,
  /*  209 */  false,
  /*  210 */  false,
  /*  211 */  false,
  /*  212 */  false,
  /*  213 */  false,
  /*  214 */  false,
  /*  215 */  false,
  /*  216 */  false,
  /*  217 */  false,
  /*  218 */  false,
  /*  219 */  false,
  /*  220 */  false,
  /*  221 */  false,
  /*  222 */  false,
  /*  223 */  false,
  /*  224 */  false,
  /*  225 */  false,
  /*  226 */  false,
  /*  227 */  false,
  /*  228 */  false,
  /*  229 */  false,
  /*  230 */  false,
  /*  231 */  false,
  /*  232 */  false,
  /*  233 */  false,
  /*  234 */  false,
  /*  235 */  false,
  /*  236 */  false,
  /*  237 */  false,
  /*  238 */  false,
  /*  239 */  false,
  /*  240 */  false,
  /*  241 */  false,
  /*  242 */  false,
  /*  243 */  false,
  /*  244 */  false,
  /*  245 */  false,
  /*  246 */  false,
  /*  247 */  false,
  /*  248 */  false,
  /*  249 */  false,
  /*  250 */  false,
  /*  251 */  false,
  /*  252 */  false,
  /*  253 */  false,
  /*  254 */  false,
  /*  255 */  false,
  /*  256 */  false,
  /*  257 */  false,
  /*  258 */  false,
  /*  259 */  false,
  /*  260 */  false,
  /*  261 */  false,
  /*  262 */  false,
  /*  263 */  false,
  /*  264 */  false,
  /*  265 */  false,
  /*  266 */  false,
  /*  267 */  false,
  /*  268 */  false,
  /*  269 */  false,
  /*  270 */  false,
  /*  271 */  false,
  /*  272 */  false,
  /*  273 */  false,
  /*  274 */  false,
  /*  275 */  false,
  /*  276 */  false,
  /*  277 */  false,
  /*  278 */  false,
  /*  279 */  false,
  /*  280 */  false,
  /*  281 */  false,
  /*  282 */  false,
  /*  283 */  false,
  /*  284 */  false,
  /*  285 */  false,
  /*  286 */  false,
  /*  287 */  false,
  /*  288 */  false,
  /*  289 */  false,
  /*  290 */  false,
  /*  291 */  false,
  /*  292 */  false,
  /*  293 */  false,
  /*  294 */  false,
  /*  295 */  false,
  /*  296 */  false,
  /*  297 */  false,
  /*  298 */  false,
  /*  299 */  false,
  /*  300 */  false,
  /*  301 */  false,
  /*  302 */  false,
  /*  303 */  false,
  /*  304 */  false,
  /*  305 */  false,
  /*  306 */  false,
  /*  307 */  false,
  /*  308 */  false,
  /*  309 */  false,
  /*  310 */  false,
  /*  311 */  false,
  /*  312 */  false,
  /*  313 */  false,
  /*  314 */  false,
  /*  315 */  false,
  /*  316 */  false,
  /*  317 */  false,
  /*  318 */  false,
  /*  319 */  false,
  /*  320 */  false,
  /*  321 */  false,
  /*  322 */  false,
  /*  323 */  false,
  /*  324 */  false,
  /*  325 */  false,
  /*  326 */  false,
  /*  327 */  false,
  /*  328 */  false,
  /*  329 */  false,
  /*  330 */  false,
  /*  331 */  false,
  /*  332 */  false,
  /*  333 */  false,
  /*  334 */  false,
  /*  335 */  false,
  /*  336 */  false,
  /*  337 */  false,
  /*  338 */  false,
  /*  339 */  false,
  /*  340 */  false,
  /*  341 */  false,
  /*  342 */  false,
  /*  343 */  false,
  /*  344 */  false,
  /*  345 */  false,
  /*  346 */  false,
  /*  347 */  false,
  /*  348 */  false,
  /*  349 */  false,
  /*  350 */  false,
  /*  351 */  false,
  /*  352 */  false,
  /*  353 */  false,
  /*  354 */  false,
  /*  355 */  false,
  /*  356 */  false,
  /*  357 */  false,
  /*  358 */  false,
  /*  359 */  false,
  /*  360 */  false,
  /*  361 */  false,
  /*  362 */  false,
  /*  363 */  false,
  /*  364 */  false,
  /*  365 */  false,
  /*  366 */  false,
  /*  367 */  false,
  /*  368 */  false,
  /*  369 */  false,
  /*  370 */  false,
  /*  371 */  false,
  /*  372 */  false,
  /*  373 */  false,
  /*  374 */  false,
  /*  375 */  false,
  /*  376 */  false,
  /*  377 */  false,
  /*  378 */  false,
  /*  379 */  false,
  /*  380 */  false,
  /*  381 */  false,
  /*  382 */  false,
  /*  383 */  false,
  /*  384 */  false,
  /*  385 */  false,
  /*  386 */  false,
  /*  387 */  false,
  /*  388 */  false,
  /*  389 */  false,
  /*  390 */  false,
  /*  391 */  false,
  /*  392 */  false,
  /*  393 */  false,
  /*  394 */  false,
  /*  395 */  false,
  /*  396 */  false,
  /*  397 */  false,
  /*  398 */  false,
  /*  399 */  false,
  /*  400 */  false,
  /*  401 */  false,
  /*  402 */  false,
  /*  403 */  false,
  /*  404 */  false,
  /*  405 */  false,
  /*  406 */  false,
  /*  407 */  false,
  /*  408 */  false,
  /*  409 */  false,
  /*  410 */  false,
  /*  411 */  false,
  /*  412 */  false,
  /*  413 */  false,
  /*  414 */  false,
  /*  415 */  false,
  /*  416 */  false,
  /*  417 */  false,
  /*  418 */  false,
  /*  419 */  false,
  /*  420 */  false,
  /*  421 */  false,
  /*  422 */  false,
  /*  423 */  false,
  /*  424 */  false,
  /*  425 */  false,
  /*  426 */  false,
  /*  427 */  false,
  /*  428 */  false,
  /*  429 */  false,
  /*  430 */  false,
  /*  431 */  false,
  /*  432 */  false,
  /*  433 */  false,
  /*  434 */  false,
  /*  435 */  false,
  /*  436 */  false,
  /*  437 */  false,
  /*  438 */  false,
  /*  439 */  false,
  /*  440 */  false,
  /*  441 */  false,
  /*  442 */  false,
  /*  443 */  false,
  /*  444 */  false,
  /*  445 */  false,
  /*  446 */  false,
  /*  447 */  false,
  /*  448 */  false,
  /*  449 */  false,
  /*  450 */  false,
  /*  451 */  false,
  /*  452 */  false,
  /*  453 */  false,
  /*  454 */  false,
  /*  455 */  false,
  /*  456 */  false,
  /*  457 */  false,
  /*  458 */  false,
  /*  459 */  false,
  /*  460 */  false,
  /*  461 */  false,
  /*  462 */  false,
  /*  463 */  false,
  /*  464 */  false,
  /*  465 */  false,
  /*  466 */  false,
  /*  467 */  false,
  /*  468 */  false,
  /*  469 */  false,
  /*  470 */  false,
  /*  471 */  false,
  /*  472 */  false,
  /*  473 */  false,
  /*  474 */  false,
  /*  475 */  false,
  /*  476 */  false,
  /*  477 */  false,
  /*  478 */  false,
  /*  479 */  false,
  /*  480 */  false,
  /*  481 */  false,
  /*  482 */  false,
  /*  483 */  false,
  /*  484 */  false,
  /*  485 */  false,
  /*  486 */  false,
  /*  487 */  false,
  /*  488 */  false,
  /*  489 */  false,
  /*  490 */  false,
  /*  491 */  false,
  /*  492 */  false,
  /*  493 */  false,
  /*  494 */  false,
  /*  495 */  false,
  /*  496 */  false,
  /*  497 */  false,
  /*  498 */  false,
  /*  499 */  false,
  /*  500 */  false,
  /*  501 */  false,
  /*  502 */  false,
  /*  503 */  false,
  /*  504 */  false,
  /*  505 */  false,
  /*  506 */  false,
  /*  507 */  false,
  /*  508 */  false,
  /*  509 */  false,
  /*  510 */  false,
  /*  511 */  false,
  /*  512 */  false,
  /*  513 */  false,
  /*  514 */  false,
  /*  515 */  false,
  /*  516 */  false,
  /*  517 */  false,
  /*  518 */  false,
  /*  519 */  false,
  /*  520 */  false,
  /*  521 */  false,
  /*  522 */  false,
  /*  523 */  false,
  /*  524 */  false,
  /*  525 */  false,
  /*  526 */  false,
  /*  527 */  false,
  /*  528 */  false,
  /*  529 */  false,
  /*  530 */  false,
  /*  531 */  false,
  /*  532 */  false,
  /*  533 */  false,
  /*  534 */  false,
  /*  535 */  false,
  /*  536 */  false,
  /*  537 */  false,
  /*  538 */  false,
  /*  539 */  false,
  /*  540 */  false,
  /*  541 */  false,
  /*  542 */  false,
  /*  543 */  false,
  /*  544 */  false,
  /*  545 */  false,
  /*  546 */  false,
  /*  547 */  false,
  /*  548 */  false,
  /*  549 */  false,
  /*  550 */  false,
  /*  551 */  false,
  /*  552 */  false,
  /*  553 */  false,
  /*  554 */  false,
  /*  555 */  false,
  /*  556 */  false,
  /*  557 */  false,
  /*  558 */  false,
  /*  559 */  false,
  /*  560 */  false,
  /*  561 */  false,
  /*  562 */  false,
  /*  563 */  false,
  /*  564 */  false,
  /*  565 */  false,
  /*  566 */  false,
  /*  567 */  false,
  /*  568 */  false,
  /*  569 */  false,
  /*  570 */  false,
  /*  571 */  false,
  /*  572 */  false,
  /*  573 */  false,
  /*  574 */  false,
  /*  575 */  false,
  /*  576 */  false,
  /*  577 */  false,
  /*  578 */  false,
  /*  579 */  false,
  /*  580 */  false,
  /*  581 */  false,
  /*  582 */  false,
  /*  583 */  false,
  /*  584 */  false,
  /*  585 */  false,
  /*  586 */  false,
  /*  587 */  false,
  /*  588 */  false,
  /*  589 */  false,
  /*  590 */  false,
  /*  591 */  false,
  /*  592 */  false,
  /*  593 */  false,
  /*  594 */  false,
  /*  595 */  false,
  /*  596 */  false,
  /*  597 */  false,
  /*  598 */  false,
  /*  599 */  false,
  /*  600 */  false,
  /*  601 */  false,
  /*  602 */  false,
  /*  603 */  false,
  /*  604 */  false,
  /*  605 */  false,
  /*  606 */  false,
  /*  607 */  false,
  /*  608 */  false,
  /*  609 */  false,
  /*  610 */  false,
  /*  611 */  false,
  /*  612 */  false,
  /*  613 */  false,
  /*  614 */  false,
  /*  615 */  false,
  /*  616 */  false,
  /*  617 */  false,
  /*  618 */  false,
  /*  619 */  false,
  /*  620 */  false,
  /*  621 */  false,
  /*  622 */  false,
  /*  623 */  false,
  /*  624 */  false,
  /*  625 */  false,
  /*  626 */  false,
  /*  627 */  false,
  /*  628 */  false,
  /*  629 */  false,
  /*  630 */  false,
  /*  631 */  false,
  /*  632 */  false,
  /*  633 */  false,
  /*  634 */  false,
  /*  635 */  false,
  /*  636 */  false,
  /*  637 */  false,
  /*  638 */  false,
  /*  639 */  false,
  /*  640 */  false,
  /*  641 */  false,
  /*  642 */  false,
  /*  643 */  false,
  /*  644 */  false,
  /*  645 */  false,
  /*  646 */  false,
  /*  647 */  false,
  /*  648 */  false,
  /*  649 */  false,
  /*  650 */  false,
  /*  651 */  false,
  /*  652 */  false,
  /*  653 */  false,
  /*  654 */  false,
  /*  655 */  false,
  /*  656 */  false,
  /*  657 */  false,
  /*  658 */  false,
  /*  659 */  false,
  /*  660 */  false,
  /*  661 */  false,
  /*  662 */  false,
  /*  663 */  false,
  /*  664 */  false,
  /*  665 */  false,
  /*  666 */  false,
  /*  667 */  false,
  /*  668 */  false,
  /*  669 */  false,
  /*  670 */  false,
  /*  671 */  false,
  /*  672 */  false,
  /*  673 */  false,
  /*  674 */  false,
  /*  675 */  false,
  /*  676 */  false,
  /*  677 */  false,
  /*  678 */  false,
  /*  679 */  false,
  /*  680 */  false,
  /*  681 */  false,
  /*  682 */  false,
  /*  683 */  false,
  /*  684 */  false,
  /*  685 */  false,
  /*  686 */  false,
  /*  687 */  false,
  /*  688 */  false,
  /*  689 */  false,
  /*  690 */  false,
  /*  691 */  false,
  /*  692 */  false,
  /*  693 */  false,
  /*  694 */  false,
  /*  695 */  false,
  /*  696 */  false,
  /*  697 */  false,
  /*  698 */  false,
  /*  699 */  false,
  /*  700 */  false,
  /*  701 */  false,
  /*  702 */  false,
  /*  703 */  false,
  /*  704 */  false,
  /*  705 */  false,
  /*  706 */  false,
  /*  707 */  false,
  /*  708 */  false,
  /*  709 */  false,
  /*  710 */  false,
  /*  711 */  false,
  /*  712 */  false,
  /*  713 */  false,
  /*  714 */  false,
  /*  715 */  false,
  /*  716 */  false,
  /*  717 */  false,
  /*  718 */  false,
  /*  719 */  false,
  /*  720 */  false,
  /*  721 */  false,
  /*  722 */  false,
  /*  723 */  false,
  /*  724 */  false,
  /*  725 */  false,
  /*  726 */  false,
  /*  727 */  false,
  /*  728 */  false,
  /*  729 */  false,
  /*  730 */  false,
  /*  731 */  false,
  /*  732 */  false,
  /*  733 */  false,
  /*  734 */  false,
  /*  735 */  false,
  /*  736 */  false,
  /*  737 */  false,
  /*  738 */  false,
  /*  739 */  false,
  /*  740 */  false,
  /*  741 */  false,
  /*  742 */  false,
  /*  743 */  false,
  /*  744 */  false,
  /*  745 */  false,
  /*  746 */  false,
  /*  747 */  false,
  /*  748 */  false,
  /*  749 */  false,
  /*  750 */  false,
  /*  751 */  false,
  /*  752 */  false,
  /*  753 */  false,
  // last instruction
  false // no trailing comma
};

// Mapping from machine-independent opcode to boolean
const        char must_clone[] = {
  0, // Node: 0
  0, // Set: 1
  0, // RegN: 2
  0, // RegI: 3
  0, // RegP: 4
  0, // RegF: 5
  0, // RegD: 6
  0, // RegL: 7
  0, // VecA: 8
  0, // VecS: 9
  0, // VecD: 10
  0, // VecX: 11
  0, // VecY: 12
  0, // VecZ: 13
  0, // RegVectMask: 14
  0, // RegFlags: 15
  0, // _last_machine_leaf: 16
  0, // AbsD: 17
  0, // AbsF: 18
  0, // AbsI: 19
  0, // AbsL: 20
  0, // AddD: 21
  0, // AddF: 22
  0, // AddI: 23
  0, // AddL: 24
  0, // AddP: 25
  0, // Allocate: 26
  0, // AllocateArray: 27
  0, // AndI: 28
  0, // AndL: 29
  0, // ArrayCopy: 30
  0, // AryEq: 31
  0, // AtanD: 32
  1, // Binary: 33
  0, // Blackhole: 34
  1, // Bool: 35
  0, // BoxLock: 36
  0, // ReverseBytesI: 37
  0, // ReverseBytesL: 38
  0, // ReverseBytesUS: 39
  0, // ReverseBytesS: 40
  0, // ReverseBytesV: 41
  0, // CProj: 42
  0, // CacheWB: 43
  0, // CacheWBPreSync: 44
  0, // CacheWBPostSync: 45
  0, // CallDynamicJava: 46
  0, // CallJava: 47
  0, // CallLeaf: 48
  0, // CallLeafNoFP: 49
  0, // CallLeafVector: 50
  0, // CallRuntime: 51
  0, // CallStaticJava: 52
  0, // CastDD: 53
  0, // CastFF: 54
  0, // CastII: 55
  0, // CastLL: 56
  0, // CastVV: 57
  0, // CastX2P: 58
  0, // CastP2X: 59
  0, // CastPP: 60
  0, // Catch: 61
  0, // CatchProj: 62
  0, // CheckCastPP: 63
  0, // ClearArray: 64
  0, // CompressBits: 65
  0, // ExpandBits: 66
  0, // ConstraintCast: 67
  0, // CMoveD: 68
  0, // CMoveVD: 69
  0, // CMoveF: 70
  0, // CMoveVF: 71
  0, // CMoveI: 72
  0, // CMoveL: 73
  0, // CMoveP: 74
  0, // CMoveN: 75
  1, // CmpN: 76
  1, // CmpD: 77
  0, // CmpD3: 78
  1, // CmpF: 79
  0, // CmpF3: 80
  1, // CmpI: 81
  1, // CmpL: 82
  0, // CmpL3: 83
  0, // CmpLTMask: 84
  1, // CmpP: 85
  1, // CmpU: 86
  0, // CmpU3: 87
  1, // CmpUL: 88
  0, // CmpUL3: 89
  0, // CompareAndSwapB: 90
  0, // CompareAndSwapS: 91
  0, // CompareAndSwapI: 92
  0, // CompareAndSwapL: 93
  0, // CompareAndSwapP: 94
  0, // CompareAndSwapN: 95
  0, // WeakCompareAndSwapB: 96
  0, // WeakCompareAndSwapS: 97
  0, // WeakCompareAndSwapI: 98
  0, // WeakCompareAndSwapL: 99
  0, // WeakCompareAndSwapP: 100
  0, // WeakCompareAndSwapN: 101
  0, // CompareAndExchangeB: 102
  0, // CompareAndExchangeS: 103
  0, // CompareAndExchangeI: 104
  0, // CompareAndExchangeL: 105
  0, // CompareAndExchangeP: 106
  0, // CompareAndExchangeN: 107
  0, // GetAndAddB: 108
  0, // GetAndAddS: 109
  0, // GetAndAddI: 110
  0, // GetAndAddL: 111
  0, // GetAndSetB: 112
  0, // GetAndSetS: 113
  0, // GetAndSetI: 114
  0, // GetAndSetL: 115
  0, // GetAndSetP: 116
  0, // GetAndSetN: 117
  0, // Con: 118
  0, // ConN: 119
  0, // ConNKlass: 120
  0, // ConD: 121
  0, // ConF: 122
  0, // ConI: 123
  0, // ConL: 124
  0, // ConP: 125
  0, // Conv2B: 126
  0, // ConvD2F: 127
  0, // ConvD2I: 128
  0, // ConvD2L: 129
  0, // ConvF2D: 130
  0, // ConvF2I: 131
  0, // ConvF2L: 132
  0, // ConvI2D: 133
  0, // ConvI2F: 134
  0, // ConvI2L: 135
  0, // ConvL2D: 136
  0, // ConvL2F: 137
  0, // ConvL2I: 138
  0, // ConvF2HF: 139
  0, // ConvHF2F: 140
  0, // CountedLoop: 141
  0, // CountedLoopEnd: 142
  0, // OuterStripMinedLoop: 143
  0, // OuterStripMinedLoopEnd: 144
  0, // LongCountedLoop: 145
  0, // LongCountedLoopEnd: 146
  0, // CountLeadingZerosI: 147
  0, // CountLeadingZerosL: 148
  0, // CountLeadingZerosV: 149
  0, // CountTrailingZerosI: 150
  0, // CountTrailingZerosL: 151
  0, // CountTrailingZerosV: 152
  0, // CreateEx: 153
  0, // DecodeN: 154
  0, // DecodeNKlass: 155
  0, // DivD: 156
  0, // DivF: 157
  0, // DivI: 158
  0, // DivL: 159
  0, // UDivI: 160
  0, // UDivL: 161
  0, // DivMod: 162
  0, // DivModI: 163
  0, // DivModL: 164
  0, // UDivModI: 165
  0, // UDivModL: 166
  0, // EncodeISOArray: 167
  0, // EncodeP: 168
  0, // EncodePKlass: 169
  1, // FastLock: 170
  1, // FastUnlock: 171
  0, // FmaD: 172
  0, // FmaF: 173
  0, // Goto: 174
  0, // Halt: 175
  0, // CountPositives: 176
  0, // If: 177
  0, // RangeCheck: 178
  0, // IfFalse: 179
  0, // IfTrue: 180
  0, // Initialize: 181
  0, // JProj: 182
  0, // Jump: 183
  0, // JumpProj: 184
  0, // LShiftI: 185
  0, // LShiftL: 186
  0, // LoadB: 187
  0, // LoadUB: 188
  0, // LoadUS: 189
  0, // LoadD: 190
  0, // LoadD_unaligned: 191
  0, // LoadF: 192
  0, // LoadI: 193
  0, // LoadKlass: 194
  0, // LoadNKlass: 195
  0, // LoadL: 196
  0, // LoadL_unaligned: 197
  0, // LoadP: 198
  0, // LoadN: 199
  0, // LoadRange: 200
  0, // LoadS: 201
  0, // Lock: 202
  0, // Loop: 203
  0, // LoopLimit: 204
  0, // Mach: 205
  0, // MachNullCheck: 206
  0, // MachProj: 207
  0, // MulAddS2I: 208
  0, // MaxI: 209
  0, // MaxL: 210
  0, // MaxD: 211
  0, // MaxF: 212
  0, // MemBarAcquire: 213
  0, // LoadFence: 214
  0, // MemBarAcquireLock: 215
  0, // MemBarCPUOrder: 216
  0, // MemBarRelease: 217
  0, // StoreFence: 218
  0, // StoreStoreFence: 219
  0, // MemBarReleaseLock: 220
  0, // MemBarVolatile: 221
  0, // MemBarStoreStore: 222
  0, // MergeMem: 223
  0, // MinI: 224
  0, // MinL: 225
  0, // MinF: 226
  0, // MinD: 227
  0, // ModD: 228
  0, // ModF: 229
  0, // ModI: 230
  0, // ModL: 231
  0, // UModI: 232
  0, // UModL: 233
  0, // MoveI2F: 234
  0, // MoveF2I: 235
  0, // MoveL2D: 236
  0, // MoveD2L: 237
  0, // IsInfiniteF: 238
  0, // IsFiniteF: 239
  0, // IsInfiniteD: 240
  0, // IsFiniteD: 241
  0, // MulD: 242
  0, // MulF: 243
  0, // MulHiL: 244
  0, // UMulHiL: 245
  0, // MulI: 246
  0, // MulL: 247
  0, // Multi: 248
  0, // NegI: 249
  0, // NegL: 250
  0, // NegD: 251
  0, // NegF: 252
  0, // NeverBranch: 253
  0, // OnSpinWait: 254
  0, // Opaque1: 255
  0, // OpaqueLoopInit: 256
  0, // OpaqueLoopStride: 257
  0, // Opaque2: 258
  0, // Opaque3: 259
  0, // Opaque4: 260
  0, // ProfileBoolean: 261
  0, // OrI: 262
  0, // OrL: 263
  1, // OverflowAddI: 264
  1, // OverflowSubI: 265
  1, // OverflowMulI: 266
  1, // OverflowAddL: 267
  1, // OverflowSubL: 268
  1, // OverflowMulL: 269
  0, // PCTable: 270
  0, // Parm: 271
  0, // PartialSubtypeCheck: 272
  0, // SubTypeCheck: 273
  0, // Phi: 274
  0, // PopCountI: 275
  0, // PopCountL: 276
  0, // PopCountVI: 277
  0, // PopCountVL: 278
  0, // PopulateIndex: 279
  0, // PrefetchAllocation: 280
  0, // Proj: 281
  0, // RShiftI: 282
  0, // RShiftL: 283
  0, // Region: 284
  0, // Rethrow: 285
  0, // Return: 286
  0, // ReverseI: 287
  0, // ReverseL: 288
  0, // ReverseV: 289
  0, // Root: 290
  0, // RoundDouble: 291
  0, // RoundDoubleMode: 292
  0, // RoundDoubleModeV: 293
  0, // RoundFloat: 294
  0, // RotateLeft: 295
  0, // RotateLeftV: 296
  0, // RotateRight: 297
  0, // RotateRightV: 298
  0, // SafePoint: 299
  0, // SafePointScalarObject: 300
  0, // ShenandoahCompareAndExchangeP: 301
  0, // ShenandoahCompareAndExchangeN: 302
  0, // ShenandoahCompareAndSwapN: 303
  0, // ShenandoahCompareAndSwapP: 304
  0, // ShenandoahWeakCompareAndSwapN: 305
  0, // ShenandoahWeakCompareAndSwapP: 306
  0, // ShenandoahIUBarrier: 307
  0, // ShenandoahLoadReferenceBarrier: 308
  0, // SCMemProj: 309
  0, // CopySignD: 310
  0, // CopySignF: 311
  0, // SignumD: 312
  0, // SignumF: 313
  0, // SignumVF: 314
  0, // SignumVD: 315
  0, // SqrtD: 316
  0, // SqrtF: 317
  0, // RoundF: 318
  0, // RoundD: 319
  0, // Start: 320
  0, // StartOSR: 321
  0, // StoreB: 322
  0, // StoreC: 323
  0, // StoreCM: 324
  0, // StoreD: 325
  0, // StoreF: 326
  0, // StoreI: 327
  0, // StoreL: 328
  0, // StoreP: 329
  0, // StoreN: 330
  0, // StoreNKlass: 331
  0, // StrComp: 332
  0, // StrCompressedCopy: 333
  0, // StrEquals: 334
  0, // StrIndexOf: 335
  0, // StrIndexOfChar: 336
  0, // StrInflatedCopy: 337
  0, // SubD: 338
  0, // SubF: 339
  0, // SubI: 340
  0, // SubL: 341
  0, // TailCall: 342
  0, // TailJump: 343
  0, // MacroLogicV: 344
  0, // ThreadLocal: 345
  0, // Unlock: 346
  0, // URShiftB: 347
  0, // URShiftS: 348
  0, // URShiftI: 349
  0, // URShiftL: 350
  0, // XorI: 351
  0, // XorL: 352
  0, // Vector: 353
  0, // AddVB: 354
  0, // AddVS: 355
  0, // AddVI: 356
  0, // AddReductionVI: 357
  0, // AddVL: 358
  0, // AddReductionVL: 359
  0, // AddVF: 360
  0, // AddReductionVF: 361
  0, // AddVD: 362
  0, // AddReductionVD: 363
  0, // SubVB: 364
  0, // SubVS: 365
  0, // SubVI: 366
  0, // SubVL: 367
  0, // SubVF: 368
  0, // SubVD: 369
  0, // MulVB: 370
  0, // MulVS: 371
  0, // MulVI: 372
  0, // MulReductionVI: 373
  0, // MulVL: 374
  0, // MulReductionVL: 375
  0, // MulVF: 376
  0, // MulReductionVF: 377
  0, // MulVD: 378
  0, // MulReductionVD: 379
  0, // MulAddVS2VI: 380
  0, // FmaVD: 381
  0, // FmaVF: 382
  0, // DivVF: 383
  0, // DivVD: 384
  0, // AbsVB: 385
  0, // AbsVS: 386
  0, // AbsVI: 387
  0, // AbsVL: 388
  0, // AbsVF: 389
  0, // AbsVD: 390
  0, // NegVI: 391
  0, // NegVL: 392
  0, // NegVF: 393
  0, // NegVD: 394
  0, // SqrtVD: 395
  0, // SqrtVF: 396
  0, // LShiftCntV: 397
  0, // RShiftCntV: 398
  0, // LShiftVB: 399
  0, // LShiftVS: 400
  0, // LShiftVI: 401
  0, // LShiftVL: 402
  0, // RShiftVB: 403
  0, // RShiftVS: 404
  0, // RShiftVI: 405
  0, // RShiftVL: 406
  0, // URShiftVB: 407
  0, // URShiftVS: 408
  0, // URShiftVI: 409
  0, // URShiftVL: 410
  0, // AndV: 411
  0, // AndReductionV: 412
  0, // OrV: 413
  0, // OrReductionV: 414
  0, // XorV: 415
  0, // XorReductionV: 416
  0, // MinV: 417
  0, // MaxV: 418
  0, // MinReductionV: 419
  0, // MaxReductionV: 420
  0, // CompressV: 421
  0, // CompressM: 422
  0, // ExpandV: 423
  0, // LoadVector: 424
  0, // LoadVectorGather: 425
  0, // LoadVectorGatherMasked: 426
  0, // StoreVector: 427
  0, // StoreVectorScatter: 428
  0, // StoreVectorScatterMasked: 429
  0, // LoadVectorMasked: 430
  0, // StoreVectorMasked: 431
  0, // VectorCmpMasked: 432
  0, // VectorMaskGen: 433
  0, // VectorMaskOp: 434
  0, // VectorMaskTrueCount: 435
  0, // VectorMaskFirstTrue: 436
  0, // VectorMaskLastTrue: 437
  0, // VectorMaskToLong: 438
  0, // VectorLongToMask: 439
  0, // Pack: 440
  0, // PackB: 441
  0, // PackS: 442
  0, // PackI: 443
  0, // PackL: 444
  0, // PackF: 445
  0, // PackD: 446
  0, // Pack2L: 447
  0, // Pack2D: 448
  0, // ReplicateB: 449
  0, // ReplicateS: 450
  0, // ReplicateI: 451
  0, // ReplicateL: 452
  0, // ReplicateF: 453
  0, // ReplicateD: 454
  0, // RoundVF: 455
  0, // RoundVD: 456
  0, // Extract: 457
  0, // ExtractB: 458
  0, // ExtractUB: 459
  0, // ExtractC: 460
  0, // ExtractS: 461
  0, // ExtractI: 462
  0, // ExtractL: 463
  0, // ExtractF: 464
  0, // ExtractD: 465
  0, // Digit: 466
  0, // LowerCase: 467
  0, // UpperCase: 468
  0, // Whitespace: 469
  0, // VectorBox: 470
  0, // VectorBoxAllocate: 471
  0, // VectorUnbox: 472
  0, // VectorMaskWrapper: 473
  0, // VectorMaskCmp: 474
  0, // VectorMaskCast: 475
  0, // VectorTest: 476
  0, // VectorBlend: 477
  0, // VectorRearrange: 478
  0, // VectorLoadMask: 479
  0, // VectorLoadShuffle: 480
  0, // VectorLoadConst: 481
  0, // VectorStoreMask: 482
  0, // VectorReinterpret: 483
  0, // VectorCast: 484
  0, // VectorCastB2X: 485
  0, // VectorCastS2X: 486
  0, // VectorCastI2X: 487
  0, // VectorCastL2X: 488
  0, // VectorCastF2X: 489
  0, // VectorCastD2X: 490
  0, // VectorUCastB2X: 491
  0, // VectorUCastS2X: 492
  0, // VectorUCastI2X: 493
  0, // VectorInsert: 494
  0, // MaskAll: 495
  0, // AndVMask: 496
  0, // OrVMask: 497
  0 // no trailing comma // XorVMask: 498
};
//  The following instructions can cisc-spill



// An array of character pointers to machine register names.
const char *Matcher::regName[REG_COUNT] = {
  "R7",
  "R7_H",
  "R28",
  "R28_H",
  "R29",
  "R29_H",
  "R30",
  "R30_H",
  "R31",
  "R31_H",
  "R10",
  "R10_H",
  "R11",
  "R11_H",
  "R12",
  "R12_H",
  "R13",
  "R13_H",
  "R14",
  "R14_H",
  "R15",
  "R15_H",
  "R16",
  "R16_H",
  "R17",
  "R17_H",
  "R9",
  "R9_H",
  "R18",
  "R18_H",
  "R19",
  "R19_H",
  "R20",
  "R20_H",
  "R21",
  "R21_H",
  "R22",
  "R22_H",
  "R24",
  "R24_H",
  "R25",
  "R25_H",
  "R26",
  "R26_H",
  "R23",
  "R23_H",
  "R27",
  "R27_H",
  "R4",
  "R4_H",
  "R8",
  "R8_H",
  "R0",
  "R0_H",
  "R1",
  "R1_H",
  "R2",
  "R2_H",
  "R3",
  "R3_H",
  "F0",
  "F0_H",
  "F1",
  "F1_H",
  "F2",
  "F2_H",
  "F3",
  "F3_H",
  "F4",
  "F4_H",
  "F5",
  "F5_H",
  "F6",
  "F6_H",
  "F7",
  "F7_H",
  "F28",
  "F28_H",
  "F29",
  "F29_H",
  "F30",
  "F30_H",
  "F31",
  "F31_H",
  "F10",
  "F10_H",
  "F11",
  "F11_H",
  "F12",
  "F12_H",
  "F13",
  "F13_H",
  "F14",
  "F14_H",
  "F15",
  "F15_H",
  "F16",
  "F16_H",
  "F17",
  "F17_H",
  "F8",
  "F8_H",
  "F9",
  "F9_H",
  "F18",
  "F18_H",
  "F19",
  "F19_H",
  "F20",
  "F20_H",
  "F21",
  "F21_H",
  "F22",
  "F22_H",
  "F23",
  "F23_H",
  "F24",
  "F24_H",
  "F25",
  "F25_H",
  "F26",
  "F26_H",
  "F27",
  "F27_H",
  "V0",
  "V0_H",
  "V0_J",
  "V0_K",
  "V1",
  "V1_H",
  "V1_J",
  "V1_K",
  "V2",
  "V2_H",
  "V2_J",
  "V2_K",
  "V3",
  "V3_H",
  "V3_J",
  "V3_K",
  "V4",
  "V4_H",
  "V4_J",
  "V4_K",
  "V5",
  "V5_H",
  "V5_J",
  "V5_K",
  "V6",
  "V6_H",
  "V6_J",
  "V6_K",
  "V7",
  "V7_H",
  "V7_J",
  "V7_K",
  "V8",
  "V8_H",
  "V8_J",
  "V8_K",
  "V9",
  "V9_H",
  "V9_J",
  "V9_K",
  "V10",
  "V10_H",
  "V10_J",
  "V10_K",
  "V11",
  "V11_H",
  "V11_J",
  "V11_K",
  "V12",
  "V12_H",
  "V12_J",
  "V12_K",
  "V13",
  "V13_H",
  "V13_J",
  "V13_K",
  "V14",
  "V14_H",
  "V14_J",
  "V14_K",
  "V15",
  "V15_H",
  "V15_J",
  "V15_K",
  "V16",
  "V16_H",
  "V16_J",
  "V16_K",
  "V17",
  "V17_H",
  "V17_J",
  "V17_K",
  "V18",
  "V18_H",
  "V18_J",
  "V18_K",
  "V19",
  "V19_H",
  "V19_J",
  "V19_K",
  "V20",
  "V20_H",
  "V20_J",
  "V20_K",
  "V21",
  "V21_H",
  "V21_J",
  "V21_K",
  "V22",
  "V22_H",
  "V22_J",
  "V22_K",
  "V23",
  "V23_H",
  "V23_J",
  "V23_K",
  "V24",
  "V24_H",
  "V24_J",
  "V24_K",
  "V25",
  "V25_H",
  "V25_J",
  "V25_K",
  "V26",
  "V26_H",
  "V26_J",
  "V26_K",
  "V27",
  "V27_H",
  "V27_J",
  "V27_K",
  "V28",
  "V28_H",
  "V28_J",
  "V28_K",
  "V29",
  "V29_H",
  "V29_J",
  "V29_K",
  "V30",
  "V30_H",
  "V30_J",
  "V30_K",
  "V31",
  "V31_H",
  "V31_J",
  "V31_K",
  "RFLAGS" // no trailing comma
};

// An array of character pointers to machine register names.
const VMReg OptoReg::opto2vm[REG_COUNT] = {
	x7->as_VMReg()         ,
	x7->as_VMReg()->next() ,
	x28->as_VMReg()        ,
	x28->as_VMReg()->next(),
	x29->as_VMReg()        ,
	x29->as_VMReg()->next(),
	x30->as_VMReg()        ,
	x30->as_VMReg()->next(),
	x31->as_VMReg()        ,
	x31->as_VMReg()->next(),
	x10->as_VMReg()        ,
	x10->as_VMReg()->next(),
	x11->as_VMReg()        ,
	x11->as_VMReg()->next(),
	x12->as_VMReg()        ,
	x12->as_VMReg()->next(),
	x13->as_VMReg()        ,
	x13->as_VMReg()->next(),
	x14->as_VMReg()        ,
	x14->as_VMReg()->next(),
	x15->as_VMReg()        ,
	x15->as_VMReg()->next(),
	x16->as_VMReg()        ,
	x16->as_VMReg()->next(),
	x17->as_VMReg()        ,
	x17->as_VMReg()->next(),
	x9->as_VMReg()         ,
	x9->as_VMReg()->next() ,
	x18->as_VMReg()        ,
	x18->as_VMReg()->next(),
	x19->as_VMReg()        ,
	x19->as_VMReg()->next(),
	x20->as_VMReg()        ,
	x20->as_VMReg()->next(),
	x21->as_VMReg()        ,
	x21->as_VMReg()->next(),
	x22->as_VMReg()        ,
	x22->as_VMReg()->next(),
	x24->as_VMReg()        ,
	x24->as_VMReg()->next(),
	x25->as_VMReg()        ,
	x25->as_VMReg()->next(),
	x26->as_VMReg()        ,
	x26->as_VMReg()->next(),
	x23->as_VMReg()        ,
	x23->as_VMReg()->next(),
	x27->as_VMReg()        ,
	x27->as_VMReg()->next(),
	x4->as_VMReg()         ,
	x4->as_VMReg()->next() ,
	x8->as_VMReg()         ,
	x8->as_VMReg()->next() ,
	x0->as_VMReg()         ,
	x0->as_VMReg()->next() ,
	x1->as_VMReg()         ,
	x1->as_VMReg()->next() ,
	x2->as_VMReg()         ,
	x2->as_VMReg()->next() ,
	x3->as_VMReg()         ,
	x3->as_VMReg()->next() ,
	f0->as_VMReg()          ,
	f0->as_VMReg()->next()  ,
	f1->as_VMReg()          ,
	f1->as_VMReg()->next()  ,
	f2->as_VMReg()          ,
	f2->as_VMReg()->next()  ,
	f3->as_VMReg()          ,
	f3->as_VMReg()->next()  ,
	f4->as_VMReg()          ,
	f4->as_VMReg()->next()  ,
	f5->as_VMReg()          ,
	f5->as_VMReg()->next()  ,
	f6->as_VMReg()          ,
	f6->as_VMReg()->next()  ,
	f7->as_VMReg()          ,
	f7->as_VMReg()->next()  ,
	f28->as_VMReg()         ,
	f28->as_VMReg()->next() ,
	f29->as_VMReg()         ,
	f29->as_VMReg()->next() ,
	f30->as_VMReg()         ,
	f30->as_VMReg()->next() ,
	f31->as_VMReg()         ,
	f31->as_VMReg()->next() ,
	f10->as_VMReg()         ,
	f10->as_VMReg()->next() ,
	f11->as_VMReg()         ,
	f11->as_VMReg()->next() ,
	f12->as_VMReg()         ,
	f12->as_VMReg()->next() ,
	f13->as_VMReg()         ,
	f13->as_VMReg()->next() ,
	f14->as_VMReg()         ,
	f14->as_VMReg()->next() ,
	f15->as_VMReg()         ,
	f15->as_VMReg()->next() ,
	f16->as_VMReg()         ,
	f16->as_VMReg()->next() ,
	f17->as_VMReg()         ,
	f17->as_VMReg()->next() ,
	f8->as_VMReg()          ,
	f8->as_VMReg()->next()  ,
	f9->as_VMReg()          ,
	f9->as_VMReg()->next()  ,
	f18->as_VMReg()         ,
	f18->as_VMReg()->next() ,
	f19->as_VMReg()         ,
	f19->as_VMReg()->next() ,
	f20->as_VMReg()         ,
	f20->as_VMReg()->next() ,
	f21->as_VMReg()         ,
	f21->as_VMReg()->next() ,
	f22->as_VMReg()         ,
	f22->as_VMReg()->next() ,
	f23->as_VMReg()         ,
	f23->as_VMReg()->next() ,
	f24->as_VMReg()         ,
	f24->as_VMReg()->next() ,
	f25->as_VMReg()         ,
	f25->as_VMReg()->next() ,
	f26->as_VMReg()         ,
	f26->as_VMReg()->next() ,
	f27->as_VMReg()         ,
	f27->as_VMReg()->next() ,
	v0->as_VMReg()           ,
	v0->as_VMReg()->next()   ,
	v0->as_VMReg()->next(2)  ,
	v0->as_VMReg()->next(3)  ,
	v1->as_VMReg() 	        ,
	v1->as_VMReg()->next()   ,
	v1->as_VMReg()->next(2)  ,
	v1->as_VMReg()->next(3)  ,
	v2->as_VMReg()           ,
	v2->as_VMReg()->next()   ,
	v2->as_VMReg()->next(2)  ,
	v2->as_VMReg()->next(3)  ,
	v3->as_VMReg()           ,
	v3->as_VMReg()->next()   ,
	v3->as_VMReg()->next(2)  ,
	v3->as_VMReg()->next(3)  ,
	v4->as_VMReg()           ,
	v4->as_VMReg()->next()   ,
	v4->as_VMReg()->next(2)  ,
	v4->as_VMReg()->next(3)  ,
	v5->as_VMReg() 	        ,
	v5->as_VMReg()->next()   ,
	v5->as_VMReg()->next(2)  ,
	v5->as_VMReg()->next(3)  ,
	v6->as_VMReg()           ,
	v6->as_VMReg()->next()   ,
	v6->as_VMReg()->next(2)  ,
	v6->as_VMReg()->next(3)  ,
	v7->as_VMReg() 	        ,
	v7->as_VMReg()->next()   ,
	v7->as_VMReg()->next(2)  ,
	v7->as_VMReg()->next(3)  ,
	v8->as_VMReg()           ,
	v8->as_VMReg()->next()   ,
	v8->as_VMReg()->next(2)  ,
	v8->as_VMReg()->next(3)  ,
	v9->as_VMReg()           ,
	v9->as_VMReg()->next()   ,
	v9->as_VMReg()->next(2)  ,
	v9->as_VMReg()->next(3)  ,
	v10->as_VMReg()          ,
	v10->as_VMReg()->next()  ,
	v10->as_VMReg()->next(2) ,
	v10->as_VMReg()->next(3) ,
	v11->as_VMReg()          ,
	v11->as_VMReg()->next()  ,
	v11->as_VMReg()->next(2) ,
	v11->as_VMReg()->next(3) ,
	v12->as_VMReg()          ,
	v12->as_VMReg()->next()  ,
	v12->as_VMReg()->next(2) ,
	v12->as_VMReg()->next(3) ,
	v13->as_VMReg()          ,
	v13->as_VMReg()->next()  ,
	v13->as_VMReg()->next(2) ,
	v13->as_VMReg()->next(3) ,
	v14->as_VMReg()          ,
	v14->as_VMReg()->next()  ,
	v14->as_VMReg()->next(2) ,
	v14->as_VMReg()->next(3) ,
	v15->as_VMReg()          ,
	v15->as_VMReg()->next()  ,
	v15->as_VMReg()->next(2) ,
	v15->as_VMReg()->next(3) ,
	v16->as_VMReg()          ,
	v16->as_VMReg()->next()  ,
	v16->as_VMReg()->next(2) ,
	v16->as_VMReg()->next(3) ,
	v17->as_VMReg()          ,
	v17->as_VMReg()->next()  ,
	v17->as_VMReg()->next(2) ,
	v17->as_VMReg()->next(3) ,
	v18->as_VMReg()          ,
	v18->as_VMReg()->next()  ,
	v18->as_VMReg()->next(2) ,
	v18->as_VMReg()->next(3) ,
	v19->as_VMReg()          ,
	v19->as_VMReg()->next()  ,
	v19->as_VMReg()->next(2) ,
	v19->as_VMReg()->next(3) ,
	v20->as_VMReg()          ,
	v20->as_VMReg()->next()  ,
	v20->as_VMReg()->next(2) ,
	v20->as_VMReg()->next(3) ,
	v21->as_VMReg()          ,
	v21->as_VMReg()->next()  ,
	v21->as_VMReg()->next(2) ,
	v21->as_VMReg()->next(3) ,
	v22->as_VMReg()          ,
	v22->as_VMReg()->next()  ,
	v22->as_VMReg()->next(2) ,
	v22->as_VMReg()->next(3) ,
	v23->as_VMReg()          ,
	v23->as_VMReg()->next()  ,
	v23->as_VMReg()->next(2) ,
	v23->as_VMReg()->next(3) ,
	v24->as_VMReg()          ,
	v24->as_VMReg()->next()  ,
	v24->as_VMReg()->next(2) ,
	v24->as_VMReg()->next(3) ,
	v25->as_VMReg()          ,
	v25->as_VMReg()->next()  ,
	v25->as_VMReg()->next(2) ,
	v25->as_VMReg()->next(3) ,
	v26->as_VMReg()          ,
	v26->as_VMReg()->next()  ,
	v26->as_VMReg()->next(2) ,
	v26->as_VMReg()->next(3) ,
	v27->as_VMReg()          ,
	v27->as_VMReg()->next()  ,
	v27->as_VMReg()->next(2) ,
	v27->as_VMReg()->next(3) ,
	v28->as_VMReg()          ,
	v28->as_VMReg()->next()  ,
	v28->as_VMReg()->next(2) ,
	v28->as_VMReg()->next(3) ,
	v29->as_VMReg()          ,
	v29->as_VMReg()->next()  ,
	v29->as_VMReg()->next(2) ,
	v29->as_VMReg()->next(3) ,
	v30->as_VMReg()          ,
	v30->as_VMReg()->next()  ,
	v30->as_VMReg()->next(2) ,
	v30->as_VMReg()->next(3) ,
	v31->as_VMReg()          ,
	v31->as_VMReg()->next()  ,
	v31->as_VMReg()->next(2) ,
	v31->as_VMReg()->next(3) ,
	x6->as_VMReg()         // no trailing comma
	};

 OptoReg::Name OptoReg::vm2opto[ConcreteRegisterImpl::number_of_registers];

// An array of the machine register encode values
const unsigned char Matcher::_regEncode[REG_COUNT] = {
  (unsigned char)'\x7',  // R7
  (unsigned char)'\x7',  // R7_H
  (unsigned char)'\x1C',  // R28
  (unsigned char)'\x1C',  // R28_H
  (unsigned char)'\x1D',  // R29
  (unsigned char)'\x1D',  // R29_H
  (unsigned char)'\x1E',  // R30
  (unsigned char)'\x1E',  // R30_H
  (unsigned char)'\x1F',  // R31
  (unsigned char)'\x1F',  // R31_H
  (unsigned char)'\xA',  // R10
  (unsigned char)'\xA',  // R10_H
  (unsigned char)'\xB',  // R11
  (unsigned char)'\xB',  // R11_H
  (unsigned char)'\xC',  // R12
  (unsigned char)'\xC',  // R12_H
  (unsigned char)'\xD',  // R13
  (unsigned char)'\xD',  // R13_H
  (unsigned char)'\xE',  // R14
  (unsigned char)'\xE',  // R14_H
  (unsigned char)'\xF',  // R15
  (unsigned char)'\xF',  // R15_H
  (unsigned char)'\x10',  // R16
  (unsigned char)'\x10',  // R16_H
  (unsigned char)'\x11',  // R17
  (unsigned char)'\x11',  // R17_H
  (unsigned char)'\x9',  // R9
  (unsigned char)'\x9',  // R9_H
  (unsigned char)'\x12',  // R18
  (unsigned char)'\x12',  // R18_H
  (unsigned char)'\x13',  // R19
  (unsigned char)'\x13',  // R19_H
  (unsigned char)'\x14',  // R20
  (unsigned char)'\x14',  // R20_H
  (unsigned char)'\x15',  // R21
  (unsigned char)'\x15',  // R21_H
  (unsigned char)'\x16',  // R22
  (unsigned char)'\x16',  // R22_H
  (unsigned char)'\x18',  // R24
  (unsigned char)'\x18',  // R24_H
  (unsigned char)'\x19',  // R25
  (unsigned char)'\x19',  // R25_H
  (unsigned char)'\x1A',  // R26
  (unsigned char)'\x1A',  // R26_H
  (unsigned char)'\x17',  // R23
  (unsigned char)'\x17',  // R23_H
  (unsigned char)'\x1B',  // R27
  (unsigned char)'\x1B',  // R27_H
  (unsigned char)'\x4',  // R4
  (unsigned char)'\x4',  // R4_H
  (unsigned char)'\x8',  // R8
  (unsigned char)'\x8',  // R8_H
  (unsigned char)'\x0',  // R0
  (unsigned char)'\x0',  // R0_H
  (unsigned char)'\x1',  // R1
  (unsigned char)'\x1',  // R1_H
  (unsigned char)'\x2',  // R2
  (unsigned char)'\x2',  // R2_H
  (unsigned char)'\x3',  // R3
  (unsigned char)'\x3',  // R3_H
  (unsigned char)'\x0',  // F0
  (unsigned char)'\x0',  // F0_H
  (unsigned char)'\x1',  // F1
  (unsigned char)'\x1',  // F1_H
  (unsigned char)'\x2',  // F2
  (unsigned char)'\x2',  // F2_H
  (unsigned char)'\x3',  // F3
  (unsigned char)'\x3',  // F3_H
  (unsigned char)'\x4',  // F4
  (unsigned char)'\x4',  // F4_H
  (unsigned char)'\x5',  // F5
  (unsigned char)'\x5',  // F5_H
  (unsigned char)'\x6',  // F6
  (unsigned char)'\x6',  // F6_H
  (unsigned char)'\x7',  // F7
  (unsigned char)'\x7',  // F7_H
  (unsigned char)'\x1C',  // F28
  (unsigned char)'\x1C',  // F28_H
  (unsigned char)'\x1D',  // F29
  (unsigned char)'\x1D',  // F29_H
  (unsigned char)'\x1E',  // F30
  (unsigned char)'\x1E',  // F30_H
  (unsigned char)'\x1F',  // F31
  (unsigned char)'\x1F',  // F31_H
  (unsigned char)'\xA',  // F10
  (unsigned char)'\xA',  // F10_H
  (unsigned char)'\xB',  // F11
  (unsigned char)'\xB',  // F11_H
  (unsigned char)'\xC',  // F12
  (unsigned char)'\xC',  // F12_H
  (unsigned char)'\xD',  // F13
  (unsigned char)'\xD',  // F13_H
  (unsigned char)'\xE',  // F14
  (unsigned char)'\xE',  // F14_H
  (unsigned char)'\xF',  // F15
  (unsigned char)'\xF',  // F15_H
  (unsigned char)'\x10',  // F16
  (unsigned char)'\x10',  // F16_H
  (unsigned char)'\x11',  // F17
  (unsigned char)'\x11',  // F17_H
  (unsigned char)'\x8',  // F8
  (unsigned char)'\x8',  // F8_H
  (unsigned char)'\x9',  // F9
  (unsigned char)'\x9',  // F9_H
  (unsigned char)'\x12',  // F18
  (unsigned char)'\x12',  // F18_H
  (unsigned char)'\x13',  // F19
  (unsigned char)'\x13',  // F19_H
  (unsigned char)'\x14',  // F20
  (unsigned char)'\x14',  // F20_H
  (unsigned char)'\x15',  // F21
  (unsigned char)'\x15',  // F21_H
  (unsigned char)'\x16',  // F22
  (unsigned char)'\x16',  // F22_H
  (unsigned char)'\x17',  // F23
  (unsigned char)'\x17',  // F23_H
  (unsigned char)'\x18',  // F24
  (unsigned char)'\x18',  // F24_H
  (unsigned char)'\x19',  // F25
  (unsigned char)'\x19',  // F25_H
  (unsigned char)'\x1A',  // F26
  (unsigned char)'\x1A',  // F26_H
  (unsigned char)'\x1B',  // F27
  (unsigned char)'\x1B',  // F27_H
  (unsigned char)'\x0',  // V0
  (unsigned char)'\x0',  // V0_H
  (unsigned char)'\x0',  // V0_J
  (unsigned char)'\x0',  // V0_K
  (unsigned char)'\x1',  // V1
  (unsigned char)'\x1',  // V1_H
  (unsigned char)'\x1',  // V1_J
  (unsigned char)'\x1',  // V1_K
  (unsigned char)'\x2',  // V2
  (unsigned char)'\x2',  // V2_H
  (unsigned char)'\x2',  // V2_J
  (unsigned char)'\x2',  // V2_K
  (unsigned char)'\x3',  // V3
  (unsigned char)'\x3',  // V3_H
  (unsigned char)'\x3',  // V3_J
  (unsigned char)'\x3',  // V3_K
  (unsigned char)'\x4',  // V4
  (unsigned char)'\x4',  // V4_H
  (unsigned char)'\x4',  // V4_J
  (unsigned char)'\x4',  // V4_K
  (unsigned char)'\x5',  // V5
  (unsigned char)'\x5',  // V5_H
  (unsigned char)'\x5',  // V5_J
  (unsigned char)'\x5',  // V5_K
  (unsigned char)'\x6',  // V6
  (unsigned char)'\x6',  // V6_H
  (unsigned char)'\x6',  // V6_J
  (unsigned char)'\x6',  // V6_K
  (unsigned char)'\x7',  // V7
  (unsigned char)'\x7',  // V7_H
  (unsigned char)'\x7',  // V7_J
  (unsigned char)'\x7',  // V7_K
  (unsigned char)'\x8',  // V8
  (unsigned char)'\x8',  // V8_H
  (unsigned char)'\x8',  // V8_J
  (unsigned char)'\x8',  // V8_K
  (unsigned char)'\x9',  // V9
  (unsigned char)'\x9',  // V9_H
  (unsigned char)'\x9',  // V9_J
  (unsigned char)'\x9',  // V9_K
  (unsigned char)'\xA',  // V10
  (unsigned char)'\xA',  // V10_H
  (unsigned char)'\xA',  // V10_J
  (unsigned char)'\xA',  // V10_K
  (unsigned char)'\xB',  // V11
  (unsigned char)'\xB',  // V11_H
  (unsigned char)'\xB',  // V11_J
  (unsigned char)'\xB',  // V11_K
  (unsigned char)'\xC',  // V12
  (unsigned char)'\xC',  // V12_H
  (unsigned char)'\xC',  // V12_J
  (unsigned char)'\xC',  // V12_K
  (unsigned char)'\xD',  // V13
  (unsigned char)'\xD',  // V13_H
  (unsigned char)'\xD',  // V13_J
  (unsigned char)'\xD',  // V13_K
  (unsigned char)'\xE',  // V14
  (unsigned char)'\xE',  // V14_H
  (unsigned char)'\xE',  // V14_J
  (unsigned char)'\xE',  // V14_K
  (unsigned char)'\xF',  // V15
  (unsigned char)'\xF',  // V15_H
  (unsigned char)'\xF',  // V15_J
  (unsigned char)'\xF',  // V15_K
  (unsigned char)'\x10',  // V16
  (unsigned char)'\x10',  // V16_H
  (unsigned char)'\x10',  // V16_J
  (unsigned char)'\x10',  // V16_K
  (unsigned char)'\x11',  // V17
  (unsigned char)'\x11',  // V17_H
  (unsigned char)'\x11',  // V17_J
  (unsigned char)'\x11',  // V17_K
  (unsigned char)'\x12',  // V18
  (unsigned char)'\x12',  // V18_H
  (unsigned char)'\x12',  // V18_J
  (unsigned char)'\x12',  // V18_K
  (unsigned char)'\x13',  // V19
  (unsigned char)'\x13',  // V19_H
  (unsigned char)'\x13',  // V19_J
  (unsigned char)'\x13',  // V19_K
  (unsigned char)'\x14',  // V20
  (unsigned char)'\x14',  // V20_H
  (unsigned char)'\x14',  // V20_J
  (unsigned char)'\x14',  // V20_K
  (unsigned char)'\x15',  // V21
  (unsigned char)'\x15',  // V21_H
  (unsigned char)'\x15',  // V21_J
  (unsigned char)'\x15',  // V21_K
  (unsigned char)'\x16',  // V22
  (unsigned char)'\x16',  // V22_H
  (unsigned char)'\x16',  // V22_J
  (unsigned char)'\x16',  // V22_K
  (unsigned char)'\x17',  // V23
  (unsigned char)'\x17',  // V23_H
  (unsigned char)'\x17',  // V23_J
  (unsigned char)'\x17',  // V23_K
  (unsigned char)'\x18',  // V24
  (unsigned char)'\x18',  // V24_H
  (unsigned char)'\x18',  // V24_J
  (unsigned char)'\x18',  // V24_K
  (unsigned char)'\x19',  // V25
  (unsigned char)'\x19',  // V25_H
  (unsigned char)'\x19',  // V25_J
  (unsigned char)'\x19',  // V25_K
  (unsigned char)'\x1A',  // V26
  (unsigned char)'\x1A',  // V26_H
  (unsigned char)'\x1A',  // V26_J
  (unsigned char)'\x1A',  // V26_K
  (unsigned char)'\x1B',  // V27
  (unsigned char)'\x1B',  // V27_H
  (unsigned char)'\x1B',  // V27_J
  (unsigned char)'\x1B',  // V27_K
  (unsigned char)'\x1C',  // V28
  (unsigned char)'\x1C',  // V28_H
  (unsigned char)'\x1C',  // V28_J
  (unsigned char)'\x1C',  // V28_K
  (unsigned char)'\x1D',  // V29
  (unsigned char)'\x1D',  // V29_H
  (unsigned char)'\x1D',  // V29_J
  (unsigned char)'\x1D',  // V29_K
  (unsigned char)'\x1E',  // V30
  (unsigned char)'\x1E',  // V30_H
  (unsigned char)'\x1E',  // V30_J
  (unsigned char)'\x1E',  // V30_K
  (unsigned char)'\x1F',  // V31
  (unsigned char)'\x1F',  // V31_H
  (unsigned char)'\x1F',  // V31_J
  (unsigned char)'\x1F',  // V31_K
  (unsigned char)'\x6' // no trailing comma  // RFLAGS
};


//------------------Define classes derived from MachOper---------------------
MachOper  *labelOper::clone() const {
  return  new labelOper(_label, _block_num);
}
uint labelOper::opcode() const { return LABEL; }

const RegMask *sRegIOper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &(Compile::current()->FIRST_STACK_mask());
}

const RegMask *sRegPOper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &(Compile::current()->FIRST_STACK_mask());
}

const RegMask *sRegFOper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &(Compile::current()->FIRST_STACK_mask());
}

const RegMask *sRegDOper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &(Compile::current()->FIRST_STACK_mask());
}

const RegMask *sRegLOper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &(Compile::current()->FIRST_STACK_mask());
}

MachOper  *methodOper::clone() const {
  return  new methodOper(_method);
}
uint methodOper::opcode() const { return METHOD; }

const RegMask *iRegIOper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &ANY_REG32_mask();
}

const RegMask *iRegINoSpOper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &NO_SPECIAL_REG32_mask();
}

const RegMask *iRegI_R10Oper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &INT_R10_REG_mask();
}

const RegMask *iRegI_R12Oper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &INT_R12_REG_mask();
}

const RegMask *iRegI_R13Oper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &INT_R13_REG_mask();
}

const RegMask *iRegI_R14Oper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &INT_R14_REG_mask();
}

const RegMask *iRegLOper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &ANY_REG_mask();
}

const RegMask *iRegLNoSpOper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &NO_SPECIAL_REG_mask();
}

const RegMask *iRegL_R28Oper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &R28_REG_mask();
}

const RegMask *iRegL_R29Oper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &R29_REG_mask();
}

const RegMask *iRegL_R30Oper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &R30_REG_mask();
}

const RegMask *iRegPOper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &PTR_REG_mask();
}

const RegMask *iRegPNoSpOper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &NO_SPECIAL_PTR_REG_mask();
}

const RegMask *iRegP_R10Oper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &R10_REG_mask();
}

const RegMask *iRegP_R11Oper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &R11_REG_mask();
}

const RegMask *iRegP_R12Oper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &R12_REG_mask();
}

const RegMask *iRegP_R13Oper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &R13_REG_mask();
}

const RegMask *iRegP_R14Oper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &R14_REG_mask();
}

const RegMask *iRegP_R15Oper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &R15_REG_mask();
}

const RegMask *iRegP_R16Oper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &R16_REG_mask();
}

const RegMask *iRegP_R28Oper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &R28_REG_mask();
}

const RegMask *iRegP_R30Oper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &R30_REG_mask();
}

const RegMask *iRegP_R31Oper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &R31_REG_mask();
}

const RegMask *iRegNOper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &ANY_REG32_mask();
}

const RegMask *iRegNNoSpOper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &NO_SPECIAL_REG32_mask();
}

const RegMask *iRegIHeapbaseOper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &HEAPBASE_REG_mask();
}

const RegMask *iRegL_R10Oper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &R10_REG_mask();
}

const RegMask *fRegFOper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &FLOAT_REG_mask();
}

const RegMask *fRegDOper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &DOUBLE_REG_mask();
}

const RegMask *vRegOper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &VECTORA_REG_mask();
}

const RegMask *vReg_V1Oper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &V1_REG_mask();
}

const RegMask *vReg_V2Oper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &V2_REG_mask();
}

const RegMask *vReg_V3Oper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &V3_REG_mask();
}

const RegMask *vReg_V4Oper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &V4_REG_mask();
}

const RegMask *vReg_V5Oper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &V5_REG_mask();
}

const RegMask *javaThread_RegPOper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &JAVA_THREAD_REG_mask();
}

const RegMask *indirectOper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &PTR_REG_mask();
}

const RegMask *indOffIOper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &PTR_REG_mask();
}

const RegMask *indOffLOper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &PTR_REG_mask();
}

const RegMask *indirectNOper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &ANY_REG32_mask();
}

const RegMask *indOffINOper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &ANY_REG32_mask();
}

const RegMask *indOffLNOper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &ANY_REG32_mask();
}

const RegMask *thread_anchor_pcOper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &PTR_REG_mask();
}

const RegMask *stackSlotIOper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &(Compile::current()->FIRST_STACK_mask());
}

const RegMask *stackSlotFOper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &(Compile::current()->FIRST_STACK_mask());
}

const RegMask *stackSlotDOper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &(Compile::current()->FIRST_STACK_mask());
}

const RegMask *stackSlotLOper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &(Compile::current()->FIRST_STACK_mask());
}

const RegMask *iRegL2IOper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &ANY_REG_mask();
}

const RegMask *rFlagsRegOper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &REG_FLAGS_mask();
}

const RegMask *inline_cache_RegPOper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &METHOD_REG_mask();
}

const RegMask *pRegGovOper::in_RegMask(int index) const {
  assert(0 <= index && index < 1, "index out of range");
  return &PR_REG_mask();
}

//------------------Define members for classes derived from MachNode----------
// Build short branch version of this instruction
MachNode *far_cmpI_branchNode::short_branch_version() {
  cmpI_branchNode *node = new cmpI_branchNode();
  node->_prob = _prob;
  node->_fcnt = _fcnt;

  // Copy _idx, inputs and operands to new node
  fill_new_machnode(node);
  return node;
}

// Build short branch version of this instruction
MachNode *far_cmpI_loopNode::short_branch_version() {
  cmpI_loopNode *node = new cmpI_loopNode();
  node->_prob = _prob;
  node->_fcnt = _fcnt;

  // Copy _idx, inputs and operands to new node
  fill_new_machnode(node);
  return node;
}

// Build short branch version of this instruction
MachNode *far_cmpU_branchNode::short_branch_version() {
  cmpU_branchNode *node = new cmpU_branchNode();
  node->_prob = _prob;
  node->_fcnt = _fcnt;

  // Copy _idx, inputs and operands to new node
  fill_new_machnode(node);
  return node;
}

// Build short branch version of this instruction
MachNode *far_cmpU_loopNode::short_branch_version() {
  cmpU_loopNode *node = new cmpU_loopNode();
  node->_prob = _prob;
  node->_fcnt = _fcnt;

  // Copy _idx, inputs and operands to new node
  fill_new_machnode(node);
  return node;
}

// Build short branch version of this instruction
MachNode *far_cmpL_branchNode::short_branch_version() {
  cmpL_branchNode *node = new cmpL_branchNode();
  node->_prob = _prob;
  node->_fcnt = _fcnt;

  // Copy _idx, inputs and operands to new node
  fill_new_machnode(node);
  return node;
}

// Build short branch version of this instruction
MachNode *far_cmpLloopNode::short_branch_version() {
  cmpL_loopNode *node = new cmpL_loopNode();
  node->_prob = _prob;
  node->_fcnt = _fcnt;

  // Copy _idx, inputs and operands to new node
  fill_new_machnode(node);
  return node;
}

// Build short branch version of this instruction
MachNode *far_cmpUL_branchNode::short_branch_version() {
  cmpUL_branchNode *node = new cmpUL_branchNode();
  node->_prob = _prob;
  node->_fcnt = _fcnt;

  // Copy _idx, inputs and operands to new node
  fill_new_machnode(node);
  return node;
}

// Build short branch version of this instruction
MachNode *far_cmpUL_loopNode::short_branch_version() {
  cmpUL_loopNode *node = new cmpUL_loopNode();
  node->_prob = _prob;
  node->_fcnt = _fcnt;

  // Copy _idx, inputs and operands to new node
  fill_new_machnode(node);
  return node;
}

// Build short branch version of this instruction
MachNode *far_cmpP_branchNode::short_branch_version() {
  cmpP_branchNode *node = new cmpP_branchNode();
  node->_prob = _prob;
  node->_fcnt = _fcnt;

  // Copy _idx, inputs and operands to new node
  fill_new_machnode(node);
  return node;
}

// Build short branch version of this instruction
MachNode *far_cmpP_loopNode::short_branch_version() {
  cmpP_loopNode *node = new cmpP_loopNode();
  node->_prob = _prob;
  node->_fcnt = _fcnt;

  // Copy _idx, inputs and operands to new node
  fill_new_machnode(node);
  return node;
}

// Build short branch version of this instruction
MachNode *far_cmpN_branchNode::short_branch_version() {
  cmpN_branchNode *node = new cmpN_branchNode();
  node->_prob = _prob;
  node->_fcnt = _fcnt;

  // Copy _idx, inputs and operands to new node
  fill_new_machnode(node);
  return node;
}

// Build short branch version of this instruction
MachNode *far_cmpN_loopNode::short_branch_version() {
  cmpN_loopNode *node = new cmpN_loopNode();
  node->_prob = _prob;
  node->_fcnt = _fcnt;

  // Copy _idx, inputs and operands to new node
  fill_new_machnode(node);
  return node;
}

// Build short branch version of this instruction
MachNode *far_cmpF_branchNode::short_branch_version() {
  cmpF_branchNode *node = new cmpF_branchNode();
  node->_prob = _prob;
  node->_fcnt = _fcnt;

  // Copy _idx, inputs and operands to new node
  fill_new_machnode(node);
  return node;
}

// Build short branch version of this instruction
MachNode *far_cmpF_loopNode::short_branch_version() {
  cmpF_loopNode *node = new cmpF_loopNode();
  node->_prob = _prob;
  node->_fcnt = _fcnt;

  // Copy _idx, inputs and operands to new node
  fill_new_machnode(node);
  return node;
}

// Build short branch version of this instruction
MachNode *far_cmpD_branchNode::short_branch_version() {
  cmpD_branchNode *node = new cmpD_branchNode();
  node->_prob = _prob;
  node->_fcnt = _fcnt;

  // Copy _idx, inputs and operands to new node
  fill_new_machnode(node);
  return node;
}

// Build short branch version of this instruction
MachNode *far_cmpD_loopNode::short_branch_version() {
  cmpD_loopNode *node = new cmpD_loopNode();
  node->_prob = _prob;
  node->_fcnt = _fcnt;

  // Copy _idx, inputs and operands to new node
  fill_new_machnode(node);
  return node;
}

// Build short branch version of this instruction
MachNode *far_cmpI_reg_imm0_branchNode::short_branch_version() {
  cmpI_reg_imm0_branchNode *node = new cmpI_reg_imm0_branchNode();
  node->_prob = _prob;
  node->_fcnt = _fcnt;

  // Copy _idx, inputs and operands to new node
  fill_new_machnode(node);
  return node;
}

// Build short branch version of this instruction
MachNode *far_cmpI_reg_imm0_loopNode::short_branch_version() {
  cmpI_reg_imm0_loopNode *node = new cmpI_reg_imm0_loopNode();
  node->_prob = _prob;
  node->_fcnt = _fcnt;

  // Copy _idx, inputs and operands to new node
  fill_new_machnode(node);
  return node;
}

// Build short branch version of this instruction
MachNode *far_cmpUEqNeLeGt_imm0_branchNode::short_branch_version() {
  cmpUEqNeLeGt_reg_imm0_branchNode *node = new cmpUEqNeLeGt_reg_imm0_branchNode();
  node->_prob = _prob;
  node->_fcnt = _fcnt;

  // Copy _idx, inputs and operands to new node
  fill_new_machnode(node);
  return node;
}

// Build short branch version of this instruction
MachNode *far_cmpUEqNeLeGt_reg_imm0_loopNode::short_branch_version() {
  cmpUEqNeLeGt_reg_imm0_loopNode *node = new cmpUEqNeLeGt_reg_imm0_loopNode();
  node->_prob = _prob;
  node->_fcnt = _fcnt;

  // Copy _idx, inputs and operands to new node
  fill_new_machnode(node);
  return node;
}

// Build short branch version of this instruction
MachNode *far_cmpL_reg_imm0_branchNode::short_branch_version() {
  cmpL_reg_imm0_branchNode *node = new cmpL_reg_imm0_branchNode();
  node->_prob = _prob;
  node->_fcnt = _fcnt;

  // Copy _idx, inputs and operands to new node
  fill_new_machnode(node);
  return node;
}

// Build short branch version of this instruction
MachNode *far_cmpL_reg_imm0_loopNode::short_branch_version() {
  cmpL_reg_imm0_loopNode *node = new cmpL_reg_imm0_loopNode();
  node->_prob = _prob;
  node->_fcnt = _fcnt;

  // Copy _idx, inputs and operands to new node
  fill_new_machnode(node);
  return node;
}

// Build short branch version of this instruction
MachNode *far_cmpULEqNeLeGt_reg_imm0_branchNode::short_branch_version() {
  cmpULEqNeLeGt_reg_imm0_branchNode *node = new cmpULEqNeLeGt_reg_imm0_branchNode();
  node->_prob = _prob;
  node->_fcnt = _fcnt;

  // Copy _idx, inputs and operands to new node
  fill_new_machnode(node);
  return node;
}

// Build short branch version of this instruction
MachNode *far_cmpULEqNeLeGt_reg_imm0_loopNode::short_branch_version() {
  cmpULEqNeLeGt_reg_imm0_loopNode *node = new cmpULEqNeLeGt_reg_imm0_loopNode();
  node->_prob = _prob;
  node->_fcnt = _fcnt;

  // Copy _idx, inputs and operands to new node
  fill_new_machnode(node);
  return node;
}

// Build short branch version of this instruction
MachNode *far_cmpP_imm0_branchNode::short_branch_version() {
  cmpP_imm0_branchNode *node = new cmpP_imm0_branchNode();
  node->_prob = _prob;
  node->_fcnt = _fcnt;

  // Copy _idx, inputs and operands to new node
  fill_new_machnode(node);
  return node;
}

// Build short branch version of this instruction
MachNode *far_cmpP_imm0_loopNode::short_branch_version() {
  cmpP_imm0_loopNode *node = new cmpP_imm0_loopNode();
  node->_prob = _prob;
  node->_fcnt = _fcnt;

  // Copy _idx, inputs and operands to new node
  fill_new_machnode(node);
  return node;
}

// Build short branch version of this instruction
MachNode *far_cmpN_imm0_branchNode::short_branch_version() {
  cmpN_imm0_branchNode *node = new cmpN_imm0_branchNode();
  node->_prob = _prob;
  node->_fcnt = _fcnt;

  // Copy _idx, inputs and operands to new node
  fill_new_machnode(node);
  return node;
}

// Build short branch version of this instruction
MachNode *far_cmpN_imm0_loopNode::short_branch_version() {
  cmpN_imm0_loopNode *node = new cmpN_imm0_loopNode();
  node->_prob = _prob;
  node->_fcnt = _fcnt;

  // Copy _idx, inputs and operands to new node
  fill_new_machnode(node);
  return node;
}

// Build short branch version of this instruction
MachNode *far_cmpP_narrowOop_imm0_branchNode::short_branch_version() {
  cmpP_narrowOop_imm0_branchNode *node = new cmpP_narrowOop_imm0_branchNode();
  node->_prob = _prob;
  node->_fcnt = _fcnt;

  // Copy _idx, inputs and operands to new node
  fill_new_machnode(node);
  return node;
}

// Build short branch version of this instruction
MachNode *far_cmpP_narrowOop_imm0_loopNode::short_branch_version() {
  cmpP_narrowOop_imm0_loopNode *node = new cmpP_narrowOop_imm0_loopNode();
  node->_prob = _prob;
  node->_fcnt = _fcnt;

  // Copy _idx, inputs and operands to new node
  fill_new_machnode(node);
  return node;
}


// Copy _idx, inputs and operands to new node
void MachNode::fill_new_machnode(MachNode* node) const {
  // New node must use same node index
  node->set_idx( _idx );
  // Copy machine-independent inputs
  for( uint j = 0; j < req(); j++ ) {
    node->add_req(in(j));
  }
  // Copy my operands, except for cisc position
  int nopnds = num_opnds();
  assert( node->num_opnds() == (uint)nopnds, "Must have same number of operands");
  MachOper **to = node->_opnds;
  for( int i = 0; i < nopnds; i++ ) {
    if( i != cisc_operand() ) 
      to[i] = _opnds[i]->clone();
  }
}

void branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(1));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(1));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void cmpFlag_branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(3));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void cmpFlag_branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(3));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void cmpI_branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void cmpI_branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void cmpI_loopNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void cmpI_loopNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void cmpU_branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void cmpU_branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void cmpU_loopNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void cmpU_loopNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void cmpL_branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void cmpL_branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void cmpL_loopNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void cmpL_loopNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void cmpUL_branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void cmpUL_branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void cmpUL_loopNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void cmpUL_loopNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void cmpP_branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void cmpP_branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void cmpP_loopNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void cmpP_loopNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void cmpN_branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void cmpN_branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void cmpN_loopNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void cmpN_loopNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void cmpF_branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void cmpF_branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void cmpF_loopNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void cmpF_loopNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void cmpD_branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void cmpD_branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void cmpD_loopNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void cmpD_loopNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void cmpI_reg_imm0_branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void cmpI_reg_imm0_branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void cmpI_reg_imm0_loopNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void cmpI_reg_imm0_loopNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void cmpUEqNeLeGt_reg_imm0_branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void cmpUEqNeLeGt_reg_imm0_branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void cmpUEqNeLeGt_reg_imm0_loopNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void cmpUEqNeLeGt_reg_imm0_loopNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void cmpL_reg_imm0_branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void cmpL_reg_imm0_branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void cmpL_reg_imm0_loopNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void cmpL_reg_imm0_loopNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void cmpULEqNeLeGt_reg_imm0_branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void cmpULEqNeLeGt_reg_imm0_branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void cmpULEqNeLeGt_reg_imm0_loopNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void cmpULEqNeLeGt_reg_imm0_loopNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void cmpP_imm0_branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void cmpP_imm0_branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void cmpP_imm0_loopNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void cmpP_imm0_loopNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void cmpN_imm0_branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void cmpN_imm0_branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void cmpN_imm0_loopNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void cmpN_imm0_loopNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void cmpP_narrowOop_imm0_branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void cmpP_narrowOop_imm0_branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void cmpP_narrowOop_imm0_loopNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void cmpP_narrowOop_imm0_loopNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpFlag_branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(3));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpFlag_branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(3));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpI_branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpI_branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpI_loopNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpI_loopNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpU_branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpU_branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpU_loopNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpU_loopNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpL_branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpL_branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpLloopNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpLloopNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpUL_branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpUL_branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpUL_loopNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpUL_loopNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpP_branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpP_branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpP_loopNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpP_loopNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpN_branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpN_branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpN_loopNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpN_loopNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpF_branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpF_branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpF_loopNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpF_loopNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpD_branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpD_branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpD_loopNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpD_loopNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpI_reg_imm0_branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpI_reg_imm0_branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpI_reg_imm0_loopNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpI_reg_imm0_loopNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpUEqNeLeGt_imm0_branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpUEqNeLeGt_imm0_branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpUEqNeLeGt_reg_imm0_loopNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpUEqNeLeGt_reg_imm0_loopNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpULtGe_reg_imm0_branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpULtGe_reg_imm0_branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpULtGe_reg_imm0_loopNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpULtGe_reg_imm0_loopNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpL_reg_imm0_branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpL_reg_imm0_branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpL_reg_imm0_loopNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpL_reg_imm0_loopNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpULEqNeLeGt_reg_imm0_branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpULEqNeLeGt_reg_imm0_branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpULEqNeLeGt_reg_imm0_loopNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpULEqNeLeGt_reg_imm0_loopNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpULLtGe_reg_imm0_branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpULLtGe_reg_imm0_branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpULLtGe_reg_imm0_loopNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpULLtGe_reg_imm0_loopNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpP_imm0_branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpP_imm0_branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpP_imm0_loopNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpP_imm0_loopNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpN_imm0_branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpN_imm0_branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpN_imm0_loopNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpN_imm0_loopNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpP_narrowOop_imm0_branchNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpP_narrowOop_imm0_branchNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void far_cmpP_narrowOop_imm0_loopNode::label_set( Label* label, uint block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  oper->_label     = label;
  oper->_block_num = block_num;
}
void far_cmpP_narrowOop_imm0_loopNode::save_label( Label** label, uint* block_num ) {
  labelOper* oper  = (labelOper*)(opnd_array(4));
  *label = oper->_label;
  *block_num = oper->_block_num;
}
void CallStaticJavaDirectNode::method_set( intptr_t method ) {
  ((methodOper*)opnd_array(1))->_method = method;
}

void CallDynamicJavaDirectNode::method_set( intptr_t method ) {
  ((methodOper*)opnd_array(1))->_method = method;
}

void CallRuntimeDirectNode::method_set( intptr_t method ) {
  ((methodOper*)opnd_array(1))->_method = method;
}

void CallLeafDirectNode::method_set( intptr_t method ) {
  ((methodOper*)opnd_array(1))->_method = method;
}

void CallLeafNoFPDirectNode::method_set( intptr_t method ) {
  ((methodOper*)opnd_array(1))->_method = method;
}

int loadBNode::reloc() const {
  return 1;
}

int loadB2LNode::reloc() const {
  return 1;
}

int loadUBNode::reloc() const {
  return 1;
}

int loadUB2LNode::reloc() const {
  return 1;
}

int loadSNode::reloc() const {
  return 1;
}

int loadS2LNode::reloc() const {
  return 1;
}

int loadUSNode::reloc() const {
  return 1;
}

int loadUS2LNode::reloc() const {
  return 1;
}

int loadINode::reloc() const {
  return 1;
}

int loadI2LNode::reloc() const {
  return 1;
}

int loadUI2LNode::reloc() const {
  return 1;
}

int loadLNode::reloc() const {
  return 1;
}

int loadRangeNode::reloc() const {
  return 1;
}

int loadPNode::reloc() const {
  return 1;
}

int loadNNode::reloc() const {
  return 1;
}

int loadKlassNode::reloc() const {
  return 1;
}

int loadNKlassNode::reloc() const {
  return 1;
}

int loadFNode::reloc() const {
  return 1;
}

int loadDNode::reloc() const {
  return 1;
}

int loadConPNode::reloc() const {
  return 1;
}

int loadConP0Node::reloc() const {
  return 1;
}

int loadConP1Node::reloc() const {
  return 1;
}

int loadByteMapBaseNode::reloc() const {
  return 1;
}

int loadConFNode::reloc() const {
  return 2;
}

int loadConF0Node::reloc() const {
  return 2;
}

int loadConDNode::reloc() const {
  return 2;
}

int loadConD0Node::reloc() const {
  return 2;
}

int storeimmCM0Node::reloc() const {
  return 2;
}

int storeimmCM0_orderedNode::reloc() const {
  return 2;
}

int storeBNode::reloc() const {
  return 3;
}

int storeimmB0Node::reloc() const {
  return 2;
}

int storeCNode::reloc() const {
  return 3;
}

int storeimmC0Node::reloc() const {
  return 2;
}

int storeINode::reloc() const {
  return 3;
}

int storeimmI0Node::reloc() const {
  return 2;
}

int storeLNode::reloc() const {
  return 2;
}

int storeimmL0Node::reloc() const {
  return 2;
}

int storePNode::reloc() const {
  return 2;
}

int storeimmP0Node::reloc() const {
  return 3;
}

int storeNNode::reloc() const {
  return 2;
}

int storeImmN0Node::reloc() const {
  return 2;
}

int storeFNode::reloc() const {
  return 2;
}

int storeDNode::reloc() const {
  return 2;
}

int storeNKlassNode::reloc() const {
  return 2;
}

int get_and_addINode::reloc() const {
  return 1;
}

int get_and_addI_no_resNode::reloc() const {
  return 1;
}

int get_and_addIAcqNode::reloc() const {
  return 1;
}

int get_and_addI_no_resAcqNode::reloc() const {
  return 1;
}

int addI_reg_regNode::reloc() const {
  return 2;
}

int addI_reg_immNode::reloc() const {
  return 1;
}

int subI_reg_regNode::reloc() const {
  return 2;
}

int subI_reg_immNode::reloc() const {
  return 1;
}

int negI_regNode::reloc() const {
  return 1;
}

int mulINode::reloc() const {
  return 2;
}

int divINode::reloc() const {
  return 2;
}

int signExtractNode::reloc() const {
  return 1;
}

int modINode::reloc() const {
  return 2;
}

int lShiftI_reg_regNode::reloc() const {
  return 2;
}

int lShiftI_reg_immNode::reloc() const {
  return 1;
}

int urShiftI_reg_regNode::reloc() const {
  return 2;
}

int urShiftI_reg_immNode::reloc() const {
  return 1;
}

int rShiftI_reg_regNode::reloc() const {
  return 2;
}

int rShiftI_reg_immNode::reloc() const {
  return 1;
}

int lShiftL_reg_regNode::reloc() const {
  return 1;
}

int urShiftL_reg_regNode::reloc() const {
  return 1;
}

int rShiftL_reg_regNode::reloc() const {
  return 1;
}

int absI_regNode::reloc() const {
  return 1;
}

int bytes_reverse_intNode::reloc() const {
  return 1;
}

int bytes_reverse_unsigned_shortNode::reloc() const {
  return 1;
}

int bytes_reverse_shortNode::reloc() const {
  return 1;
}

int convI2L_reg_regNode::reloc() const {
  return 1;
}

int convI2UL_reg_regNode::reloc() const {
  return 1;
}

int convI2F_reg_regNode::reloc() const {
  return 1;
}

int convI2D_reg_regNode::reloc() const {
  return 1;
}

int cmpLTMask_reg_zeroNode::reloc() const {
  return 1;
}

int cmpP_imm0_branchNode::reloc() const {
  return 1;
}

int cmpP_imm0_loopNode::reloc() const {
  return 1;
}

int cmpP_narrowOop_imm0_branchNode::reloc() const {
  return 1;
}

int cmpP_narrowOop_imm0_loopNode::reloc() const {
  return 1;
}

int far_cmpP_imm0_branchNode::reloc() const {
  return 1;
}

int far_cmpP_imm0_loopNode::reloc() const {
  return 1;
}

int far_cmpP_narrowOop_imm0_branchNode::reloc() const {
  return 1;
}

int far_cmpP_narrowOop_imm0_loopNode::reloc() const {
  return 1;
}

int CallStaticJavaDirectNode::reloc() const {
  return 1;
}

int CallDynamicJavaDirectNode::reloc() const {
  return 1;
}

int CallRuntimeDirectNode::reloc() const {
  return 1;
}

int CallLeafDirectNode::reloc() const {
  return 1;
}

int CallLeafNoFPDirectNode::reloc() const {
  return 1;
}

int partialSubtypeCheckVsZeroNode::reloc() const {
  return 1;
}

int safePointNode::reloc() const {
  return 1;
}

int TailCalljmpIndNode::reloc() const {
  return 1;
}

int TailjmpIndNode::reloc() const {
  return 1;
}

int RethrowExceptionNode::reloc() const {
  return 1;
}

int RetNode::reloc() const {
  return 1;
}

int loadVNode::reloc() const {
  return 1;
}

int storeVNode::reloc() const {
  return 2;
}

int reduce_andINode::reloc() const {
  return 1;
}

int reduce_orINode::reloc() const {
  return 1;
}

int reduce_xorINode::reloc() const {
  return 1;
}

int reduce_addINode::reloc() const {
  return 1;
}

int vreduce_maxINode::reloc() const {
  return 1;
}

int vreduce_minINode::reloc() const {
  return 1;
}

int replicateBNode::reloc() const {
  return 1;
}

int replicateSNode::reloc() const {
  return 1;
}

int replicateINode::reloc() const {
  return 1;
}

int vshiftcntBNode::reloc() const {
  return 1;
}

int vshiftcntB_0Node::reloc() const {
  return 1;
}

int vshiftcntSNode::reloc() const {
  return 1;
}

int vshiftcntS_0Node::reloc() const {
  return 1;
}

int vshiftcntINode::reloc() const {
  return 1;
}

int vshiftcntI_0Node::reloc() const {
  return 1;
}

int vshiftcntLNode::reloc() const {
  return 1;
}

int vshiftcntL_0Node::reloc() const {
  return 1;
}

int convB2I_reg_reg_bNode::reloc() const {
  return 1;
}

int convI2S_reg_reg_bNode::reloc() const {
  return 1;
}

int convS2UI_reg_reg_bNode::reloc() const {
  return 1;
}

int convI2UL_reg_reg_bNode::reloc() const {
  return 1;
}

int bytes_reverse_int_bNode::reloc() const {
  return 1;
}

int bytes_reverse_unsigned_short_bNode::reloc() const {
  return 1;
}

int bytes_reverse_short_bNode::reloc() const {
  return 1;
}

int countLeadingZerosI_bNode::reloc() const {
  return 1;
}

int countTrailingZerosI_bNode::reloc() const {
  return 1;
}

int popCountI_bNode::reloc() const {
  return 1;
}

int zLoadPNode::reloc() const {
  return 1;
}


void loadBNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  {
    C2_MacroAssembler _masm(&cbuf);

#line 4502 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ lb(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 8935 "ad_riscv.cpp"
  }
}

void loadB2LNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  {
    C2_MacroAssembler _masm(&cbuf);

#line 4517 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ lb(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 8951 "ad_riscv.cpp"
  }
}

void loadUBNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  {
    C2_MacroAssembler _masm(&cbuf);

#line 4532 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ lbu(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 8967 "ad_riscv.cpp"
  }
}

void loadUB2LNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  {
    C2_MacroAssembler _masm(&cbuf);

#line 4547 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ lbu(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 8983 "ad_riscv.cpp"
  }
}

void loadSNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  {
    C2_MacroAssembler _masm(&cbuf);

#line 4562 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ lh(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 8999 "ad_riscv.cpp"
  }
}

void loadS2LNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  {
    C2_MacroAssembler _masm(&cbuf);

#line 4577 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ lh(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 9015 "ad_riscv.cpp"
  }
}

void loadUSNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  {
    C2_MacroAssembler _masm(&cbuf);

#line 4592 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ lhu(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 9031 "ad_riscv.cpp"
  }
}

void loadUS2LNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  {
    C2_MacroAssembler _masm(&cbuf);

#line 4607 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ lhu(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 9047 "ad_riscv.cpp"
  }
}

void loadINode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  {
    C2_MacroAssembler _masm(&cbuf);

#line 4622 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ lw(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 9063 "ad_riscv.cpp"
  }
}

void loadI2LNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  {
    C2_MacroAssembler _masm(&cbuf);

#line 4637 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ lw(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 9079 "ad_riscv.cpp"
  }
}

void loadUI2LNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// mask
  {
    C2_MacroAssembler _masm(&cbuf);

#line 4652 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ lwu(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 9096 "ad_riscv.cpp"
  }
}

void loadLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  {
    C2_MacroAssembler _masm(&cbuf);

#line 4667 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ ld(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 9112 "ad_riscv.cpp"
  }
}

void loadRangeNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  {
    C2_MacroAssembler _masm(&cbuf);

#line 4682 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ lwu(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 9128 "ad_riscv.cpp"
  }
}

void loadPNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  {
    C2_MacroAssembler _masm(&cbuf);

#line 4698 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ ld(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 9144 "ad_riscv.cpp"
  }
}

void loadNNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  {
    C2_MacroAssembler _masm(&cbuf);

#line 4713 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ lwu(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 9160 "ad_riscv.cpp"
  }
}

void loadKlassNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  {
    C2_MacroAssembler _masm(&cbuf);

#line 4728 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ ld(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 9176 "ad_riscv.cpp"
  }
}

void loadNKlassNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  {
    C2_MacroAssembler _masm(&cbuf);

#line 4743 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ lwu(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 9192 "ad_riscv.cpp"
  }
}

void loadFNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  {
    C2_MacroAssembler _masm(&cbuf);

#line 4758 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ flw(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */), Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 9208 "ad_riscv.cpp"
  }
}

void loadDNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  {
    C2_MacroAssembler _masm(&cbuf);

#line 4773 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fld(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */), Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 9224 "ad_riscv.cpp"
  }
}

void loadConINode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {

#line 2120 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    int64_t con = (int64_t)opnd_array(1)->constant();
    Register dst_reg = as_Register(opnd_array(0)->reg(ra_,this)/* dst */);
    __ mv(dst_reg, con);
  
#line 9242 "ad_riscv.cpp"
  }
}

void loadConLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {

#line 2120 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    int64_t con = (int64_t)opnd_array(1)->constantL();
    Register dst_reg = as_Register(opnd_array(0)->reg(ra_,this)/* dst */);
    __ mv(dst_reg, con);
  
#line 9260 "ad_riscv.cpp"
  }
}

void loadConPNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// con
  {

#line 2127 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    Register dst_reg = as_Register(opnd_array(0)->reg(ra_,this)/* dst */);
    address con = (address)opnd_array(1)->constant();
    if (con == NULL || con == (address)1) {
      ShouldNotReachHere();
    } else {
      relocInfo::relocType rtype = opnd_array(1)->constant_reloc();
      if (rtype == relocInfo::oop_type) {
        __ movoop(dst_reg, (jobject)con);
      } else if (rtype == relocInfo::metadata_type) {
        __ mov_metadata(dst_reg, (Metadata*)con);
      } else {
        assert(rtype == relocInfo::none, "unexpected reloc type");
        __ mv(dst_reg, opnd_array(1)->constant());
      }
    }
  
#line 9290 "ad_riscv.cpp"
  }
}

void loadConP0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// con
  {

#line 2170 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    Register dst_reg = as_Register(opnd_array(0)->reg(ra_,this)/* dst */);
    __ mv(dst_reg, zr);
  
#line 9307 "ad_riscv.cpp"
  }
}

void loadConP1Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// con
  {

#line 2146 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    Register dst_reg = as_Register(opnd_array(0)->reg(ra_,this)/* dst */);
    __ mv(dst_reg, 1);
  
#line 9324 "ad_riscv.cpp"
  }
}

void loadByteMapBaseNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// con
  {

#line 2152 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    __ load_byte_map_base(opnd_array(0)->as_Register(ra_,this)/* dst */);
  
#line 9340 "ad_riscv.cpp"
  }
}

void loadConNNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// con
  {

#line 2157 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    Register dst_reg = as_Register(opnd_array(0)->reg(ra_,this)/* dst */);
    address con = (address)opnd_array(1)->constant();
    if (con == NULL) {
      ShouldNotReachHere();
    } else {
      relocInfo::relocType rtype = opnd_array(1)->constant_reloc();
      assert(rtype == relocInfo::oop_type, "unexpected reloc type");
      __ set_narrow_oop(dst_reg, (jobject)con);
    }
  
#line 9364 "ad_riscv.cpp"
  }
}

void loadConN0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// con
  {

#line 2170 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    Register dst_reg = as_Register(opnd_array(0)->reg(ra_,this)/* dst */);
    __ mv(dst_reg, zr);
  
#line 9381 "ad_riscv.cpp"
  }
}

void loadConNKlassNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// con
  {

#line 2176 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    Register dst_reg = as_Register(opnd_array(0)->reg(ra_,this)/* dst */);
    address con = (address)opnd_array(1)->constant();
    if (con == NULL) {
      ShouldNotReachHere();
    } else {
      relocInfo::relocType rtype = opnd_array(1)->constant_reloc();
      assert(rtype == relocInfo::metadata_type, "unexpected reloc type");
      __ set_narrow_klass(dst_reg, (Klass *)con);
    }
  
#line 9405 "ad_riscv.cpp"
  }
}

void loadConFNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// con
  {
    C2_MacroAssembler _masm(&cbuf);

#line 4905 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ flw(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */), InternalAddress(__ code()->consts()->start() + constant_offset()));
  
#line 9421 "ad_riscv.cpp"
  }
}

void loadConFNode::eval_constant(Compile* C) {
  {

#line 4906 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"
    _constant = C->output()->constant_table().add(this, opnd_array(1));
#line 9430 "ad_riscv.cpp"
  }
}
void loadConF0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// con
  {
    C2_MacroAssembler _masm(&cbuf);

#line 4919 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fmv_w_x(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */), zr);
  
#line 9445 "ad_riscv.cpp"
  }
}

void loadConDNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// con
  {
    C2_MacroAssembler _masm(&cbuf);

#line 4935 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fld(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */), InternalAddress(__ code()->consts()->start() + constant_offset()));
  
#line 9461 "ad_riscv.cpp"
  }
}

void loadConDNode::eval_constant(Compile* C) {
  {

#line 4936 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"
    _constant = C->output()->constant_table().add(this, opnd_array(1));
#line 9470 "ad_riscv.cpp"
  }
}
void loadConD0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// con
  {
    C2_MacroAssembler _masm(&cbuf);

#line 4949 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fmv_d_x(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */), zr);
  
#line 9485 "ad_riscv.cpp"
  }
}

void storeimmCM0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  {
    C2_MacroAssembler _masm(&cbuf);

#line 4966 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ sb(zr, Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 9502 "ad_riscv.cpp"
  }
}

void storeimmCM0_orderedNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  {
    C2_MacroAssembler _masm(&cbuf);

#line 4983 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ membar(MacroAssembler::LoadStore | MacroAssembler::StoreStore);
    __ sb(zr, Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 9520 "ad_riscv.cpp"
  }
}

void storeBNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 4999 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ sb(as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src */), Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 9537 "ad_riscv.cpp"
  }
}

void storeimmB0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5013 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ sb(zr, Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 9554 "ad_riscv.cpp"
  }
}

void storeCNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5028 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ sh(as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src */), Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 9571 "ad_riscv.cpp"
  }
}

void storeimmC0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5042 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ sh(zr, Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 9588 "ad_riscv.cpp"
  }
}

void storeINode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5057 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ sw(as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src */), Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 9605 "ad_riscv.cpp"
  }
}

void storeimmI0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5071 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ sw(zr, Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 9622 "ad_riscv.cpp"
  }
}

void storeLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5086 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ sd(as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src */), Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 9639 "ad_riscv.cpp"
  }
}

void storeimmL0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5101 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ sd(zr, Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 9656 "ad_riscv.cpp"
  }
}

void storePNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5116 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ sd(as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src */), Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 9673 "ad_riscv.cpp"
  }
}

void storeimmP0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5131 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ sd(zr, Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 9690 "ad_riscv.cpp"
  }
}

void storeNNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5146 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ sw(as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src */), Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 9707 "ad_riscv.cpp"
  }
}

void storeImmN0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5160 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ sw(as_Register(R27_enc), Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 9724 "ad_riscv.cpp"
  }
}

void storeFNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5175 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fsw(as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* src */), Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 9741 "ad_riscv.cpp"
  }
}

void storeDNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5190 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fsd(as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* src */), Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 9758 "ad_riscv.cpp"
  }
}

void storeNKlassNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5205 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ sw(as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src */), Address(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1)));
  
#line 9775 "ad_riscv.cpp"
  }
}

void compareAndSwapBNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// res
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// tmp1
  unsigned idx6 = idx5 + opnd_array(5)->num_edges(); 	// tmp2
  unsigned idx7 = idx6 + opnd_array(6)->num_edges(); 	// tmp3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5232 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmpxchg_narrow_value(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int8,
                            Assembler::relaxed /* acquire */, Assembler::rl /* release */, opnd_array(4)->as_Register(ra_,this,idx4)/* res */,
                            true /* result as bool */, opnd_array(5)->as_Register(ra_,this,idx5)/* tmp1 */, opnd_array(6)->as_Register(ra_,this,idx6)/* tmp2 */, opnd_array(7)->as_Register(ra_,this,idx7)/* tmp3 */);
  
#line 9799 "ad_riscv.cpp"
  }
}

void compareAndSwapSNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// res
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// tmp1
  unsigned idx6 = idx5 + opnd_array(5)->num_edges(); 	// tmp2
  unsigned idx7 = idx6 + opnd_array(6)->num_edges(); 	// tmp3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5255 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmpxchg_narrow_value(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int16,
                            Assembler::relaxed /* acquire */, Assembler::rl /* release */, opnd_array(4)->as_Register(ra_,this,idx4)/* res */,
                            true /* result as bool */, opnd_array(5)->as_Register(ra_,this,idx5)/* tmp1 */, opnd_array(6)->as_Register(ra_,this,idx6)/* tmp2 */, opnd_array(7)->as_Register(ra_,this,idx7)/* tmp3 */);
  
#line 9823 "ad_riscv.cpp"
  }
}

void compareAndSwapINode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  {

#line 2189 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    __ cmpxchg(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int32,
               /*acquire*/ Assembler::relaxed, /*release*/ Assembler::rl, opnd_array(0)->as_Register(ra_,this)/* res */,
               /*result as bool*/ true);
  
#line 9843 "ad_riscv.cpp"
  }
}

void compareAndSwapLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  {

#line 2203 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    __ cmpxchg(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int64,
               /*acquire*/ Assembler::relaxed, /*release*/ Assembler::rl, opnd_array(0)->as_Register(ra_,this)/* res */,
               /*result as bool*/ true);
  
#line 9863 "ad_riscv.cpp"
  }
}

void compareAndSwapPNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  {

#line 2203 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    __ cmpxchg(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int64,
               /*acquire*/ Assembler::relaxed, /*release*/ Assembler::rl, opnd_array(0)->as_Register(ra_,this)/* res */,
               /*result as bool*/ true);
  
#line 9883 "ad_riscv.cpp"
  }
}

void compareAndSwapNNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  {

#line 2196 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    __ cmpxchg(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::uint32,
               /*acquire*/ Assembler::relaxed, /*release*/ Assembler::rl, opnd_array(0)->as_Register(ra_,this)/* res */,
               /*result as bool*/ true);
  
#line 9903 "ad_riscv.cpp"
  }
}

void compareAndSwapBAcqNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// res
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// tmp1
  unsigned idx6 = idx5 + opnd_array(5)->num_edges(); 	// tmp2
  unsigned idx7 = idx6 + opnd_array(6)->num_edges(); 	// tmp3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5347 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmpxchg_narrow_value(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int8,
                            Assembler::aq /* acquire */, Assembler::rl /* release */, opnd_array(4)->as_Register(ra_,this,idx4)/* res */,
                            true /* result as bool */, opnd_array(5)->as_Register(ra_,this,idx5)/* tmp1 */, opnd_array(6)->as_Register(ra_,this,idx6)/* tmp2 */, opnd_array(7)->as_Register(ra_,this,idx7)/* tmp3 */);
  
#line 9927 "ad_riscv.cpp"
  }
}

void compareAndSwapSAcqNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// res
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// tmp1
  unsigned idx6 = idx5 + opnd_array(5)->num_edges(); 	// tmp2
  unsigned idx7 = idx6 + opnd_array(6)->num_edges(); 	// tmp3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5372 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmpxchg_narrow_value(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int16,
                            Assembler::aq /* acquire */, Assembler::rl /* release */, opnd_array(4)->as_Register(ra_,this,idx4)/* res */,
                            true /* result as bool */, opnd_array(5)->as_Register(ra_,this,idx5)/* tmp1 */, opnd_array(6)->as_Register(ra_,this,idx6)/* tmp2 */, opnd_array(7)->as_Register(ra_,this,idx7)/* tmp3 */);
  
#line 9951 "ad_riscv.cpp"
  }
}

void compareAndSwapIAcqNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  {

#line 2210 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    __ cmpxchg(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int32,
               /*acquire*/ Assembler::aq, /*release*/ Assembler::rl, opnd_array(0)->as_Register(ra_,this)/* res */,
               /*result as bool*/ true);
  
#line 9971 "ad_riscv.cpp"
  }
}

void compareAndSwapLAcqNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  {

#line 2224 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    __ cmpxchg(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int64,
               /*acquire*/ Assembler::aq, /*release*/ Assembler::rl, opnd_array(0)->as_Register(ra_,this)/* res */,
               /*result as bool*/ true);
  
#line 9991 "ad_riscv.cpp"
  }
}

void compareAndSwapPAcqNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  {

#line 2224 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    __ cmpxchg(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int64,
               /*acquire*/ Assembler::aq, /*release*/ Assembler::rl, opnd_array(0)->as_Register(ra_,this)/* res */,
               /*result as bool*/ true);
  
#line 10011 "ad_riscv.cpp"
  }
}

void compareAndSwapNAcqNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  {

#line 2217 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    __ cmpxchg(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::uint32,
               /*acquire*/ Assembler::aq, /*release*/ Assembler::rl, opnd_array(0)->as_Register(ra_,this)/* res */,
               /*result as bool*/ true);
  
#line 10031 "ad_riscv.cpp"
  }
}

void compareAndExchangeBNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// res
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// tmp1
  unsigned idx6 = idx5 + opnd_array(5)->num_edges(); 	// tmp2
  unsigned idx7 = idx6 + opnd_array(6)->num_edges(); 	// tmp3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5472 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmpxchg_narrow_value(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int8,
                            /*acquire*/ Assembler::relaxed, /*release*/ Assembler::rl, opnd_array(4)->as_Register(ra_,this,idx4)/* res */,
                            /*result_as_bool*/ false, opnd_array(5)->as_Register(ra_,this,idx5)/* tmp1 */, opnd_array(6)->as_Register(ra_,this,idx6)/* tmp2 */, opnd_array(7)->as_Register(ra_,this,idx7)/* tmp3 */);
  
#line 10055 "ad_riscv.cpp"
  }
}

void compareAndExchangeSNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// res
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// tmp1
  unsigned idx6 = idx5 + opnd_array(5)->num_edges(); 	// tmp2
  unsigned idx7 = idx6 + opnd_array(6)->num_edges(); 	// tmp3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5494 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmpxchg_narrow_value(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int16,
                            /*acquire*/ Assembler::relaxed, /*release*/ Assembler::rl, opnd_array(4)->as_Register(ra_,this,idx4)/* res */,
                            /*result_as_bool*/ false, opnd_array(5)->as_Register(ra_,this,idx5)/* tmp1 */, opnd_array(6)->as_Register(ra_,this,idx6)/* tmp2 */, opnd_array(7)->as_Register(ra_,this,idx7)/* tmp3 */);
  
#line 10079 "ad_riscv.cpp"
  }
}

void compareAndExchangeINode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// res
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5515 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmpxchg(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int32,
               /*acquire*/ Assembler::relaxed, /*release*/ Assembler::rl, opnd_array(4)->as_Register(ra_,this,idx4)/* res */);
  
#line 10099 "ad_riscv.cpp"
  }
}

void compareAndExchangeLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// res
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5535 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmpxchg(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int64,
               /*acquire*/ Assembler::relaxed, /*release*/ Assembler::rl, opnd_array(4)->as_Register(ra_,this,idx4)/* res */);
  
#line 10119 "ad_riscv.cpp"
  }
}

void compareAndExchangeNNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// res
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5555 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmpxchg(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::uint32,
               /*acquire*/ Assembler::relaxed, /*release*/ Assembler::rl, opnd_array(4)->as_Register(ra_,this,idx4)/* res */);
  
#line 10139 "ad_riscv.cpp"
  }
}

void compareAndExchangePNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// res
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5576 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmpxchg(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int64,
               /*acquire*/ Assembler::relaxed, /*release*/ Assembler::rl, opnd_array(4)->as_Register(ra_,this,idx4)/* res */);
  
#line 10159 "ad_riscv.cpp"
  }
}

void compareAndExchangeBAcqNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// res
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// tmp1
  unsigned idx6 = idx5 + opnd_array(5)->num_edges(); 	// tmp2
  unsigned idx7 = idx6 + opnd_array(6)->num_edges(); 	// tmp3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5599 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmpxchg_narrow_value(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int8,
                            /*acquire*/ Assembler::aq, /*release*/ Assembler::rl, opnd_array(4)->as_Register(ra_,this,idx4)/* res */,
                            /*result_as_bool*/ false, opnd_array(5)->as_Register(ra_,this,idx5)/* tmp1 */, opnd_array(6)->as_Register(ra_,this,idx6)/* tmp2 */, opnd_array(7)->as_Register(ra_,this,idx7)/* tmp3 */);
  
#line 10183 "ad_riscv.cpp"
  }
}

void compareAndExchangeSAcqNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// res
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// tmp1
  unsigned idx6 = idx5 + opnd_array(5)->num_edges(); 	// tmp2
  unsigned idx7 = idx6 + opnd_array(6)->num_edges(); 	// tmp3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5623 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmpxchg_narrow_value(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int16,
                            /*acquire*/ Assembler::aq, /*release*/ Assembler::rl, opnd_array(4)->as_Register(ra_,this,idx4)/* res */,
                            /*result_as_bool*/ false, opnd_array(5)->as_Register(ra_,this,idx5)/* tmp1 */, opnd_array(6)->as_Register(ra_,this,idx6)/* tmp2 */, opnd_array(7)->as_Register(ra_,this,idx7)/* tmp3 */);
  
#line 10207 "ad_riscv.cpp"
  }
}

void compareAndExchangeIAcqNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// res
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5646 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmpxchg(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int32,
               /*acquire*/ Assembler::aq, /*release*/ Assembler::rl, opnd_array(4)->as_Register(ra_,this,idx4)/* res */);
  
#line 10227 "ad_riscv.cpp"
  }
}

void compareAndExchangeLAcqNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// res
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5668 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmpxchg(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int64,
               /*acquire*/ Assembler::aq, /*release*/ Assembler::rl, opnd_array(4)->as_Register(ra_,this,idx4)/* res */);
  
#line 10247 "ad_riscv.cpp"
  }
}

void compareAndExchangeNAcqNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// res
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5690 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmpxchg(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::uint32,
               /*acquire*/ Assembler::aq, /*release*/ Assembler::rl, opnd_array(4)->as_Register(ra_,this,idx4)/* res */);
  
#line 10267 "ad_riscv.cpp"
  }
}

void compareAndExchangePAcqNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// res
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5712 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmpxchg(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int64,
               /*acquire*/ Assembler::aq, /*release*/ Assembler::rl, opnd_array(4)->as_Register(ra_,this,idx4)/* res */);
  
#line 10287 "ad_riscv.cpp"
  }
}

void weakCompareAndSwapBNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// res
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// tmp1
  unsigned idx6 = idx5 + opnd_array(5)->num_edges(); 	// tmp2
  unsigned idx7 = idx6 + opnd_array(6)->num_edges(); 	// tmp3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5734 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ weak_cmpxchg_narrow_value(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int8,
                                 /*acquire*/ Assembler::relaxed, /*release*/ Assembler::rl, opnd_array(4)->as_Register(ra_,this,idx4)/* res */,
                                 opnd_array(5)->as_Register(ra_,this,idx5)/* tmp1 */, opnd_array(6)->as_Register(ra_,this,idx6)/* tmp2 */, opnd_array(7)->as_Register(ra_,this,idx7)/* tmp3 */);
  
#line 10311 "ad_riscv.cpp"
  }
}

void weakCompareAndSwapSNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// res
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// tmp1
  unsigned idx6 = idx5 + opnd_array(5)->num_edges(); 	// tmp2
  unsigned idx7 = idx6 + opnd_array(6)->num_edges(); 	// tmp3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5757 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ weak_cmpxchg_narrow_value(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int16,
                                 /*acquire*/ Assembler::relaxed, /*release*/ Assembler::rl, opnd_array(4)->as_Register(ra_,this,idx4)/* res */,
                                 opnd_array(5)->as_Register(ra_,this,idx5)/* tmp1 */, opnd_array(6)->as_Register(ra_,this,idx6)/* tmp2 */, opnd_array(7)->as_Register(ra_,this,idx7)/* tmp3 */);
  
#line 10335 "ad_riscv.cpp"
  }
}

void weakCompareAndSwapINode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5777 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmpxchg_weak(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int32,
                    /*acquire*/ Assembler::relaxed, /*release*/ Assembler::rl, opnd_array(0)->as_Register(ra_,this)/* res */);
  
#line 10354 "ad_riscv.cpp"
  }
}

void weakCompareAndSwapLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5796 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmpxchg_weak(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int64,
                    /*acquire*/ Assembler::relaxed, /*release*/ Assembler::rl, opnd_array(0)->as_Register(ra_,this)/* res */);
  
#line 10373 "ad_riscv.cpp"
  }
}

void weakCompareAndSwapNNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5815 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmpxchg_weak(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::uint32,
                    /*acquire*/ Assembler::relaxed, /*release*/ Assembler::rl, opnd_array(0)->as_Register(ra_,this)/* res */);
  
#line 10392 "ad_riscv.cpp"
  }
}

void weakCompareAndSwapPNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5835 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmpxchg_weak(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int64,
                    /*acquire*/ Assembler::relaxed, /*release*/ Assembler::rl, opnd_array(0)->as_Register(ra_,this)/* res */);
  
#line 10411 "ad_riscv.cpp"
  }
}

void weakCompareAndSwapBAcqNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// res
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// tmp1
  unsigned idx6 = idx5 + opnd_array(5)->num_edges(); 	// tmp2
  unsigned idx7 = idx6 + opnd_array(6)->num_edges(); 	// tmp3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5859 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ weak_cmpxchg_narrow_value(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int8,
                                 /*acquire*/ Assembler::aq, /*release*/ Assembler::rl, opnd_array(4)->as_Register(ra_,this,idx4)/* res */,
                                 opnd_array(5)->as_Register(ra_,this,idx5)/* tmp1 */, opnd_array(6)->as_Register(ra_,this,idx6)/* tmp2 */, opnd_array(7)->as_Register(ra_,this,idx7)/* tmp3 */);
  
#line 10435 "ad_riscv.cpp"
  }
}

void weakCompareAndSwapSAcqNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// res
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// tmp1
  unsigned idx6 = idx5 + opnd_array(5)->num_edges(); 	// tmp2
  unsigned idx7 = idx6 + opnd_array(6)->num_edges(); 	// tmp3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5884 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ weak_cmpxchg_narrow_value(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int16,
                                 /*acquire*/ Assembler::aq, /*release*/ Assembler::rl, opnd_array(4)->as_Register(ra_,this,idx4)/* res */,
                                 opnd_array(5)->as_Register(ra_,this,idx5)/* tmp1 */, opnd_array(6)->as_Register(ra_,this,idx6)/* tmp2 */, opnd_array(7)->as_Register(ra_,this,idx7)/* tmp3 */);
  
#line 10459 "ad_riscv.cpp"
  }
}

void weakCompareAndSwapIAcqNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5906 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmpxchg_weak(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int32,
                    /*acquire*/ Assembler::aq, /*release*/ Assembler::rl, opnd_array(0)->as_Register(ra_,this)/* res */);
  
#line 10478 "ad_riscv.cpp"
  }
}

void weakCompareAndSwapLAcqNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5927 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmpxchg_weak(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int64,
                    /*acquire*/ Assembler::aq, /*release*/ Assembler::rl, opnd_array(0)->as_Register(ra_,this)/* res */);
  
#line 10497 "ad_riscv.cpp"
  }
}

void weakCompareAndSwapNAcqNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5948 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmpxchg_weak(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::uint32,
                    /*acquire*/ Assembler::aq, /*release*/ Assembler::rl, opnd_array(0)->as_Register(ra_,this)/* res */);
  
#line 10516 "ad_riscv.cpp"
  }
}

void weakCompareAndSwapPAcqNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5969 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmpxchg_weak(as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int64,
                    /*acquire*/ Assembler::aq, /*release*/ Assembler::rl, opnd_array(0)->as_Register(ra_,this)/* res */);
  
#line 10535 "ad_riscv.cpp"
  }
}

void get_and_setINode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// newv
  {
    C2_MacroAssembler _masm(&cbuf);

#line 5985 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ atomic_xchgw(opnd_array(0)->as_Register(ra_,this)/* prev */, opnd_array(2)->as_Register(ra_,this,idx2)/* newv */, as_Register(opnd_array(1)->base(ra_,this,idx1)));
  
#line 10552 "ad_riscv.cpp"
  }
}

void get_and_setLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// newv
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6000 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ atomic_xchg(opnd_array(0)->as_Register(ra_,this)/* prev */, opnd_array(2)->as_Register(ra_,this,idx2)/* newv */, as_Register(opnd_array(1)->base(ra_,this,idx1)));
  
#line 10569 "ad_riscv.cpp"
  }
}

void get_and_setNNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// newv
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6015 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ atomic_xchgwu(opnd_array(0)->as_Register(ra_,this)/* prev */, opnd_array(2)->as_Register(ra_,this,idx2)/* newv */, as_Register(opnd_array(1)->base(ra_,this,idx1)));
  
#line 10586 "ad_riscv.cpp"
  }
}

void get_and_setPNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// newv
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6031 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ atomic_xchg(opnd_array(0)->as_Register(ra_,this)/* prev */, opnd_array(2)->as_Register(ra_,this,idx2)/* newv */, as_Register(opnd_array(1)->base(ra_,this,idx1)));
  
#line 10603 "ad_riscv.cpp"
  }
}

void get_and_setIAcqNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// newv
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6048 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ atomic_xchgalw(opnd_array(0)->as_Register(ra_,this)/* prev */, opnd_array(2)->as_Register(ra_,this,idx2)/* newv */, as_Register(opnd_array(1)->base(ra_,this,idx1)));
  
#line 10620 "ad_riscv.cpp"
  }
}

void get_and_setLAcqNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// newv
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6065 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ atomic_xchgal(opnd_array(0)->as_Register(ra_,this)/* prev */, opnd_array(2)->as_Register(ra_,this,idx2)/* newv */, as_Register(opnd_array(1)->base(ra_,this,idx1)));
  
#line 10637 "ad_riscv.cpp"
  }
}

void get_and_setNAcqNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// newv
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6082 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ atomic_xchgalwu(opnd_array(0)->as_Register(ra_,this)/* prev */, opnd_array(2)->as_Register(ra_,this,idx2)/* newv */, as_Register(opnd_array(1)->base(ra_,this,idx1)));
  
#line 10654 "ad_riscv.cpp"
  }
}

void get_and_setPAcqNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// newv
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6099 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ atomic_xchgal(opnd_array(0)->as_Register(ra_,this)/* prev */, opnd_array(2)->as_Register(ra_,this,idx2)/* newv */, as_Register(opnd_array(1)->base(ra_,this,idx1)));
  
#line 10671 "ad_riscv.cpp"
  }
}

void get_and_addLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// incr
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6114 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ atomic_add(opnd_array(0)->as_Register(ra_,this)/* newval */, opnd_array(2)->as_Register(ra_,this,idx2)/* incr */, as_Register(opnd_array(1)->base(ra_,this,idx1)));
  
#line 10688 "ad_riscv.cpp"
  }
}

void get_and_addL_no_resNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// incr
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6131 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ atomic_add(noreg, opnd_array(2)->as_Register(ra_,this,idx2)/* incr */, as_Register(opnd_array(1)->base(ra_,this,idx1)));
  
#line 10705 "ad_riscv.cpp"
  }
}

void get_and_addLiNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// incr
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6146 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ atomic_add(opnd_array(0)->as_Register(ra_,this)/* newval */, opnd_array(2)->constantL(), as_Register(opnd_array(1)->base(ra_,this,idx1)));
  
#line 10722 "ad_riscv.cpp"
  }
}

void get_and_addLi_no_resNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// incr
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6163 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ atomic_add(noreg, opnd_array(2)->constantL(), as_Register(opnd_array(1)->base(ra_,this,idx1)));
  
#line 10739 "ad_riscv.cpp"
  }
}

void get_and_addINode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// incr
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6178 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ atomic_addw(opnd_array(0)->as_Register(ra_,this)/* newval */, opnd_array(2)->as_Register(ra_,this,idx2)/* incr */, as_Register(opnd_array(1)->base(ra_,this,idx1)));
  
#line 10756 "ad_riscv.cpp"
  }
}

void get_and_addI_no_resNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// incr
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6195 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ atomic_addw(noreg, opnd_array(2)->as_Register(ra_,this,idx2)/* incr */, as_Register(opnd_array(1)->base(ra_,this,idx1)));
  
#line 10773 "ad_riscv.cpp"
  }
}

void get_and_addIiNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// incr
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6210 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ atomic_addw(opnd_array(0)->as_Register(ra_,this)/* newval */, opnd_array(2)->constant(), as_Register(opnd_array(1)->base(ra_,this,idx1)));
  
#line 10790 "ad_riscv.cpp"
  }
}

void get_and_addIi_no_resNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// incr
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6227 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ atomic_addw(noreg, opnd_array(2)->constant(), as_Register(opnd_array(1)->base(ra_,this,idx1)));
  
#line 10807 "ad_riscv.cpp"
  }
}

void get_and_addLAcqNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// incr
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6244 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ atomic_addal(opnd_array(0)->as_Register(ra_,this)/* newval */, opnd_array(2)->as_Register(ra_,this,idx2)/* incr */, as_Register(opnd_array(1)->base(ra_,this,idx1)));
  
#line 10824 "ad_riscv.cpp"
  }
}

void get_and_addL_no_resAcqNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// incr
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6260 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ atomic_addal(noreg, opnd_array(2)->as_Register(ra_,this,idx2)/* incr */, as_Register(opnd_array(1)->base(ra_,this,idx1)));
  
#line 10841 "ad_riscv.cpp"
  }
}

void get_and_addLiAcqNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// incr
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6277 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ atomic_addal(opnd_array(0)->as_Register(ra_,this)/* newval */, opnd_array(2)->constantL(), as_Register(opnd_array(1)->base(ra_,this,idx1)));
  
#line 10858 "ad_riscv.cpp"
  }
}

void get_and_addLi_no_resAcqNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// incr
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6294 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ atomic_addal(noreg, opnd_array(2)->constantL(), as_Register(opnd_array(1)->base(ra_,this,idx1)));
  
#line 10875 "ad_riscv.cpp"
  }
}

void get_and_addIAcqNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// incr
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6311 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ atomic_addalw(opnd_array(0)->as_Register(ra_,this)/* newval */, opnd_array(2)->as_Register(ra_,this,idx2)/* incr */, as_Register(opnd_array(1)->base(ra_,this,idx1)));
  
#line 10892 "ad_riscv.cpp"
  }
}

void get_and_addI_no_resAcqNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// incr
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6328 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ atomic_addalw(noreg, opnd_array(2)->as_Register(ra_,this,idx2)/* incr */, as_Register(opnd_array(1)->base(ra_,this,idx1)));
  
#line 10909 "ad_riscv.cpp"
  }
}

void get_and_addIiAcqNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// incr
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6345 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ atomic_addalw(opnd_array(0)->as_Register(ra_,this)/* newval */, opnd_array(2)->constant(), as_Register(opnd_array(1)->base(ra_,this,idx1)));
  
#line 10926 "ad_riscv.cpp"
  }
}

void get_and_addIi_no_resAcqNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// incr
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6362 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ atomic_addalw(noreg, opnd_array(2)->constant(), as_Register(opnd_array(1)->base(ra_,this,idx1)));
  
#line 10943 "ad_riscv.cpp"
  }
}

void addI_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6386 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ addw(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
            as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
            as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 10962 "ad_riscv.cpp"
  }
}

void addI_reg_immNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6401 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    int32_t con = (int32_t)opnd_array(2)->constant();
    __ addiw(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
             as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
             opnd_array(2)->constant());
  
#line 10982 "ad_riscv.cpp"
  }
}

void addI_reg_imm_l2iNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6417 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ addiw(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
             as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
             opnd_array(2)->constant());
  
#line 11001 "ad_riscv.cpp"
  }
}

void addP_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6433 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ add(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
           as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
           as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 11020 "ad_riscv.cpp"
  }
}

void lShiftL_regI_immGE32Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// scale
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6448 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ slli(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */), opnd_array(2)->constant()& 63);
  
#line 11037 "ad_riscv.cpp"
  }
}

void addP_reg_immNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6463 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    // src2 is imm, so actually call the addi
    __ add(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
           as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
           opnd_array(2)->constantL());
  
#line 11057 "ad_riscv.cpp"
  }
}

void addL_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6479 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ add(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
           as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
           as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 11076 "ad_riscv.cpp"
  }
}

void addL_reg_immNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6494 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    // src2 is imm, so actually call the addi
    __ add(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
           as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
           opnd_array(2)->constantL());
  
#line 11096 "ad_riscv.cpp"
  }
}

void subI_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6511 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ subw(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
            as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
            as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 11115 "ad_riscv.cpp"
  }
}

void subI_reg_immNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6527 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    // src2 is imm, so actually call the addiw
    __ subw(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
            as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
            opnd_array(2)->constant());
  
#line 11135 "ad_riscv.cpp"
  }
}

void subL_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6543 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ sub(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
           as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
           as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 11154 "ad_riscv.cpp"
  }
}

void subL_reg_immNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6558 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    // src2 is imm, so actually call the addi
    __ sub(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
           as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
           opnd_array(2)->constantL());
  
#line 11174 "ad_riscv.cpp"
  }
}

void negI_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// zero
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6575 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    // actually call the subw
    __ negw(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
            as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src */));
  
#line 11193 "ad_riscv.cpp"
  }
}

void negL_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// zero
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6591 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    // actually call the sub
    __ neg(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
           as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src */));
  
#line 11212 "ad_riscv.cpp"
  }
}

void mulINode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6608 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    // riscv64 mulw will sign-extension to high 32 bits in dst reg
    __ mulw(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
            as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
            as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 11232 "ad_riscv.cpp"
  }
}

void mulLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6625 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ mul(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
           as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
           as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 11251 "ad_riscv.cpp"
  }
}

void mulHiL_rRegNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6640 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ mulh(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
            as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
            as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 11270 "ad_riscv.cpp"
  }
}

void divINode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {

#line 2553 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    Register dst_reg = as_Register(opnd_array(0)->reg(ra_,this)/* dst */);
    Register src1_reg = as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */);
    Register src2_reg = as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */);
    __ corrected_idivl(dst_reg, src1_reg, src2_reg, false);
  
#line 11290 "ad_riscv.cpp"
  }
}

void signExtractNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// div1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// div2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6665 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ srliw(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */), 31);
  
#line 11308 "ad_riscv.cpp"
  }
}

void divLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {

#line 2561 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    Register dst_reg = as_Register(opnd_array(0)->reg(ra_,this)/* dst */);
    Register src1_reg = as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */);
    Register src2_reg = as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */);
    __ corrected_idivq(dst_reg, src1_reg, src2_reg, false);
  
#line 11328 "ad_riscv.cpp"
  }
}

void signExtractLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// div1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// div2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6687 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ srli(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */), 63);
  
#line 11346 "ad_riscv.cpp"
  }
}

void modINode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {

#line 2569 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    Register dst_reg = as_Register(opnd_array(0)->reg(ra_,this)/* dst */);
    Register src1_reg = as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */);
    Register src2_reg = as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */);
    __ corrected_idivl(dst_reg, src1_reg, src2_reg, true);
  
#line 11366 "ad_riscv.cpp"
  }
}

void modLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {

#line 2577 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    Register dst_reg = as_Register(opnd_array(0)->reg(ra_,this)/* dst */);
    Register src1_reg = as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */);
    Register src2_reg = as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */);
    __ corrected_idivq(dst_reg, src1_reg, src2_reg, true);
  
#line 11386 "ad_riscv.cpp"
  }
}

void lShiftI_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6724 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ sllw(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
            as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
            as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 11405 "ad_riscv.cpp"
  }
}

void lShiftI_reg_immNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6739 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    // the shift amount is encoded in the lower
    // 5 bits of the I-immediate field for RV32I
    __ slliw(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
             as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
             (unsigned) opnd_array(2)->constant()& 0x1f);
  
#line 11426 "ad_riscv.cpp"
  }
}

void urShiftI_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6757 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ srlw(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
            as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
            as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 11445 "ad_riscv.cpp"
  }
}

void urShiftI_reg_immNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6772 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    // the shift amount is encoded in the lower
    // 6 bits of the I-immediate field for RV64I
    __ srliw(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
             as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
             (unsigned) opnd_array(2)->constant()& 0x1f);
  
#line 11466 "ad_riscv.cpp"
  }
}

void rShiftI_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6790 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    // riscv will sign-ext dst high 32 bits
    __ sraw(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
            as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
            as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 11486 "ad_riscv.cpp"
  }
}

void rShiftI_reg_immNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6806 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    // riscv will sign-ext dst high 32 bits
    __ sraiw(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
             as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
             (unsigned) opnd_array(2)->constant()& 0x1f);
  
#line 11506 "ad_riscv.cpp"
  }
}

void lShiftL_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6826 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ sll(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
           as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
           as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 11525 "ad_riscv.cpp"
  }
}

void lShiftL_reg_immNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6842 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    // the shift amount is encoded in the lower
    // 6 bits of the I-immediate field for RV64I
    __ slli(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
            as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
            (unsigned) opnd_array(2)->constant()& 0x3f);
  
#line 11546 "ad_riscv.cpp"
  }
}

void urShiftL_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6861 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ srl(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
            as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
            as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 11565 "ad_riscv.cpp"
  }
}

void urShiftL_reg_immNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6877 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    // the shift amount is encoded in the lower
    // 6 bits of the I-immediate field for RV64I
    __ srli(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
            as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
            (unsigned) opnd_array(2)->constant()& 0x3f);
  
#line 11586 "ad_riscv.cpp"
  }
}

void urShiftP_reg_immNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6895 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    // the shift amount is encoded in the lower
    // 6 bits of the I-immediate field for RV64I
    __ srli(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
            as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
            (unsigned) opnd_array(2)->constant()& 0x3f);
  
#line 11607 "ad_riscv.cpp"
  }
}

void rShiftL_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6914 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ sra(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
           as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
           as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 11626 "ad_riscv.cpp"
  }
}

void rShiftL_reg_immNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6930 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    // the shift amount is encoded in the lower
    // 6 bits of the I-immediate field for RV64I
    __ srai(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
            as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
            (unsigned) opnd_array(2)->constant()& 0x3f);
  
#line 11647 "ad_riscv.cpp"
  }
}

void regI_not_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// m1
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6946 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ xori(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */), -1);
  
#line 11664 "ad_riscv.cpp"
  }
}

void regL_not_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// m1
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6958 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ xori(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */), -1);
  
#line 11681 "ad_riscv.cpp"
  }
}

void addF_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6975 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fadd_s(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */),
              as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
              as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 11700 "ad_riscv.cpp"
  }
}

void addD_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 6990 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fadd_d(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */),
              as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
              as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 11719 "ad_riscv.cpp"
  }
}

void subF_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7005 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fsub_s(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */),
              as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
              as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 11738 "ad_riscv.cpp"
  }
}

void subD_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7020 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fsub_d(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */),
              as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
              as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 11757 "ad_riscv.cpp"
  }
}

void mulF_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7035 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fmul_s(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */),
              as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
              as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 11776 "ad_riscv.cpp"
  }
}

void mulD_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7050 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fmul_d(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */),
              as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
              as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 11795 "ad_riscv.cpp"
  }
}

void maddF_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src3
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7067 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fmadd_s(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */),
               as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* src1 */),
               as_FloatRegister(opnd_array(3)->reg(ra_,this,idx3)/* src2 */),
               as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src3 */));
  
#line 11816 "ad_riscv.cpp"
  }
}

void maddD_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src3
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7085 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fmadd_d(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */),
               as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* src1 */),
               as_FloatRegister(opnd_array(3)->reg(ra_,this,idx3)/* src2 */),
               as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src3 */));
  
#line 11837 "ad_riscv.cpp"
  }
}

void msubF_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src3
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7103 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fmsub_s(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */),
               as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* src1 */),
               as_FloatRegister(opnd_array(3)->reg(ra_,this,idx3)/* src2 */),
               as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src3 */));
  
#line 11858 "ad_riscv.cpp"
  }
}

void msubD_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src3
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7121 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fmsub_d(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */),
               as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* src1 */),
               as_FloatRegister(opnd_array(3)->reg(ra_,this,idx3)/* src2 */),
               as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src3 */));
  
#line 11879 "ad_riscv.cpp"
  }
}

void nmsubF_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src3
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7140 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fnmsub_s(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */),
                as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* src1 */),
                as_FloatRegister(opnd_array(3)->reg(ra_,this,idx3)/* src2 */),
                as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src3 */));
  
#line 11900 "ad_riscv.cpp"
  }
}

void nmsubF_reg_reg_0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src3
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7140 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fnmsub_s(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */),
                as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* src1 */),
                as_FloatRegister(opnd_array(3)->reg(ra_,this,idx3)/* src2 */),
                as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src3 */));
  
#line 11921 "ad_riscv.cpp"
  }
}

void nmsubD_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src3
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7159 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fnmsub_d(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */),
                as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* src1 */),
                as_FloatRegister(opnd_array(3)->reg(ra_,this,idx3)/* src2 */),
                as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src3 */));
  
#line 11942 "ad_riscv.cpp"
  }
}

void nmsubD_reg_reg_0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src3
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7159 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fnmsub_d(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */),
                as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* src1 */),
                as_FloatRegister(opnd_array(3)->reg(ra_,this,idx3)/* src2 */),
                as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src3 */));
  
#line 11963 "ad_riscv.cpp"
  }
}

void nmaddF_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src3
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7178 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fnmadd_s(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */),
                as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* src1 */),
                as_FloatRegister(opnd_array(3)->reg(ra_,this,idx3)/* src2 */),
                as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src3 */));
  
#line 11984 "ad_riscv.cpp"
  }
}

void nmaddF_reg_reg_0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src3
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7178 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fnmadd_s(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */),
                as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* src1 */),
                as_FloatRegister(opnd_array(3)->reg(ra_,this,idx3)/* src2 */),
                as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src3 */));
  
#line 12005 "ad_riscv.cpp"
  }
}

void nmaddD_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src3
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7197 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fnmadd_d(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */),
                as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* src1 */),
                as_FloatRegister(opnd_array(3)->reg(ra_,this,idx3)/* src2 */),
                as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src3 */));
  
#line 12026 "ad_riscv.cpp"
  }
}

void nmaddD_reg_reg_0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src3
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7197 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fnmadd_d(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */),
                as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* src1 */),
                as_FloatRegister(opnd_array(3)->reg(ra_,this,idx3)/* src2 */),
                as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src3 */));
  
#line 12047 "ad_riscv.cpp"
  }
}

void maxF_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// dst
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7214 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ minmax_FD(as_FloatRegister(opnd_array(3)->reg(ra_,this,idx3)/* dst */),
                 as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */), as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */),
                 false /* is_double */, false /* is_min */);
  
#line 12067 "ad_riscv.cpp"
  }
}

void minF_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// dst
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7230 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ minmax_FD(as_FloatRegister(opnd_array(3)->reg(ra_,this,idx3)/* dst */),
                 as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */), as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */),
                 false /* is_double */, true /* is_min */);
  
#line 12087 "ad_riscv.cpp"
  }
}

void maxD_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// dst
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7246 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ minmax_FD(as_FloatRegister(opnd_array(3)->reg(ra_,this,idx3)/* dst */),
                 as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */), as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */),
                 true /* is_double */, false /* is_min */);
  
#line 12107 "ad_riscv.cpp"
  }
}

void minD_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// dst
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7262 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ minmax_FD(as_FloatRegister(opnd_array(3)->reg(ra_,this,idx3)/* dst */),
                 as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */), as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */),
                 true /* is_double */, true /* is_min */);
  
#line 12127 "ad_riscv.cpp"
  }
}

void isIniniteF_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7276 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fclass_s(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
    __ andi(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(0)->reg(ra_,this)/* dst */), 0b10000001);
    __ slt(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), zr, as_Register(opnd_array(0)->reg(ra_,this)/* dst */));
  
#line 12145 "ad_riscv.cpp"
  }
}

void isInfiniteD_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7289 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fclass_d(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
    __ andi(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(0)->reg(ra_,this)/* dst */), 0b10000001);
    __ slt(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), zr, as_Register(opnd_array(0)->reg(ra_,this)/* dst */));
  
#line 12163 "ad_riscv.cpp"
  }
}

void isFiniteF_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7302 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fclass_s(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
    __ andi(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(0)->reg(ra_,this)/* dst */), 0b0001111110);
    __ slt(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), zr, as_Register(opnd_array(0)->reg(ra_,this)/* dst */));
  
#line 12181 "ad_riscv.cpp"
  }
}

void isFiniteD_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7315 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fclass_d(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
    __ andi(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(0)->reg(ra_,this)/* dst */), 0b0001111110);
    __ slt(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), zr, as_Register(opnd_array(0)->reg(ra_,this)/* dst */));
  
#line 12199 "ad_riscv.cpp"
  }
}

void divF_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7329 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fdiv_s(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */),
              as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
              as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 12218 "ad_riscv.cpp"
  }
}

void divD_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7344 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fdiv_d(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */),
              as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
              as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 12237 "ad_riscv.cpp"
  }
}

void negF_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7359 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fneg_s(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */),
              as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 12254 "ad_riscv.cpp"
  }
}

void negD_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7373 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fneg_d(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */),
              as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 12271 "ad_riscv.cpp"
  }
}

void absI_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7391 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ sraiw(t0, as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */), 0x1f);
    __ addw(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */), t0);
    __ xorr(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(0)->reg(ra_,this)/* dst */), t0);
  
#line 12289 "ad_riscv.cpp"
  }
}

void absL_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7410 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ srai(t0, as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */), 0x3f);
    __ add(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */), t0);
    __ xorr(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(0)->reg(ra_,this)/* dst */), t0);
  
#line 12307 "ad_riscv.cpp"
  }
}

void absF_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7424 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fabs_s(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */),
              as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 12324 "ad_riscv.cpp"
  }
}

void absD_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7437 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fabs_d(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */),
              as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 12341 "ad_riscv.cpp"
  }
}

void sqrtF_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7450 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fsqrt_s(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */),
               as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 12358 "ad_riscv.cpp"
  }
}

void sqrtD_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7463 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fsqrt_d(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */),
               as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 12375 "ad_riscv.cpp"
  }
}

void andI_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7483 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ andr(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
            as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
            as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 12394 "ad_riscv.cpp"
  }
}

void andI_reg_immNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7499 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ andi(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
            as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
            (int32_t)(opnd_array(2)->constant()));
  
#line 12413 "ad_riscv.cpp"
  }
}

void orI_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7515 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ orr(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
           as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
           as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 12432 "ad_riscv.cpp"
  }
}

void orI_reg_immNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7531 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ ori(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
           as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
           (int32_t)(opnd_array(2)->constant()));
  
#line 12451 "ad_riscv.cpp"
  }
}

void xorI_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7547 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ xorr(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
            as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
            as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 12470 "ad_riscv.cpp"
  }
}

void xorI_reg_immNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7563 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ xori(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
            as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
            (int32_t)(opnd_array(2)->constant()));
  
#line 12489 "ad_riscv.cpp"
  }
}

void andL_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7579 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ andr(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
            as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
            as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 12508 "ad_riscv.cpp"
  }
}

void andL_reg_immNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7595 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ andi(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
            as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
            (int32_t)(opnd_array(2)->constantL()));
  
#line 12527 "ad_riscv.cpp"
  }
}

void orL_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7611 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ orr(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
           as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
           as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 12546 "ad_riscv.cpp"
  }
}

void orL_reg_immNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7627 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ ori(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
           as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
           (int32_t)(opnd_array(2)->constantL()));
  
#line 12565 "ad_riscv.cpp"
  }
}

void xorL_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7643 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ xorr(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
            as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
            as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 12584 "ad_riscv.cpp"
  }
}

void xorL_reg_immNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7659 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ xori(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
            as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
            (int32_t)(opnd_array(2)->constantL()));
  
#line 12603 "ad_riscv.cpp"
  }
}

void bytes_reverse_intNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// cr
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7678 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ revb_w_w(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 12620 "ad_riscv.cpp"
  }
}

void bytes_reverse_longNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// cr
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7692 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ revb(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 12637 "ad_riscv.cpp"
  }
}

void bytes_reverse_unsigned_shortNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7705 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ revb_h_h_u(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 12653 "ad_riscv.cpp"
  }
}

void bytes_reverse_shortNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7718 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ revb_h_h(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 12669 "ad_riscv.cpp"
  }
}

void load_fenceNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7734 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ membar(MacroAssembler::LoadLoad | MacroAssembler::LoadStore);
  
#line 12685 "ad_riscv.cpp"
  }
}

void membar_acquireNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7747 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ block_comment("membar_acquire");
    __ membar(MacroAssembler::LoadLoad | MacroAssembler::LoadStore);
  
#line 12702 "ad_riscv.cpp"
  }
}

void membar_acquire_lockNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7761 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ block_comment("membar_acquire_lock (elided)");
  
#line 12718 "ad_riscv.cpp"
  }
}

void store_fenceNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7774 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ membar(MacroAssembler::LoadStore | MacroAssembler::StoreStore);
  
#line 12734 "ad_riscv.cpp"
  }
}

void membar_releaseNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7787 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ block_comment("membar_release");
    __ membar(MacroAssembler::LoadStore | MacroAssembler::StoreStore);
  
#line 12751 "ad_riscv.cpp"
  }
}

void membar_storestoreNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7801 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ membar(MacroAssembler::StoreStore);
  
#line 12767 "ad_riscv.cpp"
  }
}

void membar_storestore_0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7801 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ membar(MacroAssembler::StoreStore);
  
#line 12783 "ad_riscv.cpp"
  }
}

void membar_release_lockNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7813 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ block_comment("membar_release_lock (elided)");
  
#line 12799 "ad_riscv.cpp"
  }
}

void membar_volatileNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7827 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ block_comment("membar_volatile");
    __ membar(MacroAssembler::StoreLoad);
  
#line 12816 "ad_riscv.cpp"
  }
}

void castX2PNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7844 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    if (opnd_array(0)->reg(ra_,this)/* dst */!= opnd_array(1)->reg(ra_,this,idx1)/* src */) {
      __ mv(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
    }
  
#line 12834 "ad_riscv.cpp"
  }
}

void castP2XNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7859 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    if (opnd_array(0)->reg(ra_,this)/* dst */!= opnd_array(1)->reg(ra_,this,idx1)/* src */) {
      __ mv(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
    }
  
#line 12852 "ad_riscv.cpp"
  }
}

void castPPNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// dst
  // User did not define which encode class to use.
}

uint castPPNode::size(PhaseRegAlloc *ra_) const {
  assert(VerifyOops || MachNode::size(ra_) <= 0, "bad fixed size");
  return (VerifyOops ? MachNode::size(ra_) : 0);
}

void castLLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// dst
  // User did not define which encode class to use.
}

uint castLLNode::size(PhaseRegAlloc *ra_) const {
  assert(VerifyOops || MachNode::size(ra_) <= 0, "bad fixed size");
  return (VerifyOops ? MachNode::size(ra_) : 0);
}

void castIINode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// dst
  // User did not define which encode class to use.
}

uint castIINode::size(PhaseRegAlloc *ra_) const {
  assert(VerifyOops || MachNode::size(ra_) <= 0, "bad fixed size");
  return (VerifyOops ? MachNode::size(ra_) : 0);
}

void checkCastPPNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// dst
  // User did not define which encode class to use.
}

uint checkCastPPNode::size(PhaseRegAlloc *ra_) const {
  assert(VerifyOops || MachNode::size(ra_) <= 0, "bad fixed size");
  return (VerifyOops ? MachNode::size(ra_) : 0);
}

void castFFNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// dst
  // User did not define which encode class to use.
}

uint castFFNode::size(PhaseRegAlloc *ra_) const {
  assert(VerifyOops || MachNode::size(ra_) <= 0, "bad fixed size");
  return (VerifyOops ? MachNode::size(ra_) : 0);
}

void castDDNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// dst
  // User did not define which encode class to use.
}

uint castDDNode::size(PhaseRegAlloc *ra_) const {
  assert(VerifyOops || MachNode::size(ra_) <= 0, "bad fixed size");
  return (VerifyOops ? MachNode::size(ra_) : 0);
}

void castVVNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// dst
  // User did not define which encode class to use.
}

uint castVVNode::size(PhaseRegAlloc *ra_) const {
  assert(VerifyOops || MachNode::size(ra_) <= 0, "bad fixed size");
  return (VerifyOops ? MachNode::size(ra_) : 0);
}

void convI2BoolNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7956 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ snez(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 12959 "ad_riscv.cpp"
  }
}

void convP2BoolNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7971 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ snez(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 12975 "ad_riscv.cpp"
  }
}

void convI2L_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7986 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ addw(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */), zr);
  
#line 12991 "ad_riscv.cpp"
  }
}

void convL2I_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 7998 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ addw(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */), zr);
  
#line 13007 "ad_riscv.cpp"
  }
}

void convI2UL_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// mask
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8013 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ zero_extend(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */), 32);
  
#line 13024 "ad_riscv.cpp"
  }
}

void convF2D_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8028 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fcvt_d_s(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 13040 "ad_riscv.cpp"
  }
}

void convD2F_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8041 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fcvt_s_d(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 13056 "ad_riscv.cpp"
  }
}

void convF2I_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8056 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fcvt_w_s_safe(opnd_array(0)->as_Register(ra_,this)/* dst */, opnd_array(1)->as_FloatRegister(ra_,this,idx1)/* src */);
  
#line 13072 "ad_riscv.cpp"
  }
}

void convI2F_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8069 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fcvt_s_w(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 13088 "ad_riscv.cpp"
  }
}

void convF2L_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8084 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fcvt_l_s_safe(opnd_array(0)->as_Register(ra_,this)/* dst */, opnd_array(1)->as_FloatRegister(ra_,this,idx1)/* src */);
  
#line 13104 "ad_riscv.cpp"
  }
}

void convL2F_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8097 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fcvt_s_l(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 13120 "ad_riscv.cpp"
  }
}

void convD2I_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8112 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fcvt_w_d_safe(opnd_array(0)->as_Register(ra_,this)/* dst */, opnd_array(1)->as_FloatRegister(ra_,this,idx1)/* src */);
  
#line 13136 "ad_riscv.cpp"
  }
}

void convI2D_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8125 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fcvt_d_w(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 13152 "ad_riscv.cpp"
  }
}

void convD2L_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8140 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fcvt_l_d_safe(opnd_array(0)->as_Register(ra_,this)/* dst */, opnd_array(1)->as_FloatRegister(ra_,this,idx1)/* src */);
  
#line 13168 "ad_riscv.cpp"
  }
}

void convL2D_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8153 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fcvt_d_l(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 13184 "ad_riscv.cpp"
  }
}

void convP2INode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8167 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ zero_extend(opnd_array(0)->as_Register(ra_,this)/* dst */, opnd_array(1)->as_Register(ra_,this,idx1)/* src */, 32);
  
#line 13200 "ad_riscv.cpp"
  }
}

void convN2INode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8184 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ mv(opnd_array(0)->as_Register(ra_,this)/* dst */, opnd_array(1)->as_Register(ra_,this,idx1)/* src */);
  
#line 13216 "ad_riscv.cpp"
  }
}

void encodeHeapOopNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8196 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    Register s = opnd_array(1)->as_Register(ra_,this,idx1)/* src */;
    Register d = opnd_array(0)->as_Register(ra_,this)/* dst */;
    __ encode_heap_oop(d, s);
  
#line 13234 "ad_riscv.cpp"
  }
}

void decodeHeapOopNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8211 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    Register s = opnd_array(1)->as_Register(ra_,this,idx1)/* src */;
    Register d = opnd_array(0)->as_Register(ra_,this)/* dst */;
    __ decode_heap_oop(d, s);
  
#line 13252 "ad_riscv.cpp"
  }
}

void decodeHeapOop_not_nullNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8226 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    Register s = opnd_array(1)->as_Register(ra_,this,idx1)/* src */;
    Register d = opnd_array(0)->as_Register(ra_,this)/* dst */;
    __ decode_heap_oop_not_null(d, s);
  
#line 13270 "ad_riscv.cpp"
  }
}

void encodeKlass_not_nullNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8241 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    Register src_reg = as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */);
    Register dst_reg = as_Register(opnd_array(0)->reg(ra_,this)/* dst */);
    __ encode_klass_not_null(dst_reg, src_reg, t0);
  
#line 13288 "ad_riscv.cpp"
  }
}

void decodeKlass_not_nullNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8258 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    Register src_reg = as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */);
    Register dst_reg = as_Register(opnd_array(0)->reg(ra_,this)/* dst */);
    Register tmp_reg = as_Register(opnd_array(2)->reg(ra_,this,idx2)/* tmp */);
    __ decode_klass_not_null(dst_reg, src_reg, tmp_reg);
  
#line 13308 "ad_riscv.cpp"
  }
}

void MoveF2I_stack_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8280 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ lw(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), Address(sp, opnd_array(1)->disp(ra_,this,idx1)));
  
#line 13324 "ad_riscv.cpp"
  }
}

void MoveI2F_stack_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8298 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ flw(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */), Address(sp, opnd_array(1)->disp(ra_,this,idx1)));
  
#line 13340 "ad_riscv.cpp"
  }
}

void MoveD2L_stack_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8316 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ ld(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), Address(sp, opnd_array(1)->disp(ra_,this,idx1)));
  
#line 13356 "ad_riscv.cpp"
  }
}

void MoveL2D_stack_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8334 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fld(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */), Address(sp, opnd_array(1)->disp(ra_,this,idx1)));
  
#line 13372 "ad_riscv.cpp"
  }
}

void MoveF2I_reg_stackNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8352 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fsw(as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */), Address(sp, opnd_array(0)->disp(ra_,this,0)));
  
#line 13388 "ad_riscv.cpp"
  }
}

void MoveI2F_reg_stackNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8370 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ sw(as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */), Address(sp, opnd_array(0)->disp(ra_,this,0)));
  
#line 13404 "ad_riscv.cpp"
  }
}

void MoveD2L_reg_stackNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8388 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fsd(as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */), Address(sp, opnd_array(0)->disp(ra_,this,0)));
  
#line 13420 "ad_riscv.cpp"
  }
}

void MoveL2D_reg_stackNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8406 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ sd(as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */), Address(sp, opnd_array(0)->disp(ra_,this,0)));
  
#line 13436 "ad_riscv.cpp"
  }
}

void MoveF2I_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8424 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fmv_x_w(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 13452 "ad_riscv.cpp"
  }
}

void MoveI2F_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8442 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fmv_w_x(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 13468 "ad_riscv.cpp"
  }
}

void MoveD2L_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8460 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fmv_x_d(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 13484 "ad_riscv.cpp"
  }
}

void MoveL2D_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8478 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ fmv_d_x(as_FloatRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 13500 "ad_riscv.cpp"
  }
}

void cmpF3_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8499 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    // we want -1 for unordered or less than, 0 for equal and 1 for greater than.
    __ float_compare(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* op1 */),
                     as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* op2 */), -1 /*unordered_result < 0*/);
  
#line 13519 "ad_riscv.cpp"
  }
}

void cmpD3_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8519 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    // we want -1 for unordered or less than, 0 for equal and 1 for greater than.
    __ double_compare(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_FloatRegister(opnd_array(1)->reg(ra_,this,idx1)/* op1 */), as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* op2 */), -1 /*unordered_result < 0*/);
  
#line 13537 "ad_riscv.cpp"
  }
}

void cmpL3_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8537 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmp_l2i(t0, as_Register(opnd_array(1)->reg(ra_,this,idx1)/* op1 */), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op2 */));
    __ mv(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), t0);
  
#line 13555 "ad_riscv.cpp"
  }
}

void cmpLTMask_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// p
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// q
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8555 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ slt(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* p */), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* q */));
    __ subw(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), zr, as_Register(opnd_array(0)->reg(ra_,this)/* dst */));
  
#line 13573 "ad_riscv.cpp"
  }
}

void cmpLTMask_reg_zeroNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8571 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ sraiw(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* op */), 31);
  
#line 13590 "ad_riscv.cpp"
  }
}

void minI_rRegNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8598 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    Label Lsrc1, Ldone;
    __ ble(as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */), Lsrc1);
    __ mv(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
    __ j(Ldone);
    __ bind(Lsrc1);
    __ mv(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */));
    __ bind(Ldone);
  
#line 13613 "ad_riscv.cpp"
  }
}

void maxI_rRegNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8627 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    Label Lsrc1, Ldone;
    __ bge(as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */), Lsrc1);
    __ mv(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
    __ j(Ldone);
    __ bind(Lsrc1);
    __ mv(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */));
    __ bind(Ldone);

  
#line 13637 "ad_riscv.cpp"
  }
}

void branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// 
  {

#line 2233 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    Label* L = opnd_array(1)->label();
    __ j(*L);
  
#line 13654 "ad_riscv.cpp"
  }
}

void cmpFlag_branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// cr
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// lbl
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8671 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ enc_cmpEqNe_imm0_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* cr */), *(opnd_array(3)->label()));
  
#line 13672 "ad_riscv.cpp"
  }
}

void cmpI_branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8690 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmp_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), as_Register(opnd_array(3)->reg(ra_,this,idx3)/* op2 */), *(opnd_array(4)->label()));
  
#line 13691 "ad_riscv.cpp"
  }
}

void cmpI_loopNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8709 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmp_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), as_Register(opnd_array(3)->reg(ra_,this,idx3)/* op2 */), *(opnd_array(4)->label()));
  
#line 13710 "ad_riscv.cpp"
  }
}

void cmpU_branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8729 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmp_branch(opnd_array(1)->ccode()| C2_MacroAssembler::unsigned_branch_mask, as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */),
                  as_Register(opnd_array(3)->reg(ra_,this,idx3)/* op2 */), *(opnd_array(4)->label()));
  
#line 13730 "ad_riscv.cpp"
  }
}

void cmpU_loopNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8749 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmp_branch(opnd_array(1)->ccode()| C2_MacroAssembler::unsigned_branch_mask, as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */),
                  as_Register(opnd_array(3)->reg(ra_,this,idx3)/* op2 */), *(opnd_array(4)->label()));
  
#line 13750 "ad_riscv.cpp"
  }
}

void cmpL_branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8770 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmp_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), as_Register(opnd_array(3)->reg(ra_,this,idx3)/* op2 */), *(opnd_array(4)->label()));
  
#line 13769 "ad_riscv.cpp"
  }
}

void cmpL_loopNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8789 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmp_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), as_Register(opnd_array(3)->reg(ra_,this,idx3)/* op2 */), *(opnd_array(4)->label()));
  
#line 13788 "ad_riscv.cpp"
  }
}

void cmpUL_branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8808 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmp_branch(opnd_array(1)->ccode()| C2_MacroAssembler::unsigned_branch_mask, as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */),
                  as_Register(opnd_array(3)->reg(ra_,this,idx3)/* op2 */), *(opnd_array(4)->label()));
  
#line 13808 "ad_riscv.cpp"
  }
}

void cmpUL_loopNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8827 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmp_branch(opnd_array(1)->ccode()| C2_MacroAssembler::unsigned_branch_mask, as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */),
                  as_Register(opnd_array(3)->reg(ra_,this,idx3)/* op2 */), *(opnd_array(4)->label()));
  
#line 13828 "ad_riscv.cpp"
  }
}

void cmpP_branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8848 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmp_branch(opnd_array(1)->ccode()| C2_MacroAssembler::unsigned_branch_mask, as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */),
                  as_Register(opnd_array(3)->reg(ra_,this,idx3)/* op2 */), *(opnd_array(4)->label()));
  
#line 13848 "ad_riscv.cpp"
  }
}

void cmpP_loopNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8868 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmp_branch(opnd_array(1)->ccode()| C2_MacroAssembler::unsigned_branch_mask, as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */),
                  as_Register(opnd_array(3)->reg(ra_,this,idx3)/* op2 */), *(opnd_array(4)->label()));
  
#line 13868 "ad_riscv.cpp"
  }
}

void cmpN_branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8889 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmp_branch(opnd_array(1)->ccode()| C2_MacroAssembler::unsigned_branch_mask, as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */),
                  as_Register(opnd_array(3)->reg(ra_,this,idx3)/* op2 */), *(opnd_array(4)->label()));
  
#line 13888 "ad_riscv.cpp"
  }
}

void cmpN_loopNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8909 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmp_branch(opnd_array(1)->ccode()| C2_MacroAssembler::unsigned_branch_mask, as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */),
                  as_Register(opnd_array(3)->reg(ra_,this,idx3)/* op2 */), *(opnd_array(4)->label()));
  
#line 13908 "ad_riscv.cpp"
  }
}

void cmpF_branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8929 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ float_cmp_branch(opnd_array(1)->ccode(), as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), as_FloatRegister(opnd_array(3)->reg(ra_,this,idx3)/* op2 */), *(opnd_array(4)->label()));
  
#line 13927 "ad_riscv.cpp"
  }
}

void cmpF_loopNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8946 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ float_cmp_branch(opnd_array(1)->ccode(), as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), as_FloatRegister(opnd_array(3)->reg(ra_,this,idx3)/* op2 */), *(opnd_array(4)->label()));
  
#line 13946 "ad_riscv.cpp"
  }
}

void cmpD_branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8964 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ float_cmp_branch(opnd_array(1)->ccode()| C2_MacroAssembler::double_branch_mask, as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* op1 */),
                        as_FloatRegister(opnd_array(3)->reg(ra_,this,idx3)/* op2 */), *(opnd_array(4)->label()));
  
#line 13966 "ad_riscv.cpp"
  }
}

void cmpD_loopNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 8982 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ float_cmp_branch(opnd_array(1)->ccode()| C2_MacroAssembler::double_branch_mask, as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* op1 */),
                        as_FloatRegister(opnd_array(3)->reg(ra_,this,idx3)/* op2 */), *(opnd_array(4)->label()));
  
#line 13986 "ad_riscv.cpp"
  }
}

void cmpI_reg_imm0_branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9002 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmp_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), zr, *(opnd_array(4)->label()));
  
#line 14005 "ad_riscv.cpp"
  }
}

void cmpI_reg_imm0_loopNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9021 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmp_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), zr, *(opnd_array(4)->label()));
  
#line 14024 "ad_riscv.cpp"
  }
}

void cmpUEqNeLeGt_reg_imm0_branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9041 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ enc_cmpUEqNeLeGt_imm0_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), *(opnd_array(4)->label()));
  
#line 14043 "ad_riscv.cpp"
  }
}

void cmpUEqNeLeGt_reg_imm0_loopNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9061 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ enc_cmpUEqNeLeGt_imm0_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), *(opnd_array(4)->label()));
  
#line 14062 "ad_riscv.cpp"
  }
}

void cmpL_reg_imm0_branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9081 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmp_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), zr, *(opnd_array(4)->label()));
  
#line 14081 "ad_riscv.cpp"
  }
}

void cmpL_reg_imm0_loopNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9100 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmp_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), zr, *(opnd_array(4)->label()));
  
#line 14100 "ad_riscv.cpp"
  }
}

void cmpULEqNeLeGt_reg_imm0_branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9120 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ enc_cmpUEqNeLeGt_imm0_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), *(opnd_array(4)->label()));
  
#line 14119 "ad_riscv.cpp"
  }
}

void cmpULEqNeLeGt_reg_imm0_loopNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9139 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ enc_cmpUEqNeLeGt_imm0_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), *(opnd_array(4)->label()));
  
#line 14138 "ad_riscv.cpp"
  }
}

void cmpP_imm0_branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9156 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ enc_cmpEqNe_imm0_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), *(opnd_array(4)->label()));
  
#line 14157 "ad_riscv.cpp"
  }
}

void cmpP_imm0_loopNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9172 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ enc_cmpEqNe_imm0_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), *(opnd_array(4)->label()));
  
#line 14176 "ad_riscv.cpp"
  }
}

void cmpN_imm0_branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9190 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ enc_cmpEqNe_imm0_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), *(opnd_array(4)->label()));
  
#line 14195 "ad_riscv.cpp"
  }
}

void cmpN_imm0_loopNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9207 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ enc_cmpEqNe_imm0_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), *(opnd_array(4)->label()));
  
#line 14214 "ad_riscv.cpp"
  }
}

void cmpP_narrowOop_imm0_branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9224 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ enc_cmpEqNe_imm0_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), *(opnd_array(4)->label()));
  
#line 14233 "ad_riscv.cpp"
  }
}

void cmpP_narrowOop_imm0_loopNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9240 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ enc_cmpEqNe_imm0_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), *(opnd_array(4)->label()));
  
#line 14252 "ad_riscv.cpp"
  }
}

void far_cmpFlag_branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// cr
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// lbl
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9257 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ enc_cmpEqNe_imm0_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* cr */), *(opnd_array(3)->label()), /* is_far */ true);
  
#line 14270 "ad_riscv.cpp"
  }
}

void far_cmpI_branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9275 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmp_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), as_Register(opnd_array(3)->reg(ra_,this,idx3)/* op2 */), *(opnd_array(4)->label()), /* is_far */ true);
  
#line 14289 "ad_riscv.cpp"
  }
}

void far_cmpI_loopNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9289 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmp_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), as_Register(opnd_array(3)->reg(ra_,this,idx3)/* op2 */), *(opnd_array(4)->label()), /* is_far */ true);
  
#line 14308 "ad_riscv.cpp"
  }
}

void far_cmpU_branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9303 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmp_branch(opnd_array(1)->ccode()| C2_MacroAssembler::unsigned_branch_mask, as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */),
                       as_Register(opnd_array(3)->reg(ra_,this,idx3)/* op2 */), *(opnd_array(4)->label()), /* is_far */ true);
  
#line 14328 "ad_riscv.cpp"
  }
}

void far_cmpU_loopNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9318 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmp_branch(opnd_array(1)->ccode()| C2_MacroAssembler::unsigned_branch_mask, as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */),
                       as_Register(opnd_array(3)->reg(ra_,this,idx3)/* op2 */), *(opnd_array(4)->label()), /* is_far */ true);
  
#line 14348 "ad_riscv.cpp"
  }
}

void far_cmpL_branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9333 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmp_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), as_Register(opnd_array(3)->reg(ra_,this,idx3)/* op2 */), *(opnd_array(4)->label()), /* is_far */ true);
  
#line 14367 "ad_riscv.cpp"
  }
}

void far_cmpLloopNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9347 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmp_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), as_Register(opnd_array(3)->reg(ra_,this,idx3)/* op2 */), *(opnd_array(4)->label()), /* is_far */ true);
  
#line 14386 "ad_riscv.cpp"
  }
}

void far_cmpUL_branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9361 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmp_branch(opnd_array(1)->ccode()| C2_MacroAssembler::unsigned_branch_mask, as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */),
                       as_Register(opnd_array(3)->reg(ra_,this,idx3)/* op2 */), *(opnd_array(4)->label()), /* is_far */ true);
  
#line 14406 "ad_riscv.cpp"
  }
}

void far_cmpUL_loopNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9376 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmp_branch(opnd_array(1)->ccode()| C2_MacroAssembler::unsigned_branch_mask, as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */),
                       as_Register(opnd_array(3)->reg(ra_,this,idx3)/* op2 */), *(opnd_array(4)->label()), /* is_far */ true);
  
#line 14426 "ad_riscv.cpp"
  }
}

void far_cmpP_branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9394 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmp_branch(opnd_array(1)->ccode()| C2_MacroAssembler::unsigned_branch_mask, as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */),
                       as_Register(opnd_array(3)->reg(ra_,this,idx3)/* op2 */), *(opnd_array(4)->label()), /* is_far */ true);
  
#line 14446 "ad_riscv.cpp"
  }
}

void far_cmpP_loopNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9412 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmp_branch(opnd_array(1)->ccode()| C2_MacroAssembler::unsigned_branch_mask, as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */),
                       as_Register(opnd_array(3)->reg(ra_,this,idx3)/* op2 */), *(opnd_array(4)->label()), /* is_far */ true);
  
#line 14466 "ad_riscv.cpp"
  }
}

void far_cmpN_branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9430 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmp_branch(opnd_array(1)->ccode()| C2_MacroAssembler::unsigned_branch_mask, as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */),
                       as_Register(opnd_array(3)->reg(ra_,this,idx3)/* op2 */), *(opnd_array(4)->label()), /* is_far */ true);
  
#line 14486 "ad_riscv.cpp"
  }
}

void far_cmpN_loopNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9448 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmp_branch(opnd_array(1)->ccode()| C2_MacroAssembler::unsigned_branch_mask, as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */),
                  as_Register(opnd_array(3)->reg(ra_,this,idx3)/* op2 */), *(opnd_array(4)->label()), /* is_far */ true);
  
#line 14506 "ad_riscv.cpp"
  }
}

void far_cmpF_branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9466 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ float_cmp_branch(opnd_array(1)->ccode(), as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), as_FloatRegister(opnd_array(3)->reg(ra_,this,idx3)/* op2 */),
                        *(opnd_array(4)->label()), /* is_far */ true);
  
#line 14526 "ad_riscv.cpp"
  }
}

void far_cmpF_loopNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9482 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ float_cmp_branch(opnd_array(1)->ccode(), as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), as_FloatRegister(opnd_array(3)->reg(ra_,this,idx3)/* op2 */),
                        *(opnd_array(4)->label()), /* is_far */ true);
  
#line 14546 "ad_riscv.cpp"
  }
}

void far_cmpD_branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9499 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ float_cmp_branch(opnd_array(1)->ccode()| C2_MacroAssembler::double_branch_mask, as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* op1 */),
                        as_FloatRegister(opnd_array(3)->reg(ra_,this,idx3)/* op2 */), *(opnd_array(4)->label()), /* is_far */ true);
  
#line 14566 "ad_riscv.cpp"
  }
}

void far_cmpD_loopNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9515 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ float_cmp_branch(opnd_array(1)->ccode()| C2_MacroAssembler::double_branch_mask, as_FloatRegister(opnd_array(2)->reg(ra_,this,idx2)/* op1 */),
                        as_FloatRegister(opnd_array(3)->reg(ra_,this,idx3)/* op2 */), *(opnd_array(4)->label()), /* is_far */ true);
  
#line 14586 "ad_riscv.cpp"
  }
}

void far_cmpI_reg_imm0_branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9533 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmp_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), zr, *(opnd_array(4)->label()), /* is_far */ true);
  
#line 14605 "ad_riscv.cpp"
  }
}

void far_cmpI_reg_imm0_loopNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9550 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmp_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), zr, *(opnd_array(4)->label()), /* is_far */ true);
  
#line 14624 "ad_riscv.cpp"
  }
}

void far_cmpUEqNeLeGt_imm0_branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9567 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ enc_cmpUEqNeLeGt_imm0_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), *(opnd_array(4)->label()), /* is_far */ true);
  
#line 14643 "ad_riscv.cpp"
  }
}

void far_cmpUEqNeLeGt_reg_imm0_loopNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9585 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ enc_cmpUEqNeLeGt_imm0_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), *(opnd_array(4)->label()), /* is_far */ true);
  
#line 14662 "ad_riscv.cpp"
  }
}

void far_cmpULtGe_reg_imm0_branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {

#line 2239 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    Label* L = opnd_array(4)->label();
    switch (opnd_array(1)->ccode()) {
      case(BoolTest::ge):
        __ j(*L);
        break;
      case(BoolTest::lt):
        break;
      default:
        Unimplemented();
    }
  
#line 14690 "ad_riscv.cpp"
  }
}

void far_cmpULtGe_reg_imm0_loopNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {

#line 2239 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    Label* L = opnd_array(4)->label();
    switch (opnd_array(1)->ccode()) {
      case(BoolTest::ge):
        __ j(*L);
        break;
      case(BoolTest::lt):
        break;
      default:
        Unimplemented();
    }
  
#line 14718 "ad_riscv.cpp"
  }
}

void far_cmpL_reg_imm0_branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9633 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmp_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), zr, *(opnd_array(4)->label()), /* is_far */ true);
  
#line 14737 "ad_riscv.cpp"
  }
}

void far_cmpL_reg_imm0_loopNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9650 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ cmp_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), zr, *(opnd_array(4)->label()), /* is_far */ true);
  
#line 14756 "ad_riscv.cpp"
  }
}

void far_cmpULEqNeLeGt_reg_imm0_branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9667 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ enc_cmpUEqNeLeGt_imm0_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), *(opnd_array(4)->label()), /* is_far */ true);
  
#line 14775 "ad_riscv.cpp"
  }
}

void far_cmpULEqNeLeGt_reg_imm0_loopNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9684 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ enc_cmpUEqNeLeGt_imm0_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), *(opnd_array(4)->label()), /* is_far */ true);
  
#line 14794 "ad_riscv.cpp"
  }
}

void far_cmpULLtGe_reg_imm0_branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {

#line 2239 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    Label* L = opnd_array(4)->label();
    switch (opnd_array(1)->ccode()) {
      case(BoolTest::ge):
        __ j(*L);
        break;
      case(BoolTest::lt):
        break;
      default:
        Unimplemented();
    }
  
#line 14822 "ad_riscv.cpp"
  }
}

void far_cmpULLtGe_reg_imm0_loopNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {

#line 2239 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    Label* L = opnd_array(4)->label();
    switch (opnd_array(1)->ccode()) {
      case(BoolTest::ge):
        __ j(*L);
        break;
      case(BoolTest::lt):
        break;
      default:
        Unimplemented();
    }
  
#line 14850 "ad_riscv.cpp"
  }
}

void far_cmpP_imm0_branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9729 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ enc_cmpEqNe_imm0_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), *(opnd_array(4)->label()), /* is_far */ true);
  
#line 14869 "ad_riscv.cpp"
  }
}

void far_cmpP_imm0_loopNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9743 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ enc_cmpEqNe_imm0_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), *(opnd_array(4)->label()), /* is_far */ true);
  
#line 14888 "ad_riscv.cpp"
  }
}

void far_cmpN_imm0_branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9758 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ enc_cmpEqNe_imm0_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), *(opnd_array(4)->label()), /* is_far */ true);
  
#line 14907 "ad_riscv.cpp"
  }
}

void far_cmpN_imm0_loopNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9773 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ enc_cmpEqNe_imm0_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), *(opnd_array(4)->label()), /* is_far */ true);
  
#line 14926 "ad_riscv.cpp"
  }
}

void far_cmpP_narrowOop_imm0_branchNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9787 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ enc_cmpEqNe_imm0_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), *(opnd_array(4)->label()), /* is_far */ true);
  
#line 14945 "ad_riscv.cpp"
  }
}

void far_cmpP_narrowOop_imm0_loopNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// op1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// zero
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// lbl
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9801 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ enc_cmpEqNe_imm0_branch(opnd_array(1)->ccode(), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), *(opnd_array(4)->label()), /* is_far */ true);
  
#line 14964 "ad_riscv.cpp"
  }
}

void cmovI_cmpINode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// cop
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// op2
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// dst
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9820 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ enc_cmove(opnd_array(1)->ccode(),
                 as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), as_Register(opnd_array(3)->reg(ra_,this,idx3)/* op2 */),
                 as_Register(opnd_array(4)->reg(ra_,this,idx4)/* dst */), as_Register(opnd_array(5)->reg(ra_,this,idx5)/* src */));
  
#line 14986 "ad_riscv.cpp"
  }
}

void cmovI_cmpUNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// cop
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// op2
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// dst
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9839 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ enc_cmove(opnd_array(1)->ccode()| C2_MacroAssembler::unsigned_branch_mask,
                 as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), as_Register(opnd_array(3)->reg(ra_,this,idx3)/* op2 */),
                 as_Register(opnd_array(4)->reg(ra_,this,idx4)/* dst */), as_Register(opnd_array(5)->reg(ra_,this,idx5)/* src */));
  
#line 15008 "ad_riscv.cpp"
  }
}

void cmovI_cmpLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// cop
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// op2
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// dst
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9858 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ enc_cmove(opnd_array(1)->ccode(),
                 as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), as_Register(opnd_array(3)->reg(ra_,this,idx3)/* op2 */),
                 as_Register(opnd_array(4)->reg(ra_,this,idx4)/* dst */), as_Register(opnd_array(5)->reg(ra_,this,idx5)/* src */));
  
#line 15030 "ad_riscv.cpp"
  }
}

void cmovL_cmpLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// cop
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// op2
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// dst
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9877 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ enc_cmove(opnd_array(1)->ccode(),
                 as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), as_Register(opnd_array(3)->reg(ra_,this,idx3)/* op2 */),
                 as_Register(opnd_array(4)->reg(ra_,this,idx4)/* dst */), as_Register(opnd_array(5)->reg(ra_,this,idx5)/* src */));
  
#line 15052 "ad_riscv.cpp"
  }
}

void cmovL_cmpULNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// cop
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// op2
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// dst
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9896 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ enc_cmove(opnd_array(1)->ccode()| C2_MacroAssembler::unsigned_branch_mask,
                 as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), as_Register(opnd_array(3)->reg(ra_,this,idx3)/* op2 */),
                 as_Register(opnd_array(4)->reg(ra_,this,idx4)/* dst */), as_Register(opnd_array(5)->reg(ra_,this,idx5)/* src */));
  
#line 15074 "ad_riscv.cpp"
  }
}

void cmovI_cmpULNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// cop
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// op1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// op2
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// dst
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 9914 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ enc_cmove(opnd_array(1)->ccode()| C2_MacroAssembler::unsigned_branch_mask,
                 as_Register(opnd_array(2)->reg(ra_,this,idx2)/* op1 */), as_Register(opnd_array(3)->reg(ra_,this,idx3)/* op2 */),
                 as_Register(opnd_array(4)->reg(ra_,this,idx4)/* dst */), as_Register(opnd_array(5)->reg(ra_,this,idx5)/* src */));
  
#line 15096 "ad_riscv.cpp"
  }
}

void CallStaticJavaDirectNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// 
  {

#line 2282 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    Assembler::IncompressibleRegion ir(&_masm);  // Fixed length: see ret_addr_offset

    address addr = (address)opnd_array(1)->method();
    address call = NULL;
    assert_cond(addr != NULL);
    if (!_method) {
      // A call to a runtime wrapper, e.g. new, new_typeArray_Java, uncommon_trap.
      call = __ trampoline_call(Address(addr, relocInfo::runtime_call_type));
      if (call == NULL) {
        ciEnv::current()->record_failure("CodeCache is full");
        return;
      }
    } else {
      int method_index = resolved_method_index(cbuf);
      RelocationHolder rspec = _optimized_virtual ? opt_virtual_call_Relocation::spec(method_index)
                                                  : static_call_Relocation::spec(method_index);
      call = __ trampoline_call(Address(addr, rspec));
      if (call == NULL) {
        ciEnv::current()->record_failure("CodeCache is full");
        return;
      }

      if (CodeBuffer::supports_shared_stubs() && _method->can_be_statically_bound()) {
        // Calls of the same statically bound method can share
        // a stub to the interpreter.
        cbuf.shared_stub_to_interp_for(_method, call - cbuf.insts_begin());
      } else {
        // Emit stub for static call
        address stub = CompiledStaticCall::emit_to_interp_stub(cbuf, call);
        if (stub == NULL) {
          ciEnv::current()->record_failure("CodeCache is full");
          return;
        }
      }
    }

    __ post_call_nop();
  
#line 15148 "ad_riscv.cpp"
  }
  {

#line 2336 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    if (VerifyStackAtCalls) {
      // Check that stack depth is unchanged: find majik cookie on stack
      __ call_Unimplemented();
    }
  
#line 15160 "ad_riscv.cpp"
  }
}

void CallDynamicJavaDirectNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// cr
  {

#line 2323 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    Assembler::IncompressibleRegion ir(&_masm);  // Fixed length: see ret_addr_offset
    int method_index = resolved_method_index(cbuf);
    address call = __ ic_call((address)opnd_array(1)->method(), method_index);
    if (call == NULL) {
      ciEnv::current()->record_failure("CodeCache is full");
      return;
    }

    __ post_call_nop();
  
#line 15184 "ad_riscv.cpp"
  }
  {

#line 2336 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    if (VerifyStackAtCalls) {
      // Check that stack depth is unchanged: find majik cookie on stack
      __ call_Unimplemented();
    }
  
#line 15196 "ad_riscv.cpp"
  }
}

void CallRuntimeDirectNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// cr
  {

#line 2344 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    Assembler::IncompressibleRegion ir(&_masm);  // Fixed length: see ret_addr_offset

    // some calls to generated routines (arraycopy code) are scheduled
    // by C2 as runtime calls. if so we can call them using a jr (they
    // will be in a reachable segment) otherwise we have to use a jalr
    // which loads the absolute address into a register.
    address entry = (address)opnd_array(1)->method();
    CodeBlob *cb = CodeCache::find_blob(entry);
    if (cb != NULL) {
      address call = __ trampoline_call(Address(entry, relocInfo::runtime_call_type));
      if (call == NULL) {
        ciEnv::current()->record_failure("CodeCache is full");
        return;
      }
      __ post_call_nop();
    } else {
      Label retaddr;
      __ la(t1, retaddr);
      __ la(t0, RuntimeAddress(entry));
      // Leave a breadcrumb for JavaFrameAnchor::capture_last_Java_pc()
      __ addi(sp, sp, -2 * wordSize);
      __ sd(t1, Address(sp, wordSize));
      __ jalr(t0);
      __ bind(retaddr);
      __ post_call_nop();
      __ addi(sp, sp, 2 * wordSize);
    }
  
#line 15238 "ad_riscv.cpp"
  }
}

void CallLeafDirectNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// cr
  {

#line 2344 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    Assembler::IncompressibleRegion ir(&_masm);  // Fixed length: see ret_addr_offset

    // some calls to generated routines (arraycopy code) are scheduled
    // by C2 as runtime calls. if so we can call them using a jr (they
    // will be in a reachable segment) otherwise we have to use a jalr
    // which loads the absolute address into a register.
    address entry = (address)opnd_array(1)->method();
    CodeBlob *cb = CodeCache::find_blob(entry);
    if (cb != NULL) {
      address call = __ trampoline_call(Address(entry, relocInfo::runtime_call_type));
      if (call == NULL) {
        ciEnv::current()->record_failure("CodeCache is full");
        return;
      }
      __ post_call_nop();
    } else {
      Label retaddr;
      __ la(t1, retaddr);
      __ la(t0, RuntimeAddress(entry));
      // Leave a breadcrumb for JavaFrameAnchor::capture_last_Java_pc()
      __ addi(sp, sp, -2 * wordSize);
      __ sd(t1, Address(sp, wordSize));
      __ jalr(t0);
      __ bind(retaddr);
      __ post_call_nop();
      __ addi(sp, sp, 2 * wordSize);
    }
  
#line 15280 "ad_riscv.cpp"
  }
}

void CallLeafNoFPDirectNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// cr
  {

#line 2344 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    Assembler::IncompressibleRegion ir(&_masm);  // Fixed length: see ret_addr_offset

    // some calls to generated routines (arraycopy code) are scheduled
    // by C2 as runtime calls. if so we can call them using a jr (they
    // will be in a reachable segment) otherwise we have to use a jalr
    // which loads the absolute address into a register.
    address entry = (address)opnd_array(1)->method();
    CodeBlob *cb = CodeCache::find_blob(entry);
    if (cb != NULL) {
      address call = __ trampoline_call(Address(entry, relocInfo::runtime_call_type));
      if (call == NULL) {
        ciEnv::current()->record_failure("CodeCache is full");
        return;
      }
      __ post_call_nop();
    } else {
      Label retaddr;
      __ la(t1, retaddr);
      __ la(t0, RuntimeAddress(entry));
      // Leave a breadcrumb for JavaFrameAnchor::capture_last_Java_pc()
      __ addi(sp, sp, -2 * wordSize);
      __ sd(t1, Address(sp, wordSize));
      __ jalr(t0);
      __ bind(retaddr);
      __ post_call_nop();
      __ addi(sp, sp, 2 * wordSize);
    }
  
#line 15322 "ad_riscv.cpp"
  }
}

void partialSubtypeCheckNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// sub
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// super
  {

#line 2255 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    Register sub_reg = as_Register(opnd_array(1)->reg(ra_,this,idx1)/* sub */);
    Register super_reg = as_Register(opnd_array(2)->reg(ra_,this,idx2)/* super */);
    Register temp_reg = as_Register(R12_enc);
    Register result_reg = as_Register(opnd_array(0)->reg(ra_,this)/* result */);
    Register cr_reg = t1;

    Label miss;
    Label done;
    C2_MacroAssembler _masm(&cbuf);
    __ check_klass_subtype_slow_path(sub_reg, super_reg, temp_reg, result_reg,
                                     NULL, &miss);
    if ((0x1 /*primary()*/)) {
      __ mv(result_reg, zr);
    } else {
      __ mv(cr_reg, zr);
      __ j(done);
    }

    __ bind(miss);
    if (!(0x1 /*primary()*/)) {
      __ mv(cr_reg, 1);
    }

    __ bind(done);
  
#line 15361 "ad_riscv.cpp"
  }
}

void partialSubtypeCheckVsZeroNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// sub
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// super
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// zero
  {

#line 2255 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    Register sub_reg = as_Register(opnd_array(1)->reg(ra_,this,idx1)/* sub */);
    Register super_reg = as_Register(opnd_array(2)->reg(ra_,this,idx2)/* super */);
    Register temp_reg = as_Register(R12_enc);
    Register result_reg = as_Register(R15_enc);
    Register cr_reg = t1;

    Label miss;
    Label done;
    C2_MacroAssembler _masm(&cbuf);
    __ check_klass_subtype_slow_path(sub_reg, super_reg, temp_reg, result_reg,
                                     NULL, &miss);
    if ((0x0 /*primary()*/)) {
      __ mv(result_reg, zr);
    } else {
      __ mv(cr_reg, zr);
      __ j(done);
    }

    __ bind(miss);
    if (!(0x0 /*primary()*/)) {
      __ mv(cr_reg, 1);
    }

    __ bind(done);
  
#line 15401 "ad_riscv.cpp"
  }
}

void string_compareUNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// str1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// cnt1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// str2
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// cnt2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 10067 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    // Count is in 8-bit bytes; non-Compact chars are 16 bits.
    __ string_compare(opnd_array(1)->as_Register(ra_,this,idx1)/* str1 */, opnd_array(3)->as_Register(ra_,this,idx3)/* str2 */,
                      opnd_array(2)->as_Register(ra_,this,idx2)/* cnt1 */, opnd_array(4)->as_Register(ra_,this,idx4)/* cnt2 */, opnd_array(0)->as_Register(ra_,this)/* result */,
                      as_Register(R28_enc), as_Register(R29_enc), as_Register(R30_enc),
                      StrIntrinsicNode::UU);
  
#line 15424 "ad_riscv.cpp"
  }
}

void string_compareLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// str1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// cnt1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// str2
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// cnt2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 10085 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ string_compare(opnd_array(1)->as_Register(ra_,this,idx1)/* str1 */, opnd_array(3)->as_Register(ra_,this,idx3)/* str2 */,
                      opnd_array(2)->as_Register(ra_,this,idx2)/* cnt1 */, opnd_array(4)->as_Register(ra_,this,idx4)/* cnt2 */, opnd_array(0)->as_Register(ra_,this)/* result */,
                      as_Register(R28_enc), as_Register(R29_enc), as_Register(R30_enc),
                      StrIntrinsicNode::LL);
  
#line 15446 "ad_riscv.cpp"
  }
}

void string_compareULNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// str1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// cnt1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// str2
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// cnt2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 10102 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ string_compare(opnd_array(1)->as_Register(ra_,this,idx1)/* str1 */, opnd_array(3)->as_Register(ra_,this,idx3)/* str2 */,
                      opnd_array(2)->as_Register(ra_,this,idx2)/* cnt1 */, opnd_array(4)->as_Register(ra_,this,idx4)/* cnt2 */, opnd_array(0)->as_Register(ra_,this)/* result */,
                      as_Register(R28_enc), as_Register(R29_enc), as_Register(R30_enc),
                      StrIntrinsicNode::UL);
  
#line 15468 "ad_riscv.cpp"
  }
}

void string_compareLUNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// str1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// cnt1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// str2
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// cnt2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 10120 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ string_compare(opnd_array(1)->as_Register(ra_,this,idx1)/* str1 */, opnd_array(3)->as_Register(ra_,this,idx3)/* str2 */,
                      opnd_array(2)->as_Register(ra_,this,idx2)/* cnt1 */, opnd_array(4)->as_Register(ra_,this,idx4)/* cnt2 */, opnd_array(0)->as_Register(ra_,this)/* result */,
                      as_Register(R28_enc), as_Register(R29_enc), as_Register(R30_enc),
                      StrIntrinsicNode::LU);
  
#line 15490 "ad_riscv.cpp"
  }
}

void string_indexofUUNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// str1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// cnt1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// str2
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// cnt2
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// result
  unsigned idx6 = idx5 + opnd_array(5)->num_edges(); 	// tmp1
  unsigned idx7 = idx6 + opnd_array(6)->num_edges(); 	// tmp2
  unsigned idx8 = idx7 + opnd_array(7)->num_edges(); 	// tmp3
  unsigned idx9 = idx8 + opnd_array(8)->num_edges(); 	// tmp4
  unsigned idx10 = idx9 + opnd_array(9)->num_edges(); 	// tmp5
  unsigned idx11 = idx10 + opnd_array(10)->num_edges(); 	// tmp6
  {
    C2_MacroAssembler _masm(&cbuf);

#line 10139 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ string_indexof(opnd_array(1)->as_Register(ra_,this,idx1)/* str1 */, opnd_array(3)->as_Register(ra_,this,idx3)/* str2 */,
                      opnd_array(2)->as_Register(ra_,this,idx2)/* cnt1 */, opnd_array(4)->as_Register(ra_,this,idx4)/* cnt2 */,
                      opnd_array(6)->as_Register(ra_,this,idx6)/* tmp1 */, opnd_array(7)->as_Register(ra_,this,idx7)/* tmp2 */,
                      opnd_array(8)->as_Register(ra_,this,idx8)/* tmp3 */, opnd_array(9)->as_Register(ra_,this,idx9)/* tmp4 */,
                      opnd_array(10)->as_Register(ra_,this,idx10)/* tmp5 */, opnd_array(11)->as_Register(ra_,this,idx11)/* tmp6 */,
                      opnd_array(5)->as_Register(ra_,this,idx5)/* result */, StrIntrinsicNode::UU);
  
#line 15521 "ad_riscv.cpp"
  }
}

void string_indexofLLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// str1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// cnt1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// str2
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// cnt2
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// result
  unsigned idx6 = idx5 + opnd_array(5)->num_edges(); 	// tmp1
  unsigned idx7 = idx6 + opnd_array(6)->num_edges(); 	// tmp2
  unsigned idx8 = idx7 + opnd_array(7)->num_edges(); 	// tmp3
  unsigned idx9 = idx8 + opnd_array(8)->num_edges(); 	// tmp4
  unsigned idx10 = idx9 + opnd_array(9)->num_edges(); 	// tmp5
  unsigned idx11 = idx10 + opnd_array(10)->num_edges(); 	// tmp6
  {
    C2_MacroAssembler _masm(&cbuf);

#line 10160 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ string_indexof(opnd_array(1)->as_Register(ra_,this,idx1)/* str1 */, opnd_array(3)->as_Register(ra_,this,idx3)/* str2 */,
                      opnd_array(2)->as_Register(ra_,this,idx2)/* cnt1 */, opnd_array(4)->as_Register(ra_,this,idx4)/* cnt2 */,
                      opnd_array(6)->as_Register(ra_,this,idx6)/* tmp1 */, opnd_array(7)->as_Register(ra_,this,idx7)/* tmp2 */,
                      opnd_array(8)->as_Register(ra_,this,idx8)/* tmp3 */, opnd_array(9)->as_Register(ra_,this,idx9)/* tmp4 */,
                      opnd_array(10)->as_Register(ra_,this,idx10)/* tmp5 */, opnd_array(11)->as_Register(ra_,this,idx11)/* tmp6 */,
                      opnd_array(5)->as_Register(ra_,this,idx5)/* result */, StrIntrinsicNode::LL);
  
#line 15552 "ad_riscv.cpp"
  }
}

void string_indexofULNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// str1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// cnt1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// str2
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// cnt2
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// result
  unsigned idx6 = idx5 + opnd_array(5)->num_edges(); 	// tmp1
  unsigned idx7 = idx6 + opnd_array(6)->num_edges(); 	// tmp2
  unsigned idx8 = idx7 + opnd_array(7)->num_edges(); 	// tmp3
  unsigned idx9 = idx8 + opnd_array(8)->num_edges(); 	// tmp4
  unsigned idx10 = idx9 + opnd_array(9)->num_edges(); 	// tmp5
  unsigned idx11 = idx10 + opnd_array(10)->num_edges(); 	// tmp6
  {
    C2_MacroAssembler _masm(&cbuf);

#line 10181 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ string_indexof(opnd_array(1)->as_Register(ra_,this,idx1)/* str1 */, opnd_array(3)->as_Register(ra_,this,idx3)/* str2 */,
                      opnd_array(2)->as_Register(ra_,this,idx2)/* cnt1 */, opnd_array(4)->as_Register(ra_,this,idx4)/* cnt2 */,
                      opnd_array(6)->as_Register(ra_,this,idx6)/* tmp1 */, opnd_array(7)->as_Register(ra_,this,idx7)/* tmp2 */,
                      opnd_array(8)->as_Register(ra_,this,idx8)/* tmp3 */, opnd_array(9)->as_Register(ra_,this,idx9)/* tmp4 */,
                      opnd_array(10)->as_Register(ra_,this,idx10)/* tmp5 */, opnd_array(11)->as_Register(ra_,this,idx11)/* tmp6 */,
                      opnd_array(5)->as_Register(ra_,this,idx5)/* result */, StrIntrinsicNode::UL);
  
#line 15583 "ad_riscv.cpp"
  }
}

void string_indexof_conUUNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// str1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// cnt1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// str2
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// int_cnt2
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// result
  unsigned idx6 = idx5 + opnd_array(5)->num_edges(); 	// tmp1
  unsigned idx7 = idx6 + opnd_array(6)->num_edges(); 	// tmp2
  unsigned idx8 = idx7 + opnd_array(7)->num_edges(); 	// tmp3
  unsigned idx9 = idx8 + opnd_array(8)->num_edges(); 	// tmp4
  {
    C2_MacroAssembler _masm(&cbuf);

#line 10203 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    int icnt2 = (int)opnd_array(4)->constant();
    __ string_indexof_linearscan(opnd_array(1)->as_Register(ra_,this,idx1)/* str1 */, opnd_array(3)->as_Register(ra_,this,idx3)/* str2 */,
                                 opnd_array(2)->as_Register(ra_,this,idx2)/* cnt1 */, zr,
                                 opnd_array(6)->as_Register(ra_,this,idx6)/* tmp1 */, opnd_array(7)->as_Register(ra_,this,idx7)/* tmp2 */,
                                 opnd_array(8)->as_Register(ra_,this,idx8)/* tmp3 */, opnd_array(9)->as_Register(ra_,this,idx9)/* tmp4 */,
                                 icnt2, opnd_array(5)->as_Register(ra_,this,idx5)/* result */, StrIntrinsicNode::UU);
  
#line 15612 "ad_riscv.cpp"
  }
}

void string_indexof_conLLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// str1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// cnt1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// str2
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// int_cnt2
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// result
  unsigned idx6 = idx5 + opnd_array(5)->num_edges(); 	// tmp1
  unsigned idx7 = idx6 + opnd_array(6)->num_edges(); 	// tmp2
  unsigned idx8 = idx7 + opnd_array(7)->num_edges(); 	// tmp3
  unsigned idx9 = idx8 + opnd_array(8)->num_edges(); 	// tmp4
  {
    C2_MacroAssembler _masm(&cbuf);

#line 10224 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    int icnt2 = (int)opnd_array(4)->constant();
    __ string_indexof_linearscan(opnd_array(1)->as_Register(ra_,this,idx1)/* str1 */, opnd_array(3)->as_Register(ra_,this,idx3)/* str2 */,
                                 opnd_array(2)->as_Register(ra_,this,idx2)/* cnt1 */, zr,
                                 opnd_array(6)->as_Register(ra_,this,idx6)/* tmp1 */, opnd_array(7)->as_Register(ra_,this,idx7)/* tmp2 */,
                                 opnd_array(8)->as_Register(ra_,this,idx8)/* tmp3 */, opnd_array(9)->as_Register(ra_,this,idx9)/* tmp4 */,
                                 icnt2, opnd_array(5)->as_Register(ra_,this,idx5)/* result */, StrIntrinsicNode::LL);
  
#line 15641 "ad_riscv.cpp"
  }
}

void string_indexof_conULNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// str1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// cnt1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// str2
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// int_cnt2
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// result
  unsigned idx6 = idx5 + opnd_array(5)->num_edges(); 	// tmp1
  unsigned idx7 = idx6 + opnd_array(6)->num_edges(); 	// tmp2
  unsigned idx8 = idx7 + opnd_array(7)->num_edges(); 	// tmp3
  unsigned idx9 = idx8 + opnd_array(8)->num_edges(); 	// tmp4
  {
    C2_MacroAssembler _masm(&cbuf);

#line 10245 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    int icnt2 = (int)opnd_array(4)->constant();
    __ string_indexof_linearscan(opnd_array(1)->as_Register(ra_,this,idx1)/* str1 */, opnd_array(3)->as_Register(ra_,this,idx3)/* str2 */,
                                 opnd_array(2)->as_Register(ra_,this,idx2)/* cnt1 */, zr,
                                 opnd_array(6)->as_Register(ra_,this,idx6)/* tmp1 */, opnd_array(7)->as_Register(ra_,this,idx7)/* tmp2 */,
                                 opnd_array(8)->as_Register(ra_,this,idx8)/* tmp3 */, opnd_array(9)->as_Register(ra_,this,idx9)/* tmp4 */,
                                 icnt2, opnd_array(5)->as_Register(ra_,this,idx5)/* result */, StrIntrinsicNode::UL);
  
#line 15670 "ad_riscv.cpp"
  }
}

void stringU_indexof_charNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// str1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// cnt1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// ch
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// result
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// tmp1
  unsigned idx6 = idx5 + opnd_array(5)->num_edges(); 	// tmp2
  unsigned idx7 = idx6 + opnd_array(6)->num_edges(); 	// tmp3
  unsigned idx8 = idx7 + opnd_array(7)->num_edges(); 	// tmp4
  {
    C2_MacroAssembler _masm(&cbuf);

#line 10266 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ string_indexof_char(opnd_array(1)->as_Register(ra_,this,idx1)/* str1 */, opnd_array(2)->as_Register(ra_,this,idx2)/* cnt1 */, opnd_array(3)->as_Register(ra_,this,idx3)/* ch */,
                           opnd_array(4)->as_Register(ra_,this,idx4)/* result */, opnd_array(5)->as_Register(ra_,this,idx5)/* tmp1 */, opnd_array(6)->as_Register(ra_,this,idx6)/* tmp2 */,
                           opnd_array(7)->as_Register(ra_,this,idx7)/* tmp3 */, opnd_array(8)->as_Register(ra_,this,idx8)/* tmp4 */, false /* isU */);
  
#line 15695 "ad_riscv.cpp"
  }
}

void stringL_indexof_charNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// str1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// cnt1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// ch
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// result
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// tmp1
  unsigned idx6 = idx5 + opnd_array(5)->num_edges(); 	// tmp2
  unsigned idx7 = idx6 + opnd_array(6)->num_edges(); 	// tmp3
  unsigned idx8 = idx7 + opnd_array(7)->num_edges(); 	// tmp4
  {
    C2_MacroAssembler _masm(&cbuf);

#line 10285 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ string_indexof_char(opnd_array(1)->as_Register(ra_,this,idx1)/* str1 */, opnd_array(2)->as_Register(ra_,this,idx2)/* cnt1 */, opnd_array(3)->as_Register(ra_,this,idx3)/* ch */,
                           opnd_array(4)->as_Register(ra_,this,idx4)/* result */, opnd_array(5)->as_Register(ra_,this,idx5)/* tmp1 */, opnd_array(6)->as_Register(ra_,this,idx6)/* tmp2 */,
                           opnd_array(7)->as_Register(ra_,this,idx7)/* tmp3 */, opnd_array(8)->as_Register(ra_,this,idx8)/* tmp4 */, true /* isL */);
  
#line 15720 "ad_riscv.cpp"
  }
}

void clearArray_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// cnt
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// base
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// tmp1
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// tmp2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 10305 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    address tpc = __ zero_words(opnd_array(2)->as_Register(ra_,this,idx2)/* base */, opnd_array(1)->as_Register(ra_,this,idx1)/* cnt */);
    if (tpc == NULL) {
      ciEnv::current()->record_failure("CodeCache is full");
      return;
    }
  
#line 15743 "ad_riscv.cpp"
  }
}

void clearArray_imm_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// cnt
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// base
  {
    C2_MacroAssembler _masm(&cbuf);

#line 10326 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ zero_words(opnd_array(2)->as_Register(ra_,this,idx2)/* base */, (uint64_t)opnd_array(1)->constantL());
  
#line 15760 "ad_riscv.cpp"
  }
}

void string_equalsLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// str1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// str2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// cnt
  {
    C2_MacroAssembler _masm(&cbuf);

#line 10341 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    // Count is in 8-bit bytes; non-Compact chars are 16 bits.
    __ string_equals(opnd_array(1)->as_Register(ra_,this,idx1)/* str1 */, opnd_array(2)->as_Register(ra_,this,idx2)/* str2 */,
                     opnd_array(0)->as_Register(ra_,this)/* result */, opnd_array(3)->as_Register(ra_,this,idx3)/* cnt */, 1);
  
#line 15780 "ad_riscv.cpp"
  }
}

void string_equalsUNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// str1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// str2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// cnt
  {
    C2_MacroAssembler _masm(&cbuf);

#line 10357 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    // Count is in 8-bit bytes; non-Compact chars are 16 bits.
    __ string_equals(opnd_array(1)->as_Register(ra_,this,idx1)/* str1 */, opnd_array(2)->as_Register(ra_,this,idx2)/* str2 */,
                     opnd_array(0)->as_Register(ra_,this)/* result */, opnd_array(3)->as_Register(ra_,this,idx3)/* cnt */, 2);
  
#line 15800 "ad_riscv.cpp"
  }
}

void array_equalsBNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// ary1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// ary2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// tmp1
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// tmp2
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// tmp3
  unsigned idx6 = idx5 + opnd_array(5)->num_edges(); 	// tmp4
  {
    C2_MacroAssembler _masm(&cbuf);

#line 10374 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ arrays_equals(opnd_array(1)->as_Register(ra_,this,idx1)/* ary1 */, opnd_array(2)->as_Register(ra_,this,idx2)/* ary2 */,
                     opnd_array(3)->as_Register(ra_,this,idx3)/* tmp1 */, opnd_array(4)->as_Register(ra_,this,idx4)/* tmp2 */, opnd_array(5)->as_Register(ra_,this,idx5)/* tmp3 */, opnd_array(6)->as_Register(ra_,this,idx6)/* tmp4 */,
                     opnd_array(0)->as_Register(ra_,this)/* result */, as_Register(R28_enc), 1);
  
#line 15823 "ad_riscv.cpp"
  }
}

void array_equalsCNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// ary1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// ary2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// tmp1
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// tmp2
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// tmp3
  unsigned idx6 = idx5 + opnd_array(5)->num_edges(); 	// tmp4
  {
    C2_MacroAssembler _masm(&cbuf);

#line 10391 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ arrays_equals(opnd_array(1)->as_Register(ra_,this,idx1)/* ary1 */, opnd_array(2)->as_Register(ra_,this,idx2)/* ary2 */,
                     opnd_array(3)->as_Register(ra_,this,idx3)/* tmp1 */, opnd_array(4)->as_Register(ra_,this,idx4)/* tmp2 */, opnd_array(5)->as_Register(ra_,this,idx5)/* tmp3 */, opnd_array(6)->as_Register(ra_,this,idx6)/* tmp4 */,
                     opnd_array(0)->as_Register(ra_,this)/* result */, as_Register(R28_enc), 2);
  
#line 15846 "ad_riscv.cpp"
  }
}

void safePointNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 5;
  unsigned idx1 = 5; 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 10410 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    __ read_polling_page(as_Register(opnd_array(1)->reg(ra_,this,idx1)/* poll */), 0, relocInfo::poll_type);
  
#line 15862 "ad_riscv.cpp"
  }
}

void tlsLoadPNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// 
  // User did not define which encode class to use.
}

uint tlsLoadPNode::size(PhaseRegAlloc *ra_) const {
  assert(VerifyOops || MachNode::size(ra_) <= 0, "bad fixed size");
  return (VerifyOops ? MachNode::size(ra_) : 0);
}

void cmpFastLockNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// object
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// box
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// tmp1
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// tmp2
  {

#line 2376 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    Register flag = t1;
    Register oop = as_Register(opnd_array(1)->reg(ra_,this,idx1)/* object */);
    Register box = as_Register(opnd_array(2)->reg(ra_,this,idx2)/* box */);
    Register disp_hdr = as_Register(opnd_array(3)->reg(ra_,this,idx3)/* tmp1 */);
    Register tmp = as_Register(opnd_array(4)->reg(ra_,this,idx4)/* tmp2 */);
    Label cont;
    Label object_has_monitor;
    Label no_count;

    assert_different_registers(oop, box, tmp, disp_hdr, t0);

    // Load markWord from object into displaced_header.
    __ ld(disp_hdr, Address(oop, oopDesc::mark_offset_in_bytes()));

    if (DiagnoseSyncOnValueBasedClasses != 0) {
      __ load_klass(flag, oop);
      __ lwu(flag, Address(flag, Klass::access_flags_offset()));
      __ andi(flag, flag, JVM_ACC_IS_VALUE_BASED_CLASS, tmp /* tmp */);
      __ bnez(flag, cont, true /* is_far */);
    }

    // Check for existing monitor
    __ andi(t0, disp_hdr, markWord::monitor_value);
    __ bnez(t0, object_has_monitor);

    if (!UseHeavyMonitors) {
      // Set tmp to be (markWord of object | UNLOCK_VALUE).
      __ ori(tmp, disp_hdr, markWord::unlocked_value);

      // Initialize the box. (Must happen before we update the object mark!)
      __ sd(tmp, Address(box, BasicLock::displaced_header_offset_in_bytes()));

      // Compare object markWord with an unlocked value (tmp) and if
      // equal exchange the stack address of our box with object markWord.
      // On failure disp_hdr contains the possibly locked markWord.
      __ cmpxchg(/*memory address*/oop, /*expected value*/tmp, /*new value*/box, Assembler::int64, Assembler::aq,
                 Assembler::rl, /*result*/disp_hdr);
      __ mv(flag, zr);
      __ beq(disp_hdr, tmp, cont); // prepare zero flag and goto cont if we won the cas

      assert(oopDesc::mark_offset_in_bytes() == 0, "offset of _mark is not 0");

      // If the compare-and-exchange succeeded, then we found an unlocked
      // object, will have now locked it will continue at label cont
      // We did not see an unlocked object so try the fast recursive case.

      // Check if the owner is self by comparing the value in the
      // markWord of object (disp_hdr) with the stack pointer.
      __ sub(disp_hdr, disp_hdr, sp);
      __ mv(tmp, (intptr_t) (~(os::vm_page_size()-1) | (uintptr_t)markWord::lock_mask_in_place));
      // If (mark & lock_mask) == 0 and mark - sp < page_size, we are stack-locking and goto cont,
      // hence we can store 0 as the displaced header in the box, which indicates that it is a
      // recursive lock.
      __ andr(tmp/*==0?*/, disp_hdr, tmp);
      __ sd(tmp/*==0, perhaps*/, Address(box, BasicLock::displaced_header_offset_in_bytes()));
      __ mv(flag, tmp); // we can use the value of tmp as the result here
    } else {
      __ mv(flag, 1); // Set non-zero flag to indicate 'failure' -> take slow-path
    }

    __ j(cont);

    // Handle existing monitor.
    __ bind(object_has_monitor);
    // The object's monitor m is unlocked iff m->owner == NULL,
    // otherwise m->owner may contain a thread or a stack address.
    //
    // Try to CAS m->owner from NULL to current thread.
    __ add(tmp, disp_hdr, (ObjectMonitor::owner_offset_in_bytes() - markWord::monitor_value));
    __ cmpxchg(/*memory address*/tmp, /*expected value*/zr, /*new value*/xthread, Assembler::int64, Assembler::aq,
             Assembler::rl, /*result*/flag); // cas succeeds if flag == zr(expected)

    // Store a non-null value into the box to avoid looking like a re-entrant
    // lock. The fast-path monitor unlock code checks for
    // markWord::monitor_value so use markWord::unused_mark which has the
    // relevant bit set, and also matches ObjectSynchronizer::slow_enter.
    __ mv(tmp, (address)markWord::unused_mark().value());
    __ sd(tmp, Address(box, BasicLock::displaced_header_offset_in_bytes()));

    __ beqz(flag, cont); // CAS success means locking succeeded

    __ bne(flag, xthread, cont); // Check for recursive locking

    // Recursive lock case
    __ mv(flag, zr);
    __ increment(Address(disp_hdr, ObjectMonitor::recursions_offset_in_bytes() - markWord::monitor_value), 1, t0, tmp);

    __ bind(cont);

    __ bnez(flag, no_count);

    __ increment(Address(xthread, JavaThread::held_monitor_count_offset()), 1, t0, tmp);

    __ bind(no_count);
  
#line 15987 "ad_riscv.cpp"
  }
}

void cmpFastUnlockNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// object
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// box
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// tmp1
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// tmp2
  {

#line 2475 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    Register flag = t1;
    Register oop = as_Register(opnd_array(1)->reg(ra_,this,idx1)/* object */);
    Register box = as_Register(opnd_array(2)->reg(ra_,this,idx2)/* box */);
    Register disp_hdr = as_Register(opnd_array(3)->reg(ra_,this,idx3)/* tmp1 */);
    Register tmp = as_Register(opnd_array(4)->reg(ra_,this,idx4)/* tmp2 */);
    Label cont;
    Label object_has_monitor;
    Label no_count;

    assert_different_registers(oop, box, tmp, disp_hdr, flag);

    if (!UseHeavyMonitors) {
      // Find the lock address and load the displaced header from the stack.
      __ ld(disp_hdr, Address(box, BasicLock::displaced_header_offset_in_bytes()));

      // If the displaced header is 0, we have a recursive unlock.
      __ mv(flag, disp_hdr);
      __ beqz(disp_hdr, cont);
    }

    // Handle existing monitor.
    __ ld(tmp, Address(oop, oopDesc::mark_offset_in_bytes()));
    __ andi(t0, tmp, markWord::monitor_value);
    __ bnez(t0, object_has_monitor);

    if (!UseHeavyMonitors) {
      // Check if it is still a light weight lock, this is true if we
      // see the stack address of the basicLock in the markWord of the
      // object.

      __ cmpxchg(/*memory address*/oop, /*expected value*/box, /*new value*/disp_hdr, Assembler::int64, Assembler::relaxed,
                 Assembler::rl, /*result*/tmp);
      __ xorr(flag, box, tmp); // box == tmp if cas succeeds
    } else {
      __ mv(flag, 1); // Set non-zero flag to indicate 'failure' -> take slow path
    }
    __ j(cont);

    assert(oopDesc::mark_offset_in_bytes() == 0, "offset of _mark is not 0");

    // Handle existing monitor.
    __ bind(object_has_monitor);
    STATIC_ASSERT(markWord::monitor_value <= INT_MAX);
    __ add(tmp, tmp, -(int)markWord::monitor_value); // monitor
    __ ld(disp_hdr, Address(tmp, ObjectMonitor::recursions_offset_in_bytes()));

    Label notRecursive;
    __ beqz(disp_hdr, notRecursive); // Will be 0 if not recursive.

    // Recursive lock
    __ addi(disp_hdr, disp_hdr, -1);
    __ sd(disp_hdr, Address(tmp, ObjectMonitor::recursions_offset_in_bytes()));
    __ mv(flag, zr);
    __ j(cont);

    __ bind(notRecursive);
    __ ld(flag, Address(tmp, ObjectMonitor::EntryList_offset_in_bytes()));
    __ ld(disp_hdr, Address(tmp, ObjectMonitor::cxq_offset_in_bytes()));
    __ orr(flag, flag, disp_hdr); // Will be 0 if both are 0.
    __ bnez(flag, cont);
    // need a release store here
    __ la(tmp, Address(tmp, ObjectMonitor::owner_offset_in_bytes()));
    __ membar(MacroAssembler::LoadStore | MacroAssembler::StoreStore);
    __ sd(zr, Address(tmp)); // set unowned

    __ bind(cont);

    __ bnez(flag, no_count);

    __ decrement(Address(xthread, JavaThread::held_monitor_count_offset()), 1, t0, tmp);

    __ bind(no_count);
  
#line 16077 "ad_riscv.cpp"
  }
}

void TailCalljmpIndNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 5;
  unsigned idx1 = 5; 	// method_oop
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// 
  {

#line 2585 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    Register target_reg = as_Register(opnd_array(1)->reg(ra_,this,idx1)/* jump_target */);
    __ jr(target_reg);
  
#line 16095 "ad_riscv.cpp"
  }
}

void TailjmpIndNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 5;
  unsigned idx1 = 5; 	// ex_oop
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// 
  {

#line 2591 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    Register target_reg = as_Register(opnd_array(1)->reg(ra_,this,idx1)/* jump_target */);
    // exception oop should be in x10
    // ret addr has been popped into ra
    // callee expects it in x13
    __ mv(x13, ra);
    __ jr(target_reg);
  
#line 16117 "ad_riscv.cpp"
  }
}

void CreateExceptionNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// 
  // User did not define which encode class to use.
}

uint CreateExceptionNode::size(PhaseRegAlloc *ra_) const {
  assert(VerifyOops || MachNode::size(ra_) <= 0, "bad fixed size");
  return (VerifyOops ? MachNode::size(ra_) : 0);
}

void RethrowExceptionNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 5;
  unsigned idx1 = 5; 	// 
  {

#line 2601 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    __ far_jump(RuntimeAddress(OptoRuntime::rethrow_stub()));
  
#line 16146 "ad_riscv.cpp"
  }
}

void RetNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 5;
  unsigned idx1 = 5; 	// 
  {

#line 2606 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    C2_MacroAssembler _masm(&cbuf);
    __ ret();
  
#line 16162 "ad_riscv.cpp"
  }
}

void ShouldNotReachHereNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 5;
  unsigned idx1 = 5; 	// 
  {
    C2_MacroAssembler _masm(&cbuf);

#line 10548 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    if (is_reachable()) {
      __ stop(_halt_reason);
    }
  
#line 16180 "ad_riscv.cpp"
  }
}

void loadVNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  {
    C2_MacroAssembler _masm(&cbuf);

#line 106 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    VectorRegister dst_reg = as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */);
    loadStore(C2_MacroAssembler(&cbuf), false, dst_reg,
              Matcher::vector_element_basic_type(this), as_Register(opnd_array(1)->base(ra_,this,idx1)));
  
#line 16198 "ad_riscv.cpp"
  }
}

void storeVNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 118 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    VectorRegister src_reg = as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src */);
    loadStore(C2_MacroAssembler(&cbuf), true, src_reg,
              Matcher::vector_element_basic_type(this, opnd_array(2)), as_Register(opnd_array(1)->base(ra_,this,idx1)));
  
#line 16217 "ad_riscv.cpp"
  }
}

void vabsBNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 134 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e8);
    __ vrsub_vi(as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* tmp */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */), 0);
    __ vmax_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* tmp */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 16236 "ad_riscv.cpp"
  }
}

void vabsSNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 148 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e16);
    __ vrsub_vi(as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* tmp */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */), 0);
    __ vmax_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* tmp */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 16255 "ad_riscv.cpp"
  }
}

void vabsINode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 162 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e32);
    __ vrsub_vi(as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* tmp */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */), 0);
    __ vmax_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* tmp */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 16274 "ad_riscv.cpp"
  }
}

void vabsLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 176 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e64);
    __ vrsub_vi(as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* tmp */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */), 0);
    __ vmax_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* tmp */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 16293 "ad_riscv.cpp"
  }
}

void vabsFNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 188 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e32);
    __ vfsgnjx_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 16310 "ad_riscv.cpp"
  }
}

void vabsDNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 199 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e64);
    __ vfsgnjx_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 16327 "ad_riscv.cpp"
  }
}

void vaddBNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 212 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e8);
    __ vadd_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */),
               as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
               as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 16347 "ad_riscv.cpp"
  }
}

void vaddSNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 225 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e16);
    __ vadd_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */),
               as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
               as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 16367 "ad_riscv.cpp"
  }
}

void vaddINode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 238 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    BasicType bt = Matcher::vector_element_basic_type(this);
    Assembler::SEW sew = Assembler::elemtype_to_sew(bt);
    __ vsetvli(t0, x0, sew);
    __ vadd_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */),
               as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
               as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 16389 "ad_riscv.cpp"
  }
}

void vaddI_maskedNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// dst_src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// mask
  {
    C2_MacroAssembler _masm(&cbuf);

#line 253 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    BasicType bt = Matcher::vector_element_basic_type(this);
    Assembler::SEW sew = Assembler::elemtype_to_sew(bt);
    __ vsetvli(t0, x0, sew);
    __ vadd_vv(as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* dst_src1 */),
               as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* dst_src1 */),
               as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */),
               Assembler::v0_t);
  
#line 16413 "ad_riscv.cpp"
  }
}

void vaddLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 269 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e64);
    __ vadd_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */),
               as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
               as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 16433 "ad_riscv.cpp"
  }
}

void vaddFNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 282 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e32);
    __ vfadd_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */),
                as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
                as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 16453 "ad_riscv.cpp"
  }
}

void vaddDNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 295 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e64);
    __ vfadd_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */),
                as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
                as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 16473 "ad_riscv.cpp"
  }
}

void vandNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 310 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e64);
    __ vand_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */),
               as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
               as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 16493 "ad_riscv.cpp"
  }
}

void vorNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 325 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e64);
    __ vor_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */),
              as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
              as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 16513 "ad_riscv.cpp"
  }
}

void vxorNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 340 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e64);
    __ vxor_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */),
               as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
               as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 16533 "ad_riscv.cpp"
  }
}

void vdivFNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 355 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e32);
    __ vfdiv_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */),
                as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
                as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 16553 "ad_riscv.cpp"
  }
}

void vdivDNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 368 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e64);
    __ vfdiv_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */),
                as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
                as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 16573 "ad_riscv.cpp"
  }
}

void vmaxNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 385 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    BasicType bt = Matcher::vector_element_basic_type(this);
    Assembler::SEW sew = Assembler::elemtype_to_sew(bt);
    __ vsetvli(t0, x0, sew);
    __ vmax_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */),
               as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */), as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 16594 "ad_riscv.cpp"
  }
}

void vminNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 401 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    BasicType bt = Matcher::vector_element_basic_type(this);
    Assembler::SEW sew = Assembler::elemtype_to_sew(bt);
    __ vsetvli(t0, x0, sew);
    __ vmin_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */),
               as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */), as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 16615 "ad_riscv.cpp"
  }
}

void vmaxFNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// dst
  {
    C2_MacroAssembler _masm(&cbuf);

#line 419 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ minmax_FD_v(as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* dst */),
                   as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */), as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */),
                   false /* is_double */, false /* is_min */);
  
#line 16635 "ad_riscv.cpp"
  }
}

void vmaxDNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// dst
  {
    C2_MacroAssembler _masm(&cbuf);

#line 433 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ minmax_FD_v(as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* dst */),
                   as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */), as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */),
                   true /* is_double */, false /* is_min */);
  
#line 16655 "ad_riscv.cpp"
  }
}

void vminFNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// dst
  {
    C2_MacroAssembler _masm(&cbuf);

#line 447 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ minmax_FD_v(as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* dst */),
                   as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */), as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */),
                   false /* is_double */, true /* is_min */);
  
#line 16675 "ad_riscv.cpp"
  }
}

void vminDNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// dst
  {
    C2_MacroAssembler _masm(&cbuf);

#line 461 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ minmax_FD_v(as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* dst */),
                   as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */), as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */),
                   true /* is_double */, true /* is_min */);
  
#line 16695 "ad_riscv.cpp"
  }
}

void vfmlaFNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// dst_src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 477 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e32);
    __ vfmacc_vv(as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* dst_src1 */),
                 as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */), as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* src3 */));
  
#line 16715 "ad_riscv.cpp"
  }
}

void vfmlaDNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// dst_src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 491 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e64);
    __ vfmacc_vv(as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* dst_src1 */),
                 as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */), as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* src3 */));
  
#line 16735 "ad_riscv.cpp"
  }
}

void vfmlsFNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// dst_src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 509 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e32);
    __ vfnmsac_vv(as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* dst_src1 */),
                  as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */), as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* src3 */));
  
#line 16755 "ad_riscv.cpp"
  }
}

void vfmlsF_0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// dst_src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 509 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e32);
    __ vfnmsac_vv(as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* dst_src1 */),
                  as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */), as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* src3 */));
  
#line 16775 "ad_riscv.cpp"
  }
}

void vfmlsDNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// dst_src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 525 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e64);
    __ vfnmsac_vv(as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* dst_src1 */),
                  as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */), as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* src3 */));
  
#line 16795 "ad_riscv.cpp"
  }
}

void vfmlsD_0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// dst_src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 525 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e64);
    __ vfnmsac_vv(as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* dst_src1 */),
                  as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */), as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* src3 */));
  
#line 16815 "ad_riscv.cpp"
  }
}

void vfnmlaFNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// dst_src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 543 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e32);
    __ vfnmacc_vv(as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* dst_src1 */),
                  as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */), as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* src3 */));
  
#line 16835 "ad_riscv.cpp"
  }
}

void vfnmlaF_0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// dst_src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 543 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e32);
    __ vfnmacc_vv(as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* dst_src1 */),
                  as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */), as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* src3 */));
  
#line 16855 "ad_riscv.cpp"
  }
}

void vfnmlaDNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// dst_src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 559 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e64);
    __ vfnmacc_vv(as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* dst_src1 */),
                  as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */), as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* src3 */));
  
#line 16875 "ad_riscv.cpp"
  }
}

void vfnmlaD_0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// dst_src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 559 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e64);
    __ vfnmacc_vv(as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* dst_src1 */),
                  as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */), as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* src3 */));
  
#line 16895 "ad_riscv.cpp"
  }
}

void vfnmlsFNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// dst_src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 575 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e32);
    __ vfmsac_vv(as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* dst_src1 */),
                 as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */), as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* src3 */));
  
#line 16915 "ad_riscv.cpp"
  }
}

void vfnmlsDNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// dst_src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 589 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e64);
    __ vfmsac_vv(as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* dst_src1 */),
                 as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */), as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* src3 */));
  
#line 16935 "ad_riscv.cpp"
  }
}

void vmlaBNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// dst_src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 604 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e8);
    __ vmacc_vv(as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* dst_src1 */),
                as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */), as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* src3 */));
  
#line 16955 "ad_riscv.cpp"
  }
}

void vmlaB_0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src2
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src3
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// dst_src1
  {
    C2_MacroAssembler _masm(&cbuf);

#line 604 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e8);
    __ vmacc_vv(as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* dst_src1 */),
                as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src2 */), as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src3 */));
  
#line 16975 "ad_riscv.cpp"
  }
}

void vmlaSNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// dst_src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 617 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e16);
    __ vmacc_vv(as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* dst_src1 */),
                as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */), as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* src3 */));
  
#line 16995 "ad_riscv.cpp"
  }
}

void vmlaS_0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src2
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src3
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// dst_src1
  {
    C2_MacroAssembler _masm(&cbuf);

#line 617 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e16);
    __ vmacc_vv(as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* dst_src1 */),
                as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src2 */), as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src3 */));
  
#line 17015 "ad_riscv.cpp"
  }
}

void vmlaINode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// dst_src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 630 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e32);
    __ vmacc_vv(as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* dst_src1 */),
                as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */), as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* src3 */));
  
#line 17035 "ad_riscv.cpp"
  }
}

void vmlaI_0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src2
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src3
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// dst_src1
  {
    C2_MacroAssembler _masm(&cbuf);

#line 630 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e32);
    __ vmacc_vv(as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* dst_src1 */),
                as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src2 */), as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src3 */));
  
#line 17055 "ad_riscv.cpp"
  }
}

void vmlaLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// dst_src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 643 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e64);
    __ vmacc_vv(as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* dst_src1 */),
                as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */), as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* src3 */));
  
#line 17075 "ad_riscv.cpp"
  }
}

void vmlaL_0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src2
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src3
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// dst_src1
  {
    C2_MacroAssembler _masm(&cbuf);

#line 643 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e64);
    __ vmacc_vv(as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* dst_src1 */),
                as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src2 */), as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src3 */));
  
#line 17095 "ad_riscv.cpp"
  }
}

void vmlsBNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// dst_src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 658 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e8);
    __ vnmsac_vv(as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* dst_src1 */),
                 as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */), as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* src3 */));
  
#line 17115 "ad_riscv.cpp"
  }
}

void vmlsSNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// dst_src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 671 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e16);
    __ vnmsac_vv(as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* dst_src1 */),
                 as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */), as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* src3 */));
  
#line 17135 "ad_riscv.cpp"
  }
}

void vmlsINode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// dst_src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 684 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e32);
    __ vnmsac_vv(as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* dst_src1 */),
                 as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */), as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* src3 */));
  
#line 17155 "ad_riscv.cpp"
  }
}

void vmlsLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// dst_src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 697 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e64);
    __ vnmsac_vv(as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* dst_src1 */),
                 as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */), as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* src3 */));
  
#line 17175 "ad_riscv.cpp"
  }
}

void vmulBNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 711 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e8);
    __ vmul_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
               as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 17194 "ad_riscv.cpp"
  }
}

void vmulSNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 723 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e16);
    __ vmul_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
               as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 17213 "ad_riscv.cpp"
  }
}

void vmulINode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 735 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e32);
    __ vmul_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
               as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 17232 "ad_riscv.cpp"
  }
}

void vmulLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 747 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e64);
    __ vmul_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
               as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 17251 "ad_riscv.cpp"
  }
}

void vmulFNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 759 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e32);
    __ vfmul_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
                as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 17270 "ad_riscv.cpp"
  }
}

void vmulDNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 771 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e64);
    __ vfmul_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
                as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 17289 "ad_riscv.cpp"
  }
}

void vnegINode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 785 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e32);
    __ vneg_v(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 17306 "ad_riscv.cpp"
  }
}

void vnegLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 796 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e64);
    __ vneg_v(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 17323 "ad_riscv.cpp"
  }
}

void vnegFNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 809 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e32);
    __ vfneg_v(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 17340 "ad_riscv.cpp"
  }
}

void vnegDNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 820 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e64);
    __ vfneg_v(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 17357 "ad_riscv.cpp"
  }
}

void reduce_andINode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 839 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    BasicType bt = Matcher::vector_element_basic_type(this, opnd_array(2));
    __ rvv_reduce_integral(opnd_array(0)->as_Register(ra_,this)/* dst */, as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* tmp */),
                           opnd_array(1)->as_Register(ra_,this,idx1)/* src1 */, as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */), bt, this->ideal_Opcode());
  
#line 17377 "ad_riscv.cpp"
  }
}

void reduce_andLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 855 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    BasicType bt = Matcher::vector_element_basic_type(this, opnd_array(2));
    __ rvv_reduce_integral(opnd_array(0)->as_Register(ra_,this)/* dst */, as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* tmp */),
                           opnd_array(1)->as_Register(ra_,this,idx1)/* src1 */, as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */), bt, this->ideal_Opcode());
  
#line 17397 "ad_riscv.cpp"
  }
}

void reduce_orINode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 875 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    BasicType bt = Matcher::vector_element_basic_type(this, opnd_array(2));
    __ rvv_reduce_integral(opnd_array(0)->as_Register(ra_,this)/* dst */, as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* tmp */),
                           opnd_array(1)->as_Register(ra_,this,idx1)/* src1 */, as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */), bt, this->ideal_Opcode());
  
#line 17417 "ad_riscv.cpp"
  }
}

void reduce_orLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 891 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    BasicType bt = Matcher::vector_element_basic_type(this, opnd_array(2));
    __ rvv_reduce_integral(opnd_array(0)->as_Register(ra_,this)/* dst */, as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* tmp */),
                           opnd_array(1)->as_Register(ra_,this,idx1)/* src1 */, as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */), bt, this->ideal_Opcode());
  
#line 17437 "ad_riscv.cpp"
  }
}

void reduce_xorINode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 911 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    BasicType bt = Matcher::vector_element_basic_type(this, opnd_array(2));
    __ rvv_reduce_integral(opnd_array(0)->as_Register(ra_,this)/* dst */, as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* tmp */),
                           opnd_array(1)->as_Register(ra_,this,idx1)/* src1 */, as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */), bt, this->ideal_Opcode());
  
#line 17457 "ad_riscv.cpp"
  }
}

void reduce_xorLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 927 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    BasicType bt = Matcher::vector_element_basic_type(this, opnd_array(2));
    __ rvv_reduce_integral(opnd_array(0)->as_Register(ra_,this)/* dst */, as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* tmp */),
                           opnd_array(1)->as_Register(ra_,this,idx1)/* src1 */, as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */), bt, this->ideal_Opcode());
  
#line 17477 "ad_riscv.cpp"
  }
}

void reduce_addINode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 947 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    BasicType bt = Matcher::vector_element_basic_type(this, opnd_array(2));
    __ rvv_reduce_integral(opnd_array(0)->as_Register(ra_,this)/* dst */, as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* tmp */),
                           opnd_array(1)->as_Register(ra_,this,idx1)/* src1 */, as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */), bt, this->ideal_Opcode());
  
#line 17497 "ad_riscv.cpp"
  }
}

void reduce_addLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 963 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    BasicType bt = Matcher::vector_element_basic_type(this, opnd_array(2));
    __ rvv_reduce_integral(opnd_array(0)->as_Register(ra_,this)/* dst */, as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* tmp */),
                           opnd_array(1)->as_Register(ra_,this,idx1)/* src1 */, as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */), bt, this->ideal_Opcode());
  
#line 17517 "ad_riscv.cpp"
  }
}

void reduce_addFNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1_dst
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 978 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e32);
    __ vfmv_s_f(as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* tmp */), opnd_array(1)->as_FloatRegister(ra_,this,idx1)/* src1_dst */);
    __ vfredosum_vs(as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* tmp */), as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */),
                    as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* tmp */));
    __ vfmv_f_s(opnd_array(1)->as_FloatRegister(ra_,this,idx1)/* src1_dst */, as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* tmp */));
  
#line 17539 "ad_riscv.cpp"
  }
}

void reduce_addDNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1_dst
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 995 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e64);
    __ vfmv_s_f(as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* tmp */), opnd_array(1)->as_FloatRegister(ra_,this,idx1)/* src1_dst */);
    __ vfredosum_vs(as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* tmp */), as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */),
                    as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* tmp */));
    __ vfmv_f_s(opnd_array(1)->as_FloatRegister(ra_,this,idx1)/* src1_dst */, as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* tmp */));
  
#line 17561 "ad_riscv.cpp"
  }
}

void vreduce_maxINode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1015 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    BasicType bt = Matcher::vector_element_basic_type(this, opnd_array(2));
    __ rvv_reduce_integral(opnd_array(0)->as_Register(ra_,this)/* dst */, as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* tmp */),
                           opnd_array(1)->as_Register(ra_,this,idx1)/* src1 */, as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */), bt, this->ideal_Opcode());
  
#line 17581 "ad_riscv.cpp"
  }
}

void vreduce_maxLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1029 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    BasicType bt = Matcher::vector_element_basic_type(this, opnd_array(2));
    __ rvv_reduce_integral(opnd_array(0)->as_Register(ra_,this)/* dst */, as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* tmp */),
                           opnd_array(1)->as_Register(ra_,this,idx1)/* src1 */, as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */), bt, this->ideal_Opcode());
  
#line 17601 "ad_riscv.cpp"
  }
}

void vreduce_minINode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1047 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    BasicType bt = Matcher::vector_element_basic_type(this, opnd_array(2));
    __ rvv_reduce_integral(opnd_array(0)->as_Register(ra_,this)/* dst */, as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* tmp */),
                           opnd_array(1)->as_Register(ra_,this,idx1)/* src1 */, as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */), bt, this->ideal_Opcode());
  
#line 17621 "ad_riscv.cpp"
  }
}

void vreduce_minLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1061 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    BasicType bt = Matcher::vector_element_basic_type(this, opnd_array(2));
    __ rvv_reduce_integral(opnd_array(0)->as_Register(ra_,this)/* dst */, as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* tmp */),
                           opnd_array(1)->as_Register(ra_,this,idx1)/* src1 */, as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */), bt, this->ideal_Opcode());
  
#line 17641 "ad_riscv.cpp"
  }
}

void vreduce_maxFNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// dst
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// tmp1
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// tmp2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1077 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ reduce_minmax_FD_v(opnd_array(3)->as_FloatRegister(ra_,this,idx3)/* dst */,
                          opnd_array(1)->as_FloatRegister(ra_,this,idx1)/* src1 */, as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */),
                          as_VectorRegister(opnd_array(4)->reg(ra_,this,idx4)/* tmp1 */), as_VectorRegister(opnd_array(5)->reg(ra_,this,idx5)/* tmp2 */),
                          false /* is_double */, false /* is_min */);
  
#line 17664 "ad_riscv.cpp"
  }
}

void vreduce_maxDNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// dst
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// tmp1
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// tmp2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1092 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ reduce_minmax_FD_v(opnd_array(3)->as_FloatRegister(ra_,this,idx3)/* dst */,
                          opnd_array(1)->as_FloatRegister(ra_,this,idx1)/* src1 */, as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */),
                          as_VectorRegister(opnd_array(4)->reg(ra_,this,idx4)/* tmp1 */), as_VectorRegister(opnd_array(5)->reg(ra_,this,idx5)/* tmp2 */),
                          true /* is_double */, false /* is_min */);
  
#line 17687 "ad_riscv.cpp"
  }
}

void vreduce_minFNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// dst
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// tmp1
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// tmp2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1109 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ reduce_minmax_FD_v(opnd_array(3)->as_FloatRegister(ra_,this,idx3)/* dst */,
                          opnd_array(1)->as_FloatRegister(ra_,this,idx1)/* src1 */, as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */),
                          as_VectorRegister(opnd_array(4)->reg(ra_,this,idx4)/* tmp1 */), as_VectorRegister(opnd_array(5)->reg(ra_,this,idx5)/* tmp2 */),
                          false /* is_double */, true /* is_min */);
  
#line 17710 "ad_riscv.cpp"
  }
}

void vreduce_minDNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// dst
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// tmp1
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// tmp2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1124 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ reduce_minmax_FD_v(opnd_array(3)->as_FloatRegister(ra_,this,idx3)/* dst */,
                          opnd_array(1)->as_FloatRegister(ra_,this,idx1)/* src1 */, as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */),
                          as_VectorRegister(opnd_array(4)->reg(ra_,this,idx4)/* tmp1 */), as_VectorRegister(opnd_array(5)->reg(ra_,this,idx5)/* tmp2 */),
                          true /* is_double */, true /* is_min */);
  
#line 17733 "ad_riscv.cpp"
  }
}

void vroundDNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// rmode
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1139 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    switch (opnd_array(2)->constant()) {
      case RoundDoubleModeNode::rmode_rint:
        __ csrwi(CSR_FRM, C2_MacroAssembler::rne);
        __ vfcvt_rtz_x_f_v(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
        break;
      case RoundDoubleModeNode::rmode_floor:
        __ csrwi(CSR_FRM, C2_MacroAssembler::rdn);
        __ vfcvt_rtz_x_f_v(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
        break;
      case RoundDoubleModeNode::rmode_ceil:
        __ csrwi(CSR_FRM, C2_MacroAssembler::rup);
        __ vfcvt_rtz_x_f_v(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
        break;
      default:
        ShouldNotReachHere();
        break;
    }
  
#line 17766 "ad_riscv.cpp"
  }
}

void replicateBNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1167 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e8);
    __ vmv_v_x(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 17783 "ad_riscv.cpp"
  }
}

void replicateSNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1178 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e16);
    __ vmv_v_x(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 17800 "ad_riscv.cpp"
  }
}

void replicateINode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1189 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e32);
    __ vmv_v_x(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 17817 "ad_riscv.cpp"
  }
}

void replicateLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1200 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e64);
    __ vmv_v_x(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 17834 "ad_riscv.cpp"
  }
}

void replicateB_imm5Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// con
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1211 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e8);
    __ vmv_v_i(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), opnd_array(1)->constant());
  
#line 17851 "ad_riscv.cpp"
  }
}

void replicateS_imm5Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// con
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1222 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e16);
    __ vmv_v_i(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), opnd_array(1)->constant());
  
#line 17868 "ad_riscv.cpp"
  }
}

void replicateI_imm5Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// con
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1233 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e32);
    __ vmv_v_i(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), opnd_array(1)->constant());
  
#line 17885 "ad_riscv.cpp"
  }
}

void replicateL_imm5Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// con
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1244 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e64);
    __ vmv_v_i(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), opnd_array(1)->constantL());
  
#line 17902 "ad_riscv.cpp"
  }
}

void replicateFNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1255 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e32);
    __ vfmv_v_f(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), opnd_array(1)->as_FloatRegister(ra_,this,idx1)/* src */);
  
#line 17919 "ad_riscv.cpp"
  }
}

void replicateDNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1266 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e64);
    __ vfmv_v_f(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), opnd_array(1)->as_FloatRegister(ra_,this,idx1)/* src */);
  
#line 17936 "ad_riscv.cpp"
  }
}

void vasrBNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// shift
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// dst
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1283 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e8);
    // if shift > BitsPerByte - 1, clear the low BitsPerByte - 1 bits
    __ vmsgtu_vi(v0, as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* shift */), BitsPerByte - 1);
    __ vsra_vi(as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */),
               BitsPerByte - 1, Assembler::v0_t);
    // otherwise, shift
    __ vmnot_m(v0, v0);
    __ vsra_vv(as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */),
               as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* shift */), Assembler::v0_t);
  
#line 17962 "ad_riscv.cpp"
  }
}

void vasrSNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// shift
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// dst
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1305 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e16);
    // if shift > BitsPerShort - 1, clear the low BitsPerShort - 1 bits
    __ vmsgtu_vi(v0, as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* shift */), BitsPerShort - 1);
    __ vsra_vi(as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */),
               BitsPerShort - 1, Assembler::v0_t);
    // otherwise, shift
    __ vmnot_m(v0, v0);
    __ vsra_vv(as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */),
               as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* shift */), Assembler::v0_t);
  
#line 17988 "ad_riscv.cpp"
  }
}

void vasrINode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// shift
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1323 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e32);
    __ vsra_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */),
               as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* shift */));
  
#line 18007 "ad_riscv.cpp"
  }
}

void vasrLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// shift
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1335 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e64);
    __ vsra_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */),
         as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* shift */));
  
#line 18026 "ad_riscv.cpp"
  }
}

void vlslBNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// shift
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// dst
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1351 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e8);
    // if shift > BitsPerByte - 1, clear the element
    __ vmsgtu_vi(v0, as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* shift */), BitsPerByte - 1);
    __ vxor_vv(as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */),
               as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */), Assembler::v0_t);
    // otherwise, shift
    __ vmnot_m(v0, v0);
    __ vsll_vv(as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */),
               as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* shift */), Assembler::v0_t);
  
#line 18052 "ad_riscv.cpp"
  }
}

void vlslSNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// shift
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// dst
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1373 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e16);
    // if shift > BitsPerShort - 1, clear the element
    __ vmsgtu_vi(v0, as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* shift */), BitsPerShort - 1);
    __ vxor_vv(as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */),
               as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */), Assembler::v0_t);
    // otherwise, shift
    __ vmnot_m(v0, v0);
    __ vsll_vv(as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */),
               as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* shift */), Assembler::v0_t);
  
#line 18078 "ad_riscv.cpp"
  }
}

void vlslINode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// shift
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1391 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e32);
    __ vsll_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */),
               as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* shift */));
  
#line 18097 "ad_riscv.cpp"
  }
}

void vlslLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// shift
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1403 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e64);
    __ vsll_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */),
               as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* shift */));
  
#line 18116 "ad_riscv.cpp"
  }
}

void vlsrBNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// shift
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// dst
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1419 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e8);
    // if shift > BitsPerByte - 1, clear the element
    __ vmsgtu_vi(v0, as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* shift */), BitsPerByte - 1);
    __ vxor_vv(as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */),
               as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */), Assembler::v0_t);
    // otherwise, shift
    __ vmnot_m(v0, v0);
    __ vsrl_vv(as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */),
               as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* shift */), Assembler::v0_t);
  
#line 18142 "ad_riscv.cpp"
  }
}

void vlsrSNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// shift
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// dst
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1441 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e16);
    // if shift > BitsPerShort - 1, clear the element
    __ vmsgtu_vi(v0, as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* shift */), BitsPerShort - 1);
    __ vxor_vv(as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */),
               as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */), Assembler::v0_t);
    // otherwise, shift
    __ vmnot_m(v0, v0);
    __ vsrl_vv(as_VectorRegister(opnd_array(3)->reg(ra_,this,idx3)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */),
               as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* shift */), Assembler::v0_t);
  
#line 18168 "ad_riscv.cpp"
  }
}

void vlsrINode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// shift
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1460 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e32);
    __ vsrl_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */),
               as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* shift */));
  
#line 18187 "ad_riscv.cpp"
  }
}

void vlsrLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// shift
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1473 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e64);
    __ vsrl_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */),
               as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* shift */));
  
#line 18206 "ad_riscv.cpp"
  }
}

void vasrB_immNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// shift
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1485 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    uint32_t con = (unsigned)opnd_array(2)->constant()& 0x1f;
    __ vsetvli(t0, x0, Assembler::e8);
    if (con == 0) {
      __ vor_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */),
                as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
      return;
    }
    if (con >= BitsPerByte) con = BitsPerByte - 1;
    __ vsra_vi(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */), con);
  
#line 18231 "ad_riscv.cpp"
  }
}

void vasrS_immNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// shift
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1503 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    uint32_t con = (unsigned)opnd_array(2)->constant()& 0x1f;
    __ vsetvli(t0, x0, Assembler::e16);
    if (con == 0) {
      __ vor_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */),
                as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
      return;
    }
    if (con >= BitsPerShort) con = BitsPerShort - 1;
    __ vsra_vi(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */), con);
  
#line 18256 "ad_riscv.cpp"
  }
}

void vasrI_immNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// shift
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1521 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    uint32_t con = (unsigned)opnd_array(2)->constant()& 0x1f;
    __ vsetvli(t0, x0, Assembler::e32);
    if (con == 0) {
      __ vor_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */),
                as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
      return;
    }
    __ vsra_vi(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */), con);
  
#line 18280 "ad_riscv.cpp"
  }
}

void vasrL_immNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// shift
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1539 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    uint32_t con = (unsigned)opnd_array(2)->constant()& 0x1f;
    __ vsetvli(t0, x0, Assembler::e64);
    if (con == 0) {
      __ vor_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */),
                as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
      return;
    }
    __ vsra_vi(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */), con);
  
#line 18304 "ad_riscv.cpp"
  }
}

void vlsrB_immNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// shift
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1556 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    uint32_t con = (unsigned)opnd_array(2)->constant()& 0x1f;
    __ vsetvli(t0, x0, Assembler::e8);
    if (con == 0) {
      __ vor_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */),
                as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
      return;
    }
    if (con >= BitsPerByte) {
      __ vxor_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */),
                 as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
      return;
    }
    __ vsrl_vi(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */), con);
  
#line 18333 "ad_riscv.cpp"
  }
}

void vlsrS_immNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// shift
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1578 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    uint32_t con = (unsigned)opnd_array(2)->constant()& 0x1f;
    __ vsetvli(t0, x0, Assembler::e16);
    if (con == 0) {
      __ vor_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */),
                as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
      return;
    }
    if (con >= BitsPerShort) {
      __ vxor_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */),
                 as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
      return;
    }
    __ vsrl_vi(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */), con);
  
#line 18362 "ad_riscv.cpp"
  }
}

void vlsrI_immNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// shift
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1600 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    uint32_t con = (unsigned)opnd_array(2)->constant()& 0x1f;
    __ vsetvli(t0, x0, Assembler::e32);
    if (con == 0) {
      __ vor_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */),
                as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
      return;
    }
    __ vsrl_vi(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */), con);
  
#line 18386 "ad_riscv.cpp"
  }
}

void vlsrL_immNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// shift
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1618 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    uint32_t con = (unsigned)opnd_array(2)->constant()& 0x1f;
    __ vsetvli(t0, x0, Assembler::e64);
    if (con == 0) {
      __ vor_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */),
                as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
      return;
    }
    __ vsrl_vi(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */), con);
  
#line 18410 "ad_riscv.cpp"
  }
}

void vlslB_immNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// shift
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1635 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    uint32_t con = (unsigned)opnd_array(2)->constant()& 0x1f;
    __ vsetvli(t0, x0, Assembler::e8);
    if (con >= BitsPerByte) {
      __ vxor_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */),
                 as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
      return;
    }
    __ vsll_vi(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */), con);
  
#line 18434 "ad_riscv.cpp"
  }
}

void vlslS_immNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// shift
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1652 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    uint32_t con = (unsigned)opnd_array(2)->constant()& 0x1f;
    __ vsetvli(t0, x0, Assembler::e16);
    if (con >= BitsPerShort) {
      __ vxor_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */),
                 as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
      return;
    }
    __ vsll_vi(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */), con);
  
#line 18458 "ad_riscv.cpp"
  }
}

void vlslI_immNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// shift
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1669 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    uint32_t con = (unsigned)opnd_array(2)->constant()& 0x1f;
    __ vsetvli(t0, x0, Assembler::e32);
    __ vsll_vi(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */), con);
  
#line 18477 "ad_riscv.cpp"
  }
}

void vlslL_immNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// shift
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1682 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    uint32_t con = (unsigned)opnd_array(2)->constant()& 0x1f;
    __ vsetvli(t0, x0, Assembler::e64);
    __ vsll_vi(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */), con);
  
#line 18496 "ad_riscv.cpp"
  }
}

void vshiftcntBNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// cnt
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1695 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e8);
    __ vmv_v_x(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* cnt */));
  
#line 18513 "ad_riscv.cpp"
  }
}

void vshiftcntB_0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// cnt
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1695 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e8);
    __ vmv_v_x(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* cnt */));
  
#line 18530 "ad_riscv.cpp"
  }
}

void vshiftcntSNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// cnt
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1708 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e16);
    __ vmv_v_x(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* cnt */));
  
#line 18547 "ad_riscv.cpp"
  }
}

void vshiftcntS_0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// cnt
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1708 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e16);
    __ vmv_v_x(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* cnt */));
  
#line 18564 "ad_riscv.cpp"
  }
}

void vshiftcntINode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// cnt
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1720 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e32);
    __ vmv_v_x(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* cnt */));
  
#line 18581 "ad_riscv.cpp"
  }
}

void vshiftcntI_0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// cnt
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1720 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e32);
    __ vmv_v_x(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* cnt */));
  
#line 18598 "ad_riscv.cpp"
  }
}

void vshiftcntLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// cnt
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1732 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e64);
    __ vmv_v_x(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* cnt */));
  
#line 18615 "ad_riscv.cpp"
  }
}

void vshiftcntL_0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// cnt
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1732 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e64);
    __ vmv_v_x(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* cnt */));
  
#line 18632 "ad_riscv.cpp"
  }
}

void vsqrtFNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1745 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e32);
    __ vfsqrt_v(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 18649 "ad_riscv.cpp"
  }
}

void vsqrtDNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1756 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e64);
    __ vfsqrt_v(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 18666 "ad_riscv.cpp"
  }
}

void vsubBNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1769 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e8);
    __ vsub_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
               as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 18685 "ad_riscv.cpp"
  }
}

void vsubSNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1781 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e16);
    __ vsub_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
               as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 18704 "ad_riscv.cpp"
  }
}

void vsubINode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1793 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e32);
    __ vsub_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
               as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 18723 "ad_riscv.cpp"
  }
}

void vsubLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1805 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e64);
    __ vsub_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
               as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 18742 "ad_riscv.cpp"
  }
}

void vsubFNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1817 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e32);
    __ vfsub_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
                as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 18761 "ad_riscv.cpp"
  }
}

void vsubDNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1829 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ vsetvli(t0, x0, Assembler::e64);
    __ vfsub_vv(as_VectorRegister(opnd_array(0)->reg(ra_,this)/* dst */), as_VectorRegister(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
                as_VectorRegister(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 18780 "ad_riscv.cpp"
  }
}

void vstring_equalsLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// str1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// str2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// cnt
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// v1
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// v2
  unsigned idx6 = idx5 + opnd_array(5)->num_edges(); 	// v3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1846 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    // Count is in 8-bit bytes; non-Compact chars are 16 bits.
    __ string_equals_v(opnd_array(1)->as_Register(ra_,this,idx1)/* str1 */, opnd_array(2)->as_Register(ra_,this,idx2)/* str2 */,
                       opnd_array(0)->as_Register(ra_,this)/* result */, opnd_array(3)->as_Register(ra_,this,idx3)/* cnt */, 1);
  
#line 18803 "ad_riscv.cpp"
  }
}

void vstring_equalsUNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// str1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// str2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// cnt
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// v1
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// v2
  unsigned idx6 = idx5 + opnd_array(5)->num_edges(); 	// v3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1863 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    // Count is in 8-bit bytes; non-Compact chars are 16 bits.
    __ string_equals_v(opnd_array(1)->as_Register(ra_,this,idx1)/* str1 */, opnd_array(2)->as_Register(ra_,this,idx2)/* str2 */,
                       opnd_array(0)->as_Register(ra_,this)/* result */, opnd_array(3)->as_Register(ra_,this,idx3)/* cnt */, 2);
  
#line 18826 "ad_riscv.cpp"
  }
}

void varray_equalsBNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// ary1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// ary2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// v1
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// v2
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// v3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1879 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ arrays_equals_v(opnd_array(1)->as_Register(ra_,this,idx1)/* ary1 */, opnd_array(2)->as_Register(ra_,this,idx2)/* ary2 */,
                       opnd_array(0)->as_Register(ra_,this)/* result */, as_Register(R28_enc), 1);
    
#line 18847 "ad_riscv.cpp"
  }
}

void varray_equalsCNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// ary1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// ary2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// v1
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// v2
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// v3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1894 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ arrays_equals_v(opnd_array(1)->as_Register(ra_,this,idx1)/* ary1 */, opnd_array(2)->as_Register(ra_,this,idx2)/* ary2 */,
                       opnd_array(0)->as_Register(ra_,this)/* result */, as_Register(R28_enc), 2);
  
#line 18868 "ad_riscv.cpp"
  }
}

void vstring_compareUNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// str1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// cnt1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// str2
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// cnt2
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// v1
  unsigned idx6 = idx5 + opnd_array(5)->num_edges(); 	// v2
  unsigned idx7 = idx6 + opnd_array(6)->num_edges(); 	// v3
  unsigned idx8 = idx7 + opnd_array(7)->num_edges(); 	// v4
  unsigned idx9 = idx8 + opnd_array(8)->num_edges(); 	// v5
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1911 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    // Count is in 8-bit bytes; non-Compact chars are 16 bits.
    __ string_compare_v(opnd_array(1)->as_Register(ra_,this,idx1)/* str1 */, opnd_array(3)->as_Register(ra_,this,idx3)/* str2 */,
                        opnd_array(2)->as_Register(ra_,this,idx2)/* cnt1 */, opnd_array(4)->as_Register(ra_,this,idx4)/* cnt2 */, opnd_array(0)->as_Register(ra_,this)/* result */,
                        as_Register(R28_enc), as_Register(R29_enc),
                        StrIntrinsicNode::UU);
  
#line 18896 "ad_riscv.cpp"
  }
}

void vstring_compareLNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// str1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// cnt1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// str2
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// cnt2
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// v1
  unsigned idx6 = idx5 + opnd_array(5)->num_edges(); 	// v2
  unsigned idx7 = idx6 + opnd_array(6)->num_edges(); 	// v3
  unsigned idx8 = idx7 + opnd_array(7)->num_edges(); 	// v4
  unsigned idx9 = idx8 + opnd_array(8)->num_edges(); 	// v5
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1930 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ string_compare_v(opnd_array(1)->as_Register(ra_,this,idx1)/* str1 */, opnd_array(3)->as_Register(ra_,this,idx3)/* str2 */,
                        opnd_array(2)->as_Register(ra_,this,idx2)/* cnt1 */, opnd_array(4)->as_Register(ra_,this,idx4)/* cnt2 */, opnd_array(0)->as_Register(ra_,this)/* result */,
                        as_Register(R28_enc), as_Register(R29_enc),
                        StrIntrinsicNode::LL);
  
#line 18923 "ad_riscv.cpp"
  }
}

void vstring_compareULNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// str1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// cnt1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// str2
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// cnt2
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// v1
  unsigned idx6 = idx5 + opnd_array(5)->num_edges(); 	// v2
  unsigned idx7 = idx6 + opnd_array(6)->num_edges(); 	// v3
  unsigned idx8 = idx7 + opnd_array(7)->num_edges(); 	// v4
  unsigned idx9 = idx8 + opnd_array(8)->num_edges(); 	// v5
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1949 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ string_compare_v(opnd_array(1)->as_Register(ra_,this,idx1)/* str1 */, opnd_array(3)->as_Register(ra_,this,idx3)/* str2 */,
                        opnd_array(2)->as_Register(ra_,this,idx2)/* cnt1 */, opnd_array(4)->as_Register(ra_,this,idx4)/* cnt2 */, opnd_array(0)->as_Register(ra_,this)/* result */,
                        as_Register(R28_enc), as_Register(R29_enc),
                        StrIntrinsicNode::UL);
  
#line 18950 "ad_riscv.cpp"
  }
}

void vstring_compareLUNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// str1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// cnt1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// str2
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// cnt2
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// v1
  unsigned idx6 = idx5 + opnd_array(5)->num_edges(); 	// v2
  unsigned idx7 = idx6 + opnd_array(6)->num_edges(); 	// v3
  unsigned idx8 = idx7 + opnd_array(7)->num_edges(); 	// v4
  unsigned idx9 = idx8 + opnd_array(8)->num_edges(); 	// v5
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1967 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ string_compare_v(opnd_array(1)->as_Register(ra_,this,idx1)/* str1 */, opnd_array(3)->as_Register(ra_,this,idx3)/* str2 */,
                        opnd_array(2)->as_Register(ra_,this,idx2)/* cnt1 */, opnd_array(4)->as_Register(ra_,this,idx4)/* cnt2 */, opnd_array(0)->as_Register(ra_,this)/* result */,
                        as_Register(R28_enc), as_Register(R29_enc),
                        StrIntrinsicNode::LU);
  
#line 18977 "ad_riscv.cpp"
  }
}

void vstring_inflateNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// dst
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// len
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// v1
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// v2
  unsigned idx6 = idx5 + opnd_array(5)->num_edges(); 	// v3
  unsigned idx7 = idx6 + opnd_array(6)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 1985 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ byte_array_inflate_v(opnd_array(1)->as_Register(ra_,this,idx1)/* src */, opnd_array(2)->as_Register(ra_,this,idx2)/* dst */, opnd_array(3)->as_Register(ra_,this,idx3)/* len */, opnd_array(7)->as_Register(ra_,this,idx7)/* tmp */);
  
#line 18999 "ad_riscv.cpp"
  }
}

void vencode_iso_arrayNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// dst
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// len
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// result
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// v1
  unsigned idx6 = idx5 + opnd_array(5)->num_edges(); 	// v2
  unsigned idx7 = idx6 + opnd_array(6)->num_edges(); 	// v3
  unsigned idx8 = idx7 + opnd_array(7)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 2001 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ encode_iso_array_v(opnd_array(1)->as_Register(ra_,this,idx1)/* src */, opnd_array(2)->as_Register(ra_,this,idx2)/* dst */, opnd_array(3)->as_Register(ra_,this,idx3)/* len */,
                          opnd_array(4)->as_Register(ra_,this,idx4)/* result */, opnd_array(8)->as_Register(ra_,this,idx8)/* tmp */);
  
#line 19023 "ad_riscv.cpp"
  }
}

void vstring_compressNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// dst
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// len
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// result
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// v1
  unsigned idx6 = idx5 + opnd_array(5)->num_edges(); 	// v2
  unsigned idx7 = idx6 + opnd_array(6)->num_edges(); 	// v3
  unsigned idx8 = idx7 + opnd_array(7)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 2018 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ char_array_compress_v(opnd_array(1)->as_Register(ra_,this,idx1)/* src */, opnd_array(2)->as_Register(ra_,this,idx2)/* dst */, opnd_array(3)->as_Register(ra_,this,idx3)/* len */,
                             opnd_array(4)->as_Register(ra_,this,idx4)/* result */, opnd_array(8)->as_Register(ra_,this,idx8)/* tmp */);
  
#line 19047 "ad_riscv.cpp"
  }
}

void vcount_positivesNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// ary
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// len
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// result
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// v1
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// v2
  unsigned idx6 = idx5 + opnd_array(5)->num_edges(); 	// v3
  unsigned idx7 = idx6 + opnd_array(6)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 2033 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ count_positives_v(opnd_array(1)->as_Register(ra_,this,idx1)/* ary */, opnd_array(2)->as_Register(ra_,this,idx2)/* len */, opnd_array(3)->as_Register(ra_,this,idx3)/* result */, opnd_array(7)->as_Register(ra_,this,idx7)/* tmp */);
  
#line 19069 "ad_riscv.cpp"
  }
}

void vstringU_indexof_charNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// str1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// cnt1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// ch
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// result
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// tmp1
  unsigned idx6 = idx5 + opnd_array(5)->num_edges(); 	// tmp2
  unsigned idx7 = idx6 + opnd_array(6)->num_edges(); 	// v1
  unsigned idx8 = idx7 + opnd_array(7)->num_edges(); 	// v2
  unsigned idx9 = idx8 + opnd_array(8)->num_edges(); 	// v3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 2051 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ string_indexof_char_v(opnd_array(1)->as_Register(ra_,this,idx1)/* str1 */, opnd_array(2)->as_Register(ra_,this,idx2)/* cnt1 */, opnd_array(3)->as_Register(ra_,this,idx3)/* ch */,
                             opnd_array(4)->as_Register(ra_,this,idx4)/* result */, opnd_array(5)->as_Register(ra_,this,idx5)/* tmp1 */, opnd_array(6)->as_Register(ra_,this,idx6)/* tmp2 */,
                             false /* isL */);
  
#line 19095 "ad_riscv.cpp"
  }
}

void vstringL_indexof_charNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// str1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// cnt1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// ch
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// result
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// tmp1
  unsigned idx6 = idx5 + opnd_array(5)->num_edges(); 	// tmp2
  unsigned idx7 = idx6 + opnd_array(6)->num_edges(); 	// v1
  unsigned idx8 = idx7 + opnd_array(7)->num_edges(); 	// v2
  unsigned idx9 = idx8 + opnd_array(8)->num_edges(); 	// v3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 2071 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ string_indexof_char_v(opnd_array(1)->as_Register(ra_,this,idx1)/* str1 */, opnd_array(2)->as_Register(ra_,this,idx2)/* cnt1 */, opnd_array(3)->as_Register(ra_,this,idx3)/* ch */,
                             opnd_array(4)->as_Register(ra_,this,idx4)/* result */, opnd_array(5)->as_Register(ra_,this,idx5)/* tmp1 */, opnd_array(6)->as_Register(ra_,this,idx6)/* tmp2 */,
                             true /* isL */);
  
#line 19121 "ad_riscv.cpp"
  }
}

void vclearArray_reg_regNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// cnt
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// base
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// vReg1
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// vReg2
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// vReg3
  {
    C2_MacroAssembler _masm(&cbuf);

#line 2090 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_v.ad"

    __ clear_array_v(opnd_array(2)->as_Register(ra_,this,idx2)/* base */, opnd_array(1)->as_Register(ra_,this,idx1)/* cnt */);
  
#line 19141 "ad_riscv.cpp"
  }
}

void rorI_imm_bNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// shift
  {
    C2_MacroAssembler _masm(&cbuf);

#line 35 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ roriw(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */), opnd_array(2)->constant()& 0x1f);
  
#line 19158 "ad_riscv.cpp"
  }
}

void rorL_imm_bNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// shift
  {
    C2_MacroAssembler _masm(&cbuf);

#line 49 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ rori(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */), opnd_array(2)->constant()& 0x3f);
  
#line 19175 "ad_riscv.cpp"
  }
}

void rorI_reg_bNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// shift
  {
    C2_MacroAssembler _masm(&cbuf);

#line 62 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ rorw(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* shift */));
  
#line 19192 "ad_riscv.cpp"
  }
}

void rorL_reg_bNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// shift
  {
    C2_MacroAssembler _masm(&cbuf);

#line 74 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ ror(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* shift */));
  
#line 19209 "ad_riscv.cpp"
  }
}

void rolI_reg_bNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// shift
  {
    C2_MacroAssembler _masm(&cbuf);

#line 86 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ rolw(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* shift */));
  
#line 19226 "ad_riscv.cpp"
  }
}

void rolL_reg_bNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// shift
  {
    C2_MacroAssembler _masm(&cbuf);

#line 98 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ rol(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* shift */));
  
#line 19243 "ad_riscv.cpp"
  }
}

void convP2I_bNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 112 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ zext_w(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 19259 "ad_riscv.cpp"
  }
}

void convB2I_reg_reg_bNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// lshift
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// rshift
  {
    C2_MacroAssembler _masm(&cbuf);

#line 127 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ sext_b(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 19277 "ad_riscv.cpp"
  }
}

void convI2S_reg_reg_bNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// lshift
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// rshift
  {
    C2_MacroAssembler _masm(&cbuf);

#line 142 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ sext_h(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 19295 "ad_riscv.cpp"
  }
}

void convS2UI_reg_reg_bNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// mask
  {
    C2_MacroAssembler _masm(&cbuf);

#line 157 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ zext_h(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 19312 "ad_riscv.cpp"
  }
}

void convI2UL_reg_reg_bNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// mask
  {
    C2_MacroAssembler _masm(&cbuf);

#line 172 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ zext_w(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 19329 "ad_riscv.cpp"
  }
}

void bytes_reverse_int_bNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 187 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ revb_w_w(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 19345 "ad_riscv.cpp"
  }
}

void bytes_reverse_long_bNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 201 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ rev8(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 19361 "ad_riscv.cpp"
  }
}

void bytes_reverse_unsigned_short_bNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 215 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ revb_h_h_u(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 19377 "ad_riscv.cpp"
  }
}

void bytes_reverse_short_bNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 229 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ revb_h_h(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 19393 "ad_riscv.cpp"
  }
}

void shaddP_reg_reg_bNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// imm
  {
    C2_MacroAssembler _masm(&cbuf);

#line 244 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ shadd(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
             as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */),
             as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
             t0,
             opnd_array(3)->constant());
  
#line 19415 "ad_riscv.cpp"
  }
}

void shaddP_reg_reg_ext_bNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// imm
  {
    C2_MacroAssembler _masm(&cbuf);

#line 262 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ shadd(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
             as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */),
             as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
             t0,
             opnd_array(3)->constant());
  
#line 19437 "ad_riscv.cpp"
  }
}

void shaddL_reg_reg_bNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// imm
  {
    C2_MacroAssembler _masm(&cbuf);

#line 281 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ shadd(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
             as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */),
             as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
             t0,
             opnd_array(3)->constant());
  
#line 19459 "ad_riscv.cpp"
  }
}

void shaddL_reg_reg_b_0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src2
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// imm
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src1
  {
    C2_MacroAssembler _masm(&cbuf);

#line 281 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ shadd(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
             as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src2 */),
             as_Register(opnd_array(3)->reg(ra_,this,idx3)/* src1 */),
             t0,
             opnd_array(2)->constant());
  
#line 19481 "ad_riscv.cpp"
  }
}

void shaddL_reg_reg_ext_bNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// imm
  {
    C2_MacroAssembler _masm(&cbuf);

#line 299 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ shadd(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
             as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */),
             as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
             t0,
             opnd_array(3)->constant());
  
#line 19503 "ad_riscv.cpp"
  }
}

void shaddL_reg_reg_ext_b_0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src2
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// imm
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src1
  {
    C2_MacroAssembler _masm(&cbuf);

#line 299 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ shadd(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
             as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src2 */),
             as_Register(opnd_array(3)->reg(ra_,this,idx3)/* src1 */),
             t0,
             opnd_array(2)->constant());
  
#line 19525 "ad_riscv.cpp"
  }
}

void countLeadingZerosI_bNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 318 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ clzw(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 19541 "ad_riscv.cpp"
  }
}

void countLeadingZerosL_bNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 332 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ clz(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 19557 "ad_riscv.cpp"
  }
}

void countTrailingZerosI_bNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 346 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ ctzw(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 19573 "ad_riscv.cpp"
  }
}

void countTrailingZerosL_bNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 360 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ ctz(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 19589 "ad_riscv.cpp"
  }
}

void popCountI_bNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 375 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ cpopw(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 19605 "ad_riscv.cpp"
  }
}

void popCountL_bNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 390 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ cpop(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
  
#line 19621 "ad_riscv.cpp"
  }
}

void minI_reg_bNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 405 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ min(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 19638 "ad_riscv.cpp"
  }
}

void maxI_reg_bNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  {
    C2_MacroAssembler _masm(&cbuf);

#line 419 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ max(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */), as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 19655 "ad_riscv.cpp"
  }
}

void absI_reg_bNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 437 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ negw(t0, as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
    __ max(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */), t0);
  
#line 19672 "ad_riscv.cpp"
  }
}

void absL_reg_bNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src
  {
    C2_MacroAssembler _masm(&cbuf);

#line 455 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ neg(t0, as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */));
    __ max(as_Register(opnd_array(0)->reg(ra_,this)/* dst */), as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src */), t0);
  
#line 19689 "ad_riscv.cpp"
  }
}

void andnI_reg_reg_bNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// m1
  {
    C2_MacroAssembler _masm(&cbuf);

#line 471 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ andn(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
            as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
            as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 19709 "ad_riscv.cpp"
  }
}

void andnI_reg_reg_b_0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src2
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// m1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src1
  {
    C2_MacroAssembler _masm(&cbuf);

#line 471 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ andn(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
            as_Register(opnd_array(3)->reg(ra_,this,idx3)/* src1 */),
            as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src2 */));
  
#line 19729 "ad_riscv.cpp"
  }
}

void andnL_reg_reg_bNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// m1
  {
    C2_MacroAssembler _masm(&cbuf);

#line 487 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ andn(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
            as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
            as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 19749 "ad_riscv.cpp"
  }
}

void andnL_reg_reg_b_0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src2
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// m1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src1
  {
    C2_MacroAssembler _masm(&cbuf);

#line 487 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ andn(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
            as_Register(opnd_array(3)->reg(ra_,this,idx3)/* src1 */),
            as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src2 */));
  
#line 19769 "ad_riscv.cpp"
  }
}

void ornI_reg_reg_bNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// m1
  {
    C2_MacroAssembler _masm(&cbuf);

#line 504 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ orn(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
           as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
           as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 19789 "ad_riscv.cpp"
  }
}

void ornI_reg_reg_b_0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src2
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// m1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src1
  {
    C2_MacroAssembler _masm(&cbuf);

#line 504 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ orn(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
           as_Register(opnd_array(3)->reg(ra_,this,idx3)/* src1 */),
           as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src2 */));
  
#line 19809 "ad_riscv.cpp"
  }
}

void ornL_reg_reg_bNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src1
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// src2
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// m1
  {
    C2_MacroAssembler _masm(&cbuf);

#line 520 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ orn(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
           as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src1 */),
           as_Register(opnd_array(2)->reg(ra_,this,idx2)/* src2 */));
  
#line 19829 "ad_riscv.cpp"
  }
}

void ornL_reg_reg_b_0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 1;
  unsigned idx1 = 1; 	// src2
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// m1
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// src1
  {
    C2_MacroAssembler _masm(&cbuf);

#line 520 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv_b.ad"

    __ orn(as_Register(opnd_array(0)->reg(ra_,this)/* dst */),
           as_Register(opnd_array(3)->reg(ra_,this,idx3)/* src1 */),
           as_Register(opnd_array(1)->reg(ra_,this,idx1)/* src2 */));
  
#line 19849 "ad_riscv.cpp"
  }
}

void compareAndSwapP_shenandoahNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 41 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/gc/shenandoah/shenandoah_riscv64.ad"

    Register tmp = opnd_array(4)->as_Register(ra_,this,idx4)/* tmp */;
    __ mv(tmp, opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */); // Must not clobber oldval.
    ShenandoahBarrierSet::assembler()->cmpxchg_oop(&_masm, opnd_array(1)->as_Register(ra_,this,idx1)/* mem */, tmp, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */,
                                                   Assembler::relaxed /* acquire */, Assembler::rl /* release */,
                                                   false /* is_cae */, opnd_array(0)->as_Register(ra_,this)/* res */);
  
#line 19872 "ad_riscv.cpp"
  }
}

void compareAndSwapN_shenandoahNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 62 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/gc/shenandoah/shenandoah_riscv64.ad"

    Register tmp = opnd_array(4)->as_Register(ra_,this,idx4)/* tmp */;
    __ mv(tmp, opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */); // Must not clobber oldval.
    ShenandoahBarrierSet::assembler()->cmpxchg_oop(&_masm, opnd_array(1)->as_Register(ra_,this,idx1)/* mem */, tmp, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */,
                                                   Assembler::relaxed /* acquire */, Assembler::rl /* release */,
                                                   false /* is_cae */, opnd_array(0)->as_Register(ra_,this)/* res */);
  
#line 19895 "ad_riscv.cpp"
  }
}

void compareAndSwapPAcq_shenandoahNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 84 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/gc/shenandoah/shenandoah_riscv64.ad"

    Register tmp = opnd_array(4)->as_Register(ra_,this,idx4)/* tmp */;
    __ mv(tmp, opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */); // Must not clobber oldval.
    ShenandoahBarrierSet::assembler()->cmpxchg_oop(&_masm, opnd_array(1)->as_Register(ra_,this,idx1)/* mem */, tmp, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */,
                                                   Assembler::aq /* acquire */, Assembler::rl /* release */,
                                                   false /* is_cae */, opnd_array(0)->as_Register(ra_,this)/* res */);
  
#line 19918 "ad_riscv.cpp"
  }
}

void compareAndSwapNAcq_shenandoahNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 106 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/gc/shenandoah/shenandoah_riscv64.ad"

    Register tmp = opnd_array(4)->as_Register(ra_,this,idx4)/* tmp */;
    __ mv(tmp, opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */); // Must not clobber oldval.
    ShenandoahBarrierSet::assembler()->cmpxchg_oop(&_masm, opnd_array(1)->as_Register(ra_,this,idx1)/* mem */, tmp, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */,
                                                   Assembler::aq /* acquire */, Assembler::rl /* release */,
                                                   false /* is_cae */, opnd_array(0)->as_Register(ra_,this)/* res */);
  
#line 19941 "ad_riscv.cpp"
  }
}

void compareAndExchangeN_shenandoahNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// res
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 126 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/gc/shenandoah/shenandoah_riscv64.ad"

    Register tmp = opnd_array(5)->as_Register(ra_,this,idx5)/* tmp */;
    __ mv(tmp, opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */); // Must not clobber oldval.
    ShenandoahBarrierSet::assembler()->cmpxchg_oop(&_masm, opnd_array(1)->as_Register(ra_,this,idx1)/* mem */, tmp, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */,
                                                   Assembler::relaxed /* acquire */, Assembler::rl /* release */,
                                                   true /* is_cae */, opnd_array(4)->as_Register(ra_,this,idx4)/* res */);
  
#line 19965 "ad_riscv.cpp"
  }
}

void compareAndExchangeP_shenandoahNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// res
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 146 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/gc/shenandoah/shenandoah_riscv64.ad"

    Register tmp = opnd_array(5)->as_Register(ra_,this,idx5)/* tmp */;
    __ mv(tmp, opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */); // Must not clobber oldval.
    ShenandoahBarrierSet::assembler()->cmpxchg_oop(&_masm, opnd_array(1)->as_Register(ra_,this,idx1)/* mem */, tmp, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */,
                                                   Assembler::relaxed /* acquire */, Assembler::rl /* release */,
                                                   true /* is_cae */, opnd_array(4)->as_Register(ra_,this,idx4)/* res */);
  
#line 19989 "ad_riscv.cpp"
  }
}

void weakCompareAndSwapN_shenandoahNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 167 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/gc/shenandoah/shenandoah_riscv64.ad"

    Register tmp = opnd_array(4)->as_Register(ra_,this,idx4)/* tmp */;
    __ mv(tmp, opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */); // Must not clobber oldval.
    // Weak is not current supported by ShenandoahBarrierSet::cmpxchg_oop
    ShenandoahBarrierSet::assembler()->cmpxchg_oop(&_masm, opnd_array(1)->as_Register(ra_,this,idx1)/* mem */, tmp, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */,
                                                   Assembler::relaxed /* acquire */, Assembler::rl /* release */,
                                                   false /* is_cae */, opnd_array(0)->as_Register(ra_,this)/* res */);
  
#line 20013 "ad_riscv.cpp"
  }
}

void compareAndExchangeNAcq_shenandoahNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// res
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 189 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/gc/shenandoah/shenandoah_riscv64.ad"

    Register tmp = opnd_array(5)->as_Register(ra_,this,idx5)/* tmp */;
    __ mv(tmp, opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */);
    ShenandoahBarrierSet::assembler()->cmpxchg_oop(&_masm, opnd_array(1)->as_Register(ra_,this,idx1)/* mem */, tmp, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */,
                                                   Assembler::aq /* acquire */, Assembler::rl /* release */,
                                                   true /* is_cae */, opnd_array(4)->as_Register(ra_,this,idx4)/* res */);
  
#line 20037 "ad_riscv.cpp"
  }
}

void compareAndExchangePAcq_shenandoahNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// res
  unsigned idx5 = idx4 + opnd_array(4)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 210 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/gc/shenandoah/shenandoah_riscv64.ad"

    Register tmp = opnd_array(5)->as_Register(ra_,this,idx5)/* tmp */;
    __ mv(tmp, opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */);
    ShenandoahBarrierSet::assembler()->cmpxchg_oop(&_masm, opnd_array(1)->as_Register(ra_,this,idx1)/* mem */, tmp, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */,
                                                   Assembler::aq /* acquire */, Assembler::rl /* release */,
                                                   true /* is_cae */, opnd_array(4)->as_Register(ra_,this,idx4)/* res */);
  
#line 20061 "ad_riscv.cpp"
  }
}

void weakCompareAndSwapP_shenandoahNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 230 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/gc/shenandoah/shenandoah_riscv64.ad"

    Register tmp = opnd_array(4)->as_Register(ra_,this,idx4)/* tmp */;
    __ mv(tmp, opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */); // Must not clobber oldval.
    ShenandoahBarrierSet::assembler()->cmpxchg_oop(&_masm, opnd_array(1)->as_Register(ra_,this,idx1)/* mem */, tmp, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */,
                                                   Assembler::relaxed /* acquire */, Assembler::rl /* release */,
                                                   false /* is_cae */, opnd_array(0)->as_Register(ra_,this)/* res */);
  
#line 20084 "ad_riscv.cpp"
  }
}

void weakCompareAndSwapNAcq_shenandoahNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 252 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/gc/shenandoah/shenandoah_riscv64.ad"

    Register tmp = opnd_array(4)->as_Register(ra_,this,idx4)/* tmp */;
    __ mv(tmp, opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */); // Must not clobber oldval.
    // Weak is not current supported by ShenandoahBarrierSet::cmpxchg_oop
    ShenandoahBarrierSet::assembler()->cmpxchg_oop(&_masm, opnd_array(1)->as_Register(ra_,this,idx1)/* mem */, tmp, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */,
                                                   Assembler::aq /* acquire */, Assembler::rl /* release */,
                                                   false /* is_cae */, opnd_array(0)->as_Register(ra_,this)/* res */);
  
#line 20108 "ad_riscv.cpp"
  }
}

void weakCompareAndSwapPAcq_shenandoahNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// tmp
  {
    C2_MacroAssembler _masm(&cbuf);

#line 275 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/gc/shenandoah/shenandoah_riscv64.ad"

    Register tmp = opnd_array(4)->as_Register(ra_,this,idx4)/* tmp */;
    __ mv(tmp, opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */); // Must not clobber oldval.
    // Weak is not current supported by ShenandoahBarrierSet::cmpxchg_oop
    ShenandoahBarrierSet::assembler()->cmpxchg_oop(&_masm, opnd_array(1)->as_Register(ra_,this,idx1)/* mem */, tmp, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */,
                                                   Assembler::aq /* acquire */, Assembler::rl /* release */,
                                                   false /* is_cae */, opnd_array(0)->as_Register(ra_,this)/* res */);
  
#line 20132 "ad_riscv.cpp"
  }
}

void zLoadPNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// dst
  {
    C2_MacroAssembler _masm(&cbuf);

#line 65 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/gc/z/z_riscv64.ad"

    const Address ref_addr (as_Register(opnd_array(1)->base(ra_,this,idx1)), opnd_array(1)->disp(ra_,this,idx1));
    __ ld(opnd_array(2)->as_Register(ra_,this,idx2)/* dst */, ref_addr);
    z_load_barrier(_masm, this, ref_addr, opnd_array(2)->as_Register(ra_,this,idx2)/* dst */, t0 /* tmp */, barrier_data());
  
#line 20151 "ad_riscv.cpp"
  }
}

void zCompareAndSwapPNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// res
  {
    C2_MacroAssembler _masm(&cbuf);

#line 85 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/gc/z/z_riscv64.ad"

    Label failed;
    guarantee(opnd_array(1)->index(ra_,this,idx1)== -1 && opnd_array(1)->disp(ra_,this,idx1)== 0, "impossible encoding");
    __ cmpxchg(opnd_array(1)->as_Register(ra_,this,idx1)/* mem */, opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int64,
               Assembler::relaxed /* acquire */, Assembler::rl /* release */, opnd_array(4)->as_Register(ra_,this,idx4)/* res */,
               true /* result_as_bool */);
    __ beqz(opnd_array(4)->as_Register(ra_,this,idx4)/* res */, failed);
    __ mv(t0, opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */);
    __ bind(failed);
    if (barrier_data() != ZLoadBarrierElided) {
      Label good;
      __ ld(t1, Address(xthread, ZThreadLocalData::address_bad_mask_offset()), t1 /* tmp */);
      __ andr(t1, t1, t0);
      __ beqz(t1, good);
      z_load_barrier_slow_path(_masm, this, Address(opnd_array(1)->as_Register(ra_,this,idx1)/* mem */), t0 /* ref */, t1 /* tmp */);
      __ cmpxchg(opnd_array(1)->as_Register(ra_,this,idx1)/* mem */, opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int64,
                 Assembler::relaxed /* acquire */, Assembler::rl /* release */, opnd_array(4)->as_Register(ra_,this,idx4)/* res */,
                 true /* result_as_bool */);
      __ bind(good);
    }
  
#line 20188 "ad_riscv.cpp"
  }
}

void zCompareAndSwapP_0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// res
  {
    C2_MacroAssembler _masm(&cbuf);

#line 85 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/gc/z/z_riscv64.ad"

    Label failed;
    guarantee(opnd_array(1)->index(ra_,this,idx1)== -1 && opnd_array(1)->disp(ra_,this,idx1)== 0, "impossible encoding");
    __ cmpxchg(opnd_array(1)->as_Register(ra_,this,idx1)/* mem */, opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int64,
               Assembler::relaxed /* acquire */, Assembler::rl /* release */, opnd_array(4)->as_Register(ra_,this,idx4)/* res */,
               true /* result_as_bool */);
    __ beqz(opnd_array(4)->as_Register(ra_,this,idx4)/* res */, failed);
    __ mv(t0, opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */);
    __ bind(failed);
    if (barrier_data() != ZLoadBarrierElided) {
      Label good;
      __ ld(t1, Address(xthread, ZThreadLocalData::address_bad_mask_offset()), t1 /* tmp */);
      __ andr(t1, t1, t0);
      __ beqz(t1, good);
      z_load_barrier_slow_path(_masm, this, Address(opnd_array(1)->as_Register(ra_,this,idx1)/* mem */), t0 /* ref */, t1 /* tmp */);
      __ cmpxchg(opnd_array(1)->as_Register(ra_,this,idx1)/* mem */, opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int64,
                 Assembler::relaxed /* acquire */, Assembler::rl /* release */, opnd_array(4)->as_Register(ra_,this,idx4)/* res */,
                 true /* result_as_bool */);
      __ bind(good);
    }
  
#line 20225 "ad_riscv.cpp"
  }
}

void zCompareAndSwapPAcqNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// res
  {
    C2_MacroAssembler _masm(&cbuf);

#line 121 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/gc/z/z_riscv64.ad"

    Label failed;
    guarantee(opnd_array(1)->index(ra_,this,idx1)== -1 && opnd_array(1)->disp(ra_,this,idx1)== 0, "impossible encoding");
    __ cmpxchg(opnd_array(1)->as_Register(ra_,this,idx1)/* mem */, opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int64,
               Assembler::aq /* acquire */, Assembler::rl /* release */, opnd_array(4)->as_Register(ra_,this,idx4)/* res */,
               true /* result_as_bool */);
    __ beqz(opnd_array(4)->as_Register(ra_,this,idx4)/* res */, failed);
    __ mv(t0, opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */);
    __ bind(failed);
    if (barrier_data() != ZLoadBarrierElided) {
      Label good;
      __ ld(t1, Address(xthread, ZThreadLocalData::address_bad_mask_offset()), t1 /* tmp */);
      __ andr(t1, t1, t0);
      __ beqz(t1, good);
      z_load_barrier_slow_path(_masm, this, Address(opnd_array(1)->as_Register(ra_,this,idx1)/* mem */), t0 /* ref */, t1 /* tmp */);
      __ cmpxchg(opnd_array(1)->as_Register(ra_,this,idx1)/* mem */, opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int64,
                 Assembler::aq /* acquire */, Assembler::rl /* release */, opnd_array(4)->as_Register(ra_,this,idx4)/* res */,
                 true /* result_as_bool */);
      __ bind(good);
    }
  
#line 20262 "ad_riscv.cpp"
  }
}

void zCompareAndSwapPAcq_0Node::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// res
  {
    C2_MacroAssembler _masm(&cbuf);

#line 121 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/gc/z/z_riscv64.ad"

    Label failed;
    guarantee(opnd_array(1)->index(ra_,this,idx1)== -1 && opnd_array(1)->disp(ra_,this,idx1)== 0, "impossible encoding");
    __ cmpxchg(opnd_array(1)->as_Register(ra_,this,idx1)/* mem */, opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int64,
               Assembler::aq /* acquire */, Assembler::rl /* release */, opnd_array(4)->as_Register(ra_,this,idx4)/* res */,
               true /* result_as_bool */);
    __ beqz(opnd_array(4)->as_Register(ra_,this,idx4)/* res */, failed);
    __ mv(t0, opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */);
    __ bind(failed);
    if (barrier_data() != ZLoadBarrierElided) {
      Label good;
      __ ld(t1, Address(xthread, ZThreadLocalData::address_bad_mask_offset()), t1 /* tmp */);
      __ andr(t1, t1, t0);
      __ beqz(t1, good);
      z_load_barrier_slow_path(_masm, this, Address(opnd_array(1)->as_Register(ra_,this,idx1)/* mem */), t0 /* ref */, t1 /* tmp */);
      __ cmpxchg(opnd_array(1)->as_Register(ra_,this,idx1)/* mem */, opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int64,
                 Assembler::aq /* acquire */, Assembler::rl /* release */, opnd_array(4)->as_Register(ra_,this,idx4)/* res */,
                 true /* result_as_bool */);
      __ bind(good);
    }
  
#line 20299 "ad_riscv.cpp"
  }
}

void zCompareAndExchangePNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// res
  {
    C2_MacroAssembler _masm(&cbuf);

#line 155 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/gc/z/z_riscv64.ad"

    guarantee(opnd_array(1)->index(ra_,this,idx1)== -1 && opnd_array(1)->disp(ra_,this,idx1)== 0, "impossible encoding");
    __ cmpxchg(opnd_array(1)->as_Register(ra_,this,idx1)/* mem */, opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int64,
               Assembler::relaxed /* acquire */, Assembler::rl /* release */, opnd_array(4)->as_Register(ra_,this,idx4)/* res */);
    if (barrier_data() != ZLoadBarrierElided) {
      Label good;
      __ ld(t0, Address(xthread, ZThreadLocalData::address_bad_mask_offset()));
      __ andr(t0, t0, opnd_array(4)->as_Register(ra_,this,idx4)/* res */);
      __ beqz(t0, good);
      z_load_barrier_slow_path(_masm, this, Address(opnd_array(1)->as_Register(ra_,this,idx1)/* mem */), opnd_array(4)->as_Register(ra_,this,idx4)/* res */, t0 /* tmp */);
      __ cmpxchg(opnd_array(1)->as_Register(ra_,this,idx1)/* mem */, opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int64,
                 Assembler::relaxed /* acquire */, Assembler::rl /* release */, opnd_array(4)->as_Register(ra_,this,idx4)/* res */);
      __ bind(good);
    }
  
#line 20330 "ad_riscv.cpp"
  }
}

void zCompareAndExchangePAcqNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// oldval
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// newval
  unsigned idx4 = idx3 + opnd_array(3)->num_edges(); 	// res
  {
    C2_MacroAssembler _masm(&cbuf);

#line 183 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/gc/z/z_riscv64.ad"

    guarantee(opnd_array(1)->index(ra_,this,idx1)== -1 && opnd_array(1)->disp(ra_,this,idx1)== 0, "impossible encoding");
    __ cmpxchg(opnd_array(1)->as_Register(ra_,this,idx1)/* mem */, opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int64,
               Assembler::aq /* acquire */, Assembler::rl /* release */, opnd_array(4)->as_Register(ra_,this,idx4)/* res */);
    if (barrier_data() != ZLoadBarrierElided) {
      Label good;
      __ ld(t0, Address(xthread, ZThreadLocalData::address_bad_mask_offset()));
      __ andr(t0, t0, opnd_array(4)->as_Register(ra_,this,idx4)/* res */);
      __ beqz(t0, good);
      z_load_barrier_slow_path(_masm, this, Address(opnd_array(1)->as_Register(ra_,this,idx1)/* mem */), opnd_array(4)->as_Register(ra_,this,idx4)/* res */, t0 /* tmp */);
      __ cmpxchg(opnd_array(1)->as_Register(ra_,this,idx1)/* mem */, opnd_array(2)->as_Register(ra_,this,idx2)/* oldval */, opnd_array(3)->as_Register(ra_,this,idx3)/* newval */, Assembler::int64,
                 Assembler::aq /* acquire */, Assembler::rl /* release */, opnd_array(4)->as_Register(ra_,this,idx4)/* res */);
      __ bind(good);
    }
  
#line 20361 "ad_riscv.cpp"
  }
}

void zGetAndSetPNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// newv
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// prev
  {
    C2_MacroAssembler _masm(&cbuf);

#line 211 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/gc/z/z_riscv64.ad"

    __ atomic_xchg(opnd_array(3)->as_Register(ra_,this,idx3)/* prev */, opnd_array(2)->as_Register(ra_,this,idx2)/* newv */, as_Register(opnd_array(1)->base(ra_,this,idx1)));
    z_load_barrier(_masm, this, Address(noreg, 0), opnd_array(3)->as_Register(ra_,this,idx3)/* prev */, t0 /* tmp */, barrier_data());
  
#line 20380 "ad_riscv.cpp"
  }
}

void zGetAndSetPAcqNode::emit(CodeBuffer& cbuf, PhaseRegAlloc* ra_) const {
  cbuf.set_insts_mark();
  // Start at oper_input_base() and count operands
  unsigned idx0 = 2;
  unsigned idx1 = 2; 	// mem
  unsigned idx2 = idx1 + opnd_array(1)->num_edges(); 	// newv
  unsigned idx3 = idx2 + opnd_array(2)->num_edges(); 	// prev
  {
    C2_MacroAssembler _masm(&cbuf);

#line 228 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/gc/z/z_riscv64.ad"

    __ atomic_xchgal(opnd_array(3)->as_Register(ra_,this,idx3)/* prev */, opnd_array(2)->as_Register(ra_,this,idx2)/* newv */, as_Register(opnd_array(1)->base(ra_,this,idx1)));
    z_load_barrier(_masm, this, Address(noreg, 0), opnd_array(3)->as_Register(ra_,this,idx3)/* prev */, t0 /* tmp */, barrier_data());
  
#line 20399 "ad_riscv.cpp"
  }
}

const MachOper* loadBNode::memory_operand() const { return _opnds[1]; }
const MachOper* loadB2LNode::memory_operand() const { return _opnds[1]; }
const MachOper* loadUBNode::memory_operand() const { return _opnds[1]; }
const MachOper* loadUB2LNode::memory_operand() const { return _opnds[1]; }
const MachOper* loadSNode::memory_operand() const { return _opnds[1]; }
const MachOper* loadS2LNode::memory_operand() const { return _opnds[1]; }
const MachOper* loadUSNode::memory_operand() const { return _opnds[1]; }
const MachOper* loadUS2LNode::memory_operand() const { return _opnds[1]; }
const MachOper* loadINode::memory_operand() const { return _opnds[1]; }
const MachOper* loadI2LNode::memory_operand() const { return _opnds[1]; }
const MachOper* loadUI2LNode::memory_operand() const { return _opnds[1]; }
const MachOper* loadLNode::memory_operand() const { return _opnds[1]; }
const MachOper* loadRangeNode::memory_operand() const { return _opnds[1]; }
const MachOper* loadPNode::memory_operand() const { return _opnds[1]; }
const MachOper* loadNNode::memory_operand() const { return _opnds[1]; }
const MachOper* loadKlassNode::memory_operand() const { return _opnds[1]; }
const MachOper* loadNKlassNode::memory_operand() const { return _opnds[1]; }
const MachOper* loadFNode::memory_operand() const { return _opnds[1]; }
const MachOper* loadDNode::memory_operand() const { return _opnds[1]; }
const MachOper* storeimmCM0Node::memory_operand() const { return _opnds[1]; }
const MachOper* storeimmCM0_orderedNode::memory_operand() const { return _opnds[1]; }
const MachOper* storeBNode::memory_operand() const { return _opnds[1]; }
const MachOper* storeimmB0Node::memory_operand() const { return _opnds[1]; }
const MachOper* storeCNode::memory_operand() const { return _opnds[1]; }
const MachOper* storeimmC0Node::memory_operand() const { return _opnds[1]; }
const MachOper* storeINode::memory_operand() const { return _opnds[1]; }
const MachOper* storeimmI0Node::memory_operand() const { return _opnds[1]; }
const MachOper* storeLNode::memory_operand() const { return _opnds[1]; }
const MachOper* storeimmL0Node::memory_operand() const { return _opnds[1]; }
const MachOper* storePNode::memory_operand() const { return _opnds[1]; }
const MachOper* storeimmP0Node::memory_operand() const { return _opnds[1]; }
const MachOper* storeNNode::memory_operand() const { return _opnds[1]; }
const MachOper* storeImmN0Node::memory_operand() const { return _opnds[1]; }
const MachOper* storeFNode::memory_operand() const { return _opnds[1]; }
const MachOper* storeDNode::memory_operand() const { return _opnds[1]; }
const MachOper* storeNKlassNode::memory_operand() const { return _opnds[1]; }
const MachOper* compareAndSwapBNode::memory_operand() const { return _opnds[1]; }
const MachOper* compareAndSwapSNode::memory_operand() const { return _opnds[1]; }
const MachOper* compareAndSwapINode::memory_operand() const { return _opnds[1]; }
const MachOper* compareAndSwapLNode::memory_operand() const { return _opnds[1]; }
const MachOper* compareAndSwapPNode::memory_operand() const { return _opnds[1]; }
const MachOper* compareAndSwapNNode::memory_operand() const { return _opnds[1]; }
const MachOper* compareAndSwapBAcqNode::memory_operand() const { return _opnds[1]; }
const MachOper* compareAndSwapSAcqNode::memory_operand() const { return _opnds[1]; }
const MachOper* compareAndSwapIAcqNode::memory_operand() const { return _opnds[1]; }
const MachOper* compareAndSwapLAcqNode::memory_operand() const { return _opnds[1]; }
const MachOper* compareAndSwapPAcqNode::memory_operand() const { return _opnds[1]; }
const MachOper* compareAndSwapNAcqNode::memory_operand() const { return _opnds[1]; }
const MachOper* compareAndExchangeBNode::memory_operand() const { return _opnds[1]; }
const MachOper* compareAndExchangeSNode::memory_operand() const { return _opnds[1]; }
const MachOper* compareAndExchangeINode::memory_operand() const { return _opnds[1]; }
const MachOper* compareAndExchangeLNode::memory_operand() const { return _opnds[1]; }
const MachOper* compareAndExchangeNNode::memory_operand() const { return _opnds[1]; }
const MachOper* compareAndExchangePNode::memory_operand() const { return _opnds[1]; }
const MachOper* compareAndExchangeBAcqNode::memory_operand() const { return _opnds[1]; }
const MachOper* compareAndExchangeSAcqNode::memory_operand() const { return _opnds[1]; }
const MachOper* compareAndExchangeIAcqNode::memory_operand() const { return _opnds[1]; }
const MachOper* compareAndExchangeLAcqNode::memory_operand() const { return _opnds[1]; }
const MachOper* compareAndExchangeNAcqNode::memory_operand() const { return _opnds[1]; }
const MachOper* compareAndExchangePAcqNode::memory_operand() const { return _opnds[1]; }
const MachOper* weakCompareAndSwapBNode::memory_operand() const { return _opnds[1]; }
const MachOper* weakCompareAndSwapSNode::memory_operand() const { return _opnds[1]; }
const MachOper* weakCompareAndSwapINode::memory_operand() const { return _opnds[1]; }
const MachOper* weakCompareAndSwapLNode::memory_operand() const { return _opnds[1]; }
const MachOper* weakCompareAndSwapNNode::memory_operand() const { return _opnds[1]; }
const MachOper* weakCompareAndSwapPNode::memory_operand() const { return _opnds[1]; }
const MachOper* weakCompareAndSwapBAcqNode::memory_operand() const { return _opnds[1]; }
const MachOper* weakCompareAndSwapSAcqNode::memory_operand() const { return _opnds[1]; }
const MachOper* weakCompareAndSwapIAcqNode::memory_operand() const { return _opnds[1]; }
const MachOper* weakCompareAndSwapLAcqNode::memory_operand() const { return _opnds[1]; }
const MachOper* weakCompareAndSwapNAcqNode::memory_operand() const { return _opnds[1]; }
const MachOper* weakCompareAndSwapPAcqNode::memory_operand() const { return _opnds[1]; }
const MachOper* get_and_setINode::memory_operand() const { return _opnds[1]; }
const MachOper* get_and_setLNode::memory_operand() const { return _opnds[1]; }
const MachOper* get_and_setNNode::memory_operand() const { return _opnds[1]; }
const MachOper* get_and_setPNode::memory_operand() const { return _opnds[1]; }
const MachOper* get_and_setIAcqNode::memory_operand() const { return _opnds[1]; }
const MachOper* get_and_setLAcqNode::memory_operand() const { return _opnds[1]; }
const MachOper* get_and_setNAcqNode::memory_operand() const { return _opnds[1]; }
const MachOper* get_and_setPAcqNode::memory_operand() const { return _opnds[1]; }
const MachOper* get_and_addLNode::memory_operand() const { return _opnds[1]; }
const MachOper* get_and_addL_no_resNode::memory_operand() const { return _opnds[1]; }
const MachOper* get_and_addLiNode::memory_operand() const { return _opnds[1]; }
const MachOper* get_and_addLi_no_resNode::memory_operand() const { return _opnds[1]; }
const MachOper* get_and_addINode::memory_operand() const { return _opnds[1]; }
const MachOper* get_and_addI_no_resNode::memory_operand() const { return _opnds[1]; }
const MachOper* get_and_addIiNode::memory_operand() const { return _opnds[1]; }
const MachOper* get_and_addIi_no_resNode::memory_operand() const { return _opnds[1]; }
const MachOper* get_and_addLAcqNode::memory_operand() const { return _opnds[1]; }
const MachOper* get_and_addL_no_resAcqNode::memory_operand() const { return _opnds[1]; }
const MachOper* get_and_addLiAcqNode::memory_operand() const { return _opnds[1]; }
const MachOper* get_and_addLi_no_resAcqNode::memory_operand() const { return _opnds[1]; }
const MachOper* get_and_addIAcqNode::memory_operand() const { return _opnds[1]; }
const MachOper* get_and_addI_no_resAcqNode::memory_operand() const { return _opnds[1]; }
const MachOper* get_and_addIiAcqNode::memory_operand() const { return _opnds[1]; }
const MachOper* get_and_addIi_no_resAcqNode::memory_operand() const { return _opnds[1]; }
const MachOper* loadVNode::memory_operand() const { return _opnds[1]; }
const MachOper* storeVNode::memory_operand() const { return _opnds[1]; }
const MachOper* compareAndSwapP_shenandoahNode::memory_operand() const { return _opnds[1]; }
const MachOper* compareAndSwapN_shenandoahNode::memory_operand() const { return _opnds[1]; }
const MachOper* compareAndSwapPAcq_shenandoahNode::memory_operand() const { return _opnds[1]; }
const MachOper* compareAndSwapNAcq_shenandoahNode::memory_operand() const { return _opnds[1]; }
const MachOper* compareAndExchangeN_shenandoahNode::memory_operand() const { return _opnds[1]; }
const MachOper* compareAndExchangeP_shenandoahNode::memory_operand() const { return _opnds[1]; }
const MachOper* weakCompareAndSwapN_shenandoahNode::memory_operand() const { return _opnds[1]; }
const MachOper* compareAndExchangeNAcq_shenandoahNode::memory_operand() const { return _opnds[1]; }
const MachOper* compareAndExchangePAcq_shenandoahNode::memory_operand() const { return _opnds[1]; }
const MachOper* weakCompareAndSwapP_shenandoahNode::memory_operand() const { return _opnds[1]; }
const MachOper* weakCompareAndSwapNAcq_shenandoahNode::memory_operand() const { return _opnds[1]; }
const MachOper* weakCompareAndSwapPAcq_shenandoahNode::memory_operand() const { return _opnds[1]; }
const MachOper* zLoadPNode::memory_operand() const { return _opnds[1]; }
const MachOper* zCompareAndSwapPNode::memory_operand() const { return _opnds[1]; }
const MachOper* zCompareAndSwapP_0Node::memory_operand() const { return _opnds[1]; }
const MachOper* zCompareAndSwapPAcqNode::memory_operand() const { return _opnds[1]; }
const MachOper* zCompareAndSwapPAcq_0Node::memory_operand() const { return _opnds[1]; }
const MachOper* zCompareAndExchangePNode::memory_operand() const { return _opnds[1]; }
const MachOper* zCompareAndExchangePAcqNode::memory_operand() const { return _opnds[1]; }
const MachOper* zGetAndSetPNode::memory_operand() const { return _opnds[1]; }
const MachOper* zGetAndSetPAcqNode::memory_operand() const { return _opnds[1]; }


const bool Matcher::has_match_rule(int opcode) {
  assert(_last_machine_leaf < opcode && opcode < _last_opcode, "opcode in range");
  return _hasMatchRule[opcode];
}

const bool Matcher::_hasMatchRule[_last_opcode] = {
    false,  // Node
    false,  // Set
    false,  // RegN
    false,  // RegI
    false,  // RegP
    false,  // RegF
    false,  // RegD
    false,  // RegL
    false,  // VecA
    false,  // VecS
    false,  // VecD
    false,  // VecX
    false,  // VecY
    false,  // VecZ
    false,  // RegVectMask
    false,  // RegFlags
    false,  // _last_machine_leaf
    true ,  // AbsD
    true ,  // AbsF
    true ,  // AbsI
    true ,  // AbsL
    true ,  // AddD
    true ,  // AddF
    true ,  // AddI
    true ,  // AddL
    true ,  // AddP
    false,  // Allocate
    false,  // AllocateArray
    true ,  // AndI
    true ,  // AndL
    false,  // ArrayCopy
    true ,  // AryEq
    false,  // AtanD
    true ,  // Binary
    false,  // Blackhole
    true ,  // Bool
    false,  // BoxLock
    true ,  // ReverseBytesI
    true ,  // ReverseBytesL
    true ,  // ReverseBytesUS
    true ,  // ReverseBytesS
    false,  // ReverseBytesV
    false,  // CProj
    false,  // CacheWB
    false,  // CacheWBPreSync
    false,  // CacheWBPostSync
    true ,  // CallDynamicJava
    false,  // CallJava
    true ,  // CallLeaf
    true ,  // CallLeafNoFP
    false,  // CallLeafVector
    true ,  // CallRuntime
    true ,  // CallStaticJava
    true ,  // CastDD
    true ,  // CastFF
    true ,  // CastII
    true ,  // CastLL
    true ,  // CastVV
    true ,  // CastX2P
    true ,  // CastP2X
    true ,  // CastPP
    false,  // Catch
    false,  // CatchProj
    true ,  // CheckCastPP
    true ,  // ClearArray
    false,  // CompressBits
    false,  // ExpandBits
    false,  // ConstraintCast
    false,  // CMoveD
    false,  // CMoveVD
    false,  // CMoveF
    false,  // CMoveVF
    true ,  // CMoveI
    true ,  // CMoveL
    false,  // CMoveP
    false,  // CMoveN
    true ,  // CmpN
    true ,  // CmpD
    true ,  // CmpD3
    true ,  // CmpF
    true ,  // CmpF3
    true ,  // CmpI
    true ,  // CmpL
    true ,  // CmpL3
    true ,  // CmpLTMask
    true ,  // CmpP
    true ,  // CmpU
    false,  // CmpU3
    true ,  // CmpUL
    false,  // CmpUL3
    true ,  // CompareAndSwapB
    true ,  // CompareAndSwapS
    true ,  // CompareAndSwapI
    true ,  // CompareAndSwapL
    true ,  // CompareAndSwapP
    true ,  // CompareAndSwapN
    true ,  // WeakCompareAndSwapB
    true ,  // WeakCompareAndSwapS
    true ,  // WeakCompareAndSwapI
    true ,  // WeakCompareAndSwapL
    true ,  // WeakCompareAndSwapP
    true ,  // WeakCompareAndSwapN
    true ,  // CompareAndExchangeB
    true ,  // CompareAndExchangeS
    true ,  // CompareAndExchangeI
    true ,  // CompareAndExchangeL
    true ,  // CompareAndExchangeP
    true ,  // CompareAndExchangeN
    false,  // GetAndAddB
    false,  // GetAndAddS
    true ,  // GetAndAddI
    true ,  // GetAndAddL
    false,  // GetAndSetB
    false,  // GetAndSetS
    true ,  // GetAndSetI
    true ,  // GetAndSetL
    true ,  // GetAndSetP
    true ,  // GetAndSetN
    false,  // Con
    true ,  // ConN
    true ,  // ConNKlass
    true ,  // ConD
    true ,  // ConF
    true ,  // ConI
    true ,  // ConL
    true ,  // ConP
    true ,  // Conv2B
    true ,  // ConvD2F
    true ,  // ConvD2I
    true ,  // ConvD2L
    true ,  // ConvF2D
    true ,  // ConvF2I
    true ,  // ConvF2L
    true ,  // ConvI2D
    true ,  // ConvI2F
    true ,  // ConvI2L
    true ,  // ConvL2D
    true ,  // ConvL2F
    true ,  // ConvL2I
    false,  // ConvF2HF
    false,  // ConvHF2F
    false,  // CountedLoop
    true ,  // CountedLoopEnd
    false,  // OuterStripMinedLoop
    false,  // OuterStripMinedLoopEnd
    false,  // LongCountedLoop
    false,  // LongCountedLoopEnd
    true ,  // CountLeadingZerosI
    true ,  // CountLeadingZerosL
    false,  // CountLeadingZerosV
    true ,  // CountTrailingZerosI
    true ,  // CountTrailingZerosL
    false,  // CountTrailingZerosV
    true ,  // CreateEx
    true ,  // DecodeN
    true ,  // DecodeNKlass
    true ,  // DivD
    true ,  // DivF
    true ,  // DivI
    true ,  // DivL
    false,  // UDivI
    false,  // UDivL
    false,  // DivMod
    false,  // DivModI
    false,  // DivModL
    false,  // UDivModI
    false,  // UDivModL
    true ,  // EncodeISOArray
    true ,  // EncodeP
    true ,  // EncodePKlass
    true ,  // FastLock
    true ,  // FastUnlock
    true ,  // FmaD
    true ,  // FmaF
    true ,  // Goto
    true ,  // Halt
    true ,  // CountPositives
    true ,  // If
    false,  // RangeCheck
    false,  // IfFalse
    false,  // IfTrue
    false,  // Initialize
    false,  // JProj
    false,  // Jump
    false,  // JumpProj
    true ,  // LShiftI
    true ,  // LShiftL
    true ,  // LoadB
    true ,  // LoadUB
    true ,  // LoadUS
    true ,  // LoadD
    false,  // LoadD_unaligned
    true ,  // LoadF
    true ,  // LoadI
    true ,  // LoadKlass
    true ,  // LoadNKlass
    true ,  // LoadL
    false,  // LoadL_unaligned
    true ,  // LoadP
    true ,  // LoadN
    true ,  // LoadRange
    true ,  // LoadS
    false,  // Lock
    false,  // Loop
    false,  // LoopLimit
    false,  // Mach
    false,  // MachNullCheck
    false,  // MachProj
    false,  // MulAddS2I
    true ,  // MaxI
    false,  // MaxL
    true ,  // MaxD
    true ,  // MaxF
    true ,  // MemBarAcquire
    true ,  // LoadFence
    true ,  // MemBarAcquireLock
    false,  // MemBarCPUOrder
    true ,  // MemBarRelease
    true ,  // StoreFence
    true ,  // StoreStoreFence
    true ,  // MemBarReleaseLock
    true ,  // MemBarVolatile
    true ,  // MemBarStoreStore
    false,  // MergeMem
    true ,  // MinI
    false,  // MinL
    true ,  // MinF
    true ,  // MinD
    false,  // ModD
    false,  // ModF
    true ,  // ModI
    true ,  // ModL
    false,  // UModI
    false,  // UModL
    true ,  // MoveI2F
    true ,  // MoveF2I
    true ,  // MoveL2D
    true ,  // MoveD2L
    true ,  // IsInfiniteF
    true ,  // IsFiniteF
    true ,  // IsInfiniteD
    true ,  // IsFiniteD
    true ,  // MulD
    true ,  // MulF
    true ,  // MulHiL
    false,  // UMulHiL
    true ,  // MulI
    true ,  // MulL
    false,  // Multi
    false,  // NegI
    false,  // NegL
    true ,  // NegD
    true ,  // NegF
    false,  // NeverBranch
    false,  // OnSpinWait
    false,  // Opaque1
    false,  // OpaqueLoopInit
    false,  // OpaqueLoopStride
    false,  // Opaque2
    false,  // Opaque3
    false,  // Opaque4
    false,  // ProfileBoolean
    true ,  // OrI
    true ,  // OrL
    false,  // OverflowAddI
    false,  // OverflowSubI
    false,  // OverflowMulI
    false,  // OverflowAddL
    false,  // OverflowSubL
    false,  // OverflowMulL
    false,  // PCTable
    false,  // Parm
    true ,  // PartialSubtypeCheck
    false,  // SubTypeCheck
    false,  // Phi
    true ,  // PopCountI
    true ,  // PopCountL
    false,  // PopCountVI
    false,  // PopCountVL
    false,  // PopulateIndex
    false,  // PrefetchAllocation
    false,  // Proj
    true ,  // RShiftI
    true ,  // RShiftL
    false,  // Region
    true ,  // Rethrow
    true ,  // Return
    false,  // ReverseI
    false,  // ReverseL
    false,  // ReverseV
    false,  // Root
    false,  // RoundDouble
    false,  // RoundDoubleMode
    true ,  // RoundDoubleModeV
    false,  // RoundFloat
    true ,  // RotateLeft
    false,  // RotateLeftV
    true ,  // RotateRight
    false,  // RotateRightV
    true ,  // SafePoint
    false,  // SafePointScalarObject
    true ,  // ShenandoahCompareAndExchangeP
    true ,  // ShenandoahCompareAndExchangeN
    true ,  // ShenandoahCompareAndSwapN
    true ,  // ShenandoahCompareAndSwapP
    true ,  // ShenandoahWeakCompareAndSwapN
    true ,  // ShenandoahWeakCompareAndSwapP
    false,  // ShenandoahIUBarrier
    false,  // ShenandoahLoadReferenceBarrier
    false,  // SCMemProj
    false,  // CopySignD
    false,  // CopySignF
    false,  // SignumD
    false,  // SignumF
    false,  // SignumVF
    false,  // SignumVD
    true ,  // SqrtD
    false,  // SqrtF
    false,  // RoundF
    false,  // RoundD
    false,  // Start
    false,  // StartOSR
    true ,  // StoreB
    true ,  // StoreC
    true ,  // StoreCM
    true ,  // StoreD
    true ,  // StoreF
    true ,  // StoreI
    true ,  // StoreL
    true ,  // StoreP
    true ,  // StoreN
    true ,  // StoreNKlass
    true ,  // StrComp
    true ,  // StrCompressedCopy
    true ,  // StrEquals
    true ,  // StrIndexOf
    true ,  // StrIndexOfChar
    true ,  // StrInflatedCopy
    true ,  // SubD
    true ,  // SubF
    true ,  // SubI
    true ,  // SubL
    true ,  // TailCall
    true ,  // TailJump
    false,  // MacroLogicV
    true ,  // ThreadLocal
    false,  // Unlock
    false,  // URShiftB
    false,  // URShiftS
    true ,  // URShiftI
    true ,  // URShiftL
    true ,  // XorI
    true ,  // XorL
    false,  // Vector
    true ,  // AddVB
    true ,  // AddVS
    true ,  // AddVI
    true ,  // AddReductionVI
    true ,  // AddVL
    true ,  // AddReductionVL
    true ,  // AddVF
    true ,  // AddReductionVF
    true ,  // AddVD
    true ,  // AddReductionVD
    true ,  // SubVB
    true ,  // SubVS
    true ,  // SubVI
    true ,  // SubVL
    true ,  // SubVF
    true ,  // SubVD
    true ,  // MulVB
    true ,  // MulVS
    true ,  // MulVI
    false,  // MulReductionVI
    true ,  // MulVL
    false,  // MulReductionVL
    true ,  // MulVF
    false,  // MulReductionVF
    true ,  // MulVD
    false,  // MulReductionVD
    false,  // MulAddVS2VI
    true ,  // FmaVD
    true ,  // FmaVF
    true ,  // DivVF
    true ,  // DivVD
    true ,  // AbsVB
    true ,  // AbsVS
    true ,  // AbsVI
    true ,  // AbsVL
    true ,  // AbsVF
    true ,  // AbsVD
    true ,  // NegVI
    true ,  // NegVL
    true ,  // NegVF
    true ,  // NegVD
    true ,  // SqrtVD
    true ,  // SqrtVF
    true ,  // LShiftCntV
    true ,  // RShiftCntV
    true ,  // LShiftVB
    true ,  // LShiftVS
    true ,  // LShiftVI
    true ,  // LShiftVL
    true ,  // RShiftVB
    true ,  // RShiftVS
    true ,  // RShiftVI
    true ,  // RShiftVL
    true ,  // URShiftVB
    true ,  // URShiftVS
    true ,  // URShiftVI
    true ,  // URShiftVL
    true ,  // AndV
    true ,  // AndReductionV
    true ,  // OrV
    true ,  // OrReductionV
    true ,  // XorV
    true ,  // XorReductionV
    true ,  // MinV
    true ,  // MaxV
    true ,  // MinReductionV
    true ,  // MaxReductionV
    false,  // CompressV
    false,  // CompressM
    false,  // ExpandV
    true ,  // LoadVector
    false,  // LoadVectorGather
    false,  // LoadVectorGatherMasked
    true ,  // StoreVector
    false,  // StoreVectorScatter
    false,  // StoreVectorScatterMasked
    false,  // LoadVectorMasked
    false,  // StoreVectorMasked
    false,  // VectorCmpMasked
    false,  // VectorMaskGen
    false,  // VectorMaskOp
    false,  // VectorMaskTrueCount
    false,  // VectorMaskFirstTrue
    false,  // VectorMaskLastTrue
    false,  // VectorMaskToLong
    false,  // VectorLongToMask
    false,  // Pack
    false,  // PackB
    false,  // PackS
    false,  // PackI
    false,  // PackL
    false,  // PackF
    false,  // PackD
    false,  // Pack2L
    false,  // Pack2D
    true ,  // ReplicateB
    true ,  // ReplicateS
    true ,  // ReplicateI
    true ,  // ReplicateL
    true ,  // ReplicateF
    true ,  // ReplicateD
    false,  // RoundVF
    false,  // RoundVD
    false,  // Extract
    false,  // ExtractB
    false,  // ExtractUB
    false,  // ExtractC
    false,  // ExtractS
    false,  // ExtractI
    false,  // ExtractL
    false,  // ExtractF
    false,  // ExtractD
    false,  // Digit
    false,  // LowerCase
    false,  // UpperCase
    false,  // Whitespace
    false,  // VectorBox
    false,  // VectorBoxAllocate
    false,  // VectorUnbox
    false,  // VectorMaskWrapper
    false,  // VectorMaskCmp
    false,  // VectorMaskCast
    false,  // VectorTest
    false,  // VectorBlend
    false,  // VectorRearrange
    false,  // VectorLoadMask
    false,  // VectorLoadShuffle
    false,  // VectorLoadConst
    false,  // VectorStoreMask
    false,  // VectorReinterpret
    false,  // VectorCast
    false,  // VectorCastB2X
    false,  // VectorCastS2X
    false,  // VectorCastI2X
    false,  // VectorCastL2X
    false,  // VectorCastF2X
    false,  // VectorCastD2X
    false,  // VectorUCastB2X
    false,  // VectorUCastS2X
    false,  // VectorUCastI2X
    false,  // VectorInsert
    false,  // MaskAll
    false,  // AndVMask
    false,  // OrVMask
    false   // XorVMask
};


int Compile::sync_stack_slots() const { return 1 * VMRegImpl::slots_per_word; }

uint Matcher::stack_alignment_in_bytes() { return StackAlignmentInBytes; }

OptoReg::Name Matcher::return_addr() const { return OptoReg::stack2reg(- 2 +
              align_up((Compile::current()->in_preserve_stack_slots() +
                        Compile::current()->fixed_slots()),
                       stack_alignment_in_slots())); }

uint Compile::varargs_C_out_slots_killed() const { return frame::arg_reg_save_area_bytes / BytesPerInt; }

OptoRegPair Matcher::return_value(uint ideal_reg) {

#line 2717 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    assert(ideal_reg >= Op_RegI && ideal_reg <= Op_RegL,
           "only return normal values");

    static const int lo[Op_RegL + 1] = { // enum name
      0,                                 // Op_Node
      0,                                 // Op_Set
      R10_num,                           // Op_RegN
      R10_num,                           // Op_RegI
      R10_num,                           // Op_RegP
      F10_num,                           // Op_RegF
      F10_num,                           // Op_RegD
      R10_num                            // Op_RegL
    };

    static const int hi[Op_RegL + 1] = { // enum name
      0,                                 // Op_Node
      0,                                 // Op_Set
      OptoReg::Bad,                      // Op_RegN
      OptoReg::Bad,                      // Op_RegI
      R10_H_num,                         // Op_RegP
      OptoReg::Bad,                      // Op_RegF
      F10_H_num,                         // Op_RegD
      R10_H_num                          // Op_RegL
    };

    return OptoRegPair(hi[ideal_reg], lo[ideal_reg]);
  
#line 21074 "ad_riscv.cpp"

}

OptoRegPair Matcher::c_return_value(uint ideal_reg) {

#line 2717 "/home/zifeihan/jdk/src/hotspot/cpu/riscv/riscv.ad"

    assert(ideal_reg >= Op_RegI && ideal_reg <= Op_RegL,
           "only return normal values");

    static const int lo[Op_RegL + 1] = { // enum name
      0,                                 // Op_Node
      0,                                 // Op_Set
      R10_num,                           // Op_RegN
      R10_num,                           // Op_RegI
      R10_num,                           // Op_RegP
      F10_num,                           // Op_RegF
      F10_num,                           // Op_RegD
      R10_num                            // Op_RegL
    };

    static const int hi[Op_RegL + 1] = { // enum name
      0,                                 // Op_Node
      0,                                 // Op_Set
      OptoReg::Bad,                      // Op_RegN
      OptoReg::Bad,                      // Op_RegI
      R10_H_num,                         // Op_RegP
      OptoReg::Bad,                      // Op_RegF
      F10_H_num,                         // Op_RegD
      R10_H_num                          // Op_RegL
    };

    return OptoRegPair(hi[ideal_reg], lo[ideal_reg]);
  
#line 21109 "ad_riscv.cpp"

}

OptoReg::Name Matcher::inline_cache_reg() { return OptoReg::Name(R31_num); }

int Matcher::inline_cache_reg_encode() { return _regEncode[inline_cache_reg()]; }

OptoReg::Name Matcher::interpreter_frame_pointer_reg() { return OptoReg::Name(R8_num); }

OptoReg::Name Matcher::c_frame_pointer() const { return OptoReg::Name(R2_num); }

// Number of callee-save + always-save registers
int  Matcher::number_of_saved_registers() {
  return 0;
};

bool Compile::needs_deep_clone_jvms() { return false; }

// Check consistency of C++ compilation with ADLC options:
// Check adlc -DLINUX=1
#ifndef LINUX
#  error "LINUX must be defined"
#endif // LINUX
// Check adlc -D_GNU_SOURCE=1
#ifndef _GNU_SOURCE
#  error "_GNU_SOURCE must be defined"
#endif // _GNU_SOURCE
// Check adlc -DRISCV64=1
#ifndef RISCV64
#  error "RISCV64 must be defined"
#endif // RISCV64
// Check adlc -D_LP64=1
#ifndef _LP64
#  error "_LP64 must be defined"
#endif // _LP64
