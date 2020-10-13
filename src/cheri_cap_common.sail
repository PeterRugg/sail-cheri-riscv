/*========================================================================*/
/*                                                                        */
/*  Copyright (c) 2015-2019 Robert M. Norton                              */
/*  Copyright (c) 2015-2019 Kathyrn Gray                                  */
/*  All rights reserved.                                                  */
/*                                                                        */
/*  This software was developed by the University of Cambridge Computer   */
/*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  */
/*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   */
/*                                                                        */
/*  Redistribution and use in source and binary forms, with or without    */
/*  modification, are permitted provided that the following conditions    */
/*  are met:                                                              */
/*  1. Redistributions of source code must retain the above copyright     */
/*     notice, this list of conditions and the following disclaimer.      */
/*  2. Redistributions in binary form must reproduce the above copyright  */
/*     notice, this list of conditions and the following disclaimer in    */
/*     the documentation and/or other materials provided with the         */
/*     distribution.                                                      */
/*                                                                        */
/*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    */
/*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     */
/*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       */
/*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   */
/*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          */
/*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      */
/*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      */
/*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   */
/*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    */
/*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    */
/*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    */
/*  SUCH DAMAGE.                                                          */
/*========================================================================*/


let max_otype = MAX(otype_width) - reserved_otypes
type CapAddrBits = bits(cap_addr_width)
type CapLenBits  = bits(cap_len_width)

function getCapHardPerms(cap) : Capability -> bits(12) =
   (bool_to_bits(cap.permit_set_CID)
  @ bool_to_bits(cap.access_system_regs)
  @ bool_to_bits(cap.permit_unseal)
  @ bool_to_bits(cap.permit_cinvoke)
  @ bool_to_bits(cap.permit_seal)
  @ bool_to_bits(cap.permit_store_local_cap)
  @ bool_to_bits(cap.permit_store_cap)
  @ bool_to_bits(cap.permit_load_cap)
  @ bool_to_bits(cap.permit_store)
  @ bool_to_bits(cap.permit_load)
  @ bool_to_bits(cap.permit_execute)
  @ bool_to_bits(cap.global))

/* Convert from capabilty struct to bits (no tag) */
function capToBits(cap) : Capability -> CapBits = {
  t_hi : bits(mantissa_width - 5) = cap.T[mantissa_width - 3..3];
  t_lo : bits(3)  = cap.T[2..0];
  b_hi : bits(mantissa_width - 3) = cap.B[mantissa_width - 1..3];
  b_lo : bits(3)  = cap.B[2..0];
  if cap.internal_e then {
    t_lo = cap.E[5..3];
    b_lo = cap.E[2..0];
  };
  return (cap.uperms
    @ getCapHardPerms(cap)
    @ cap.reserved
    @ bool_to_bits(cap.flag_cap_mode)
    @ cap.otype
    @ bool_to_bits(cap.internal_e)
    @ t_hi
    @ t_lo
    @ b_hi
    @ b_lo
    @ cap.address
  );
}

/* When saving/restoring capabilities xor them with bits of null_cap --
 * this ensures that canonical null_cap is always all-zeros in memory
 * even though it may have bits set logically (e.g. length or exponent
 */

let null_cap_bits : CapBits = capToBits(null_cap)

function capToMemBits(cap) : Capability -> CapBits =
  capToBits(cap) ^ null_cap_bits

function memBitsToCapability(tag, b) : (bool, CapBits) -> Capability =
  capBitsToCapability(tag, b ^ null_cap_bits)

function getCapBoundsBitsUncorrected(c) : Capability -> (CapLenBits, CapLenBits) =
  let E = min(maxE, unsigned(c.E)) in
  let a : CapAddrBits = c.address in
  let a_ext : CapLenBits = EXTZ(a) in
  let a_top = truncateLSB(a_ext, cap_len_width - E - mantissa_width) in
  let base : CapLenBits = a_top @ c.B @ zeros(E) in
  let top  : CapLenBits = a_top @ c.T @ zeros(E) in
    (base, top)

function getCapLegalised(c) : Capability -> Capability =
  let (base, top) = getCapBoundsBitsUncorrected(c) in
  /* Check that base is within the address space */
  if unsigned(c.E) <= maxE
   & (base <_u (to_bits(cap_len_width, 1) << cap_addr_width)) then
    c
  else
    /* Legalise the capability by zeroing the ie bit, implicitly setting E to 0. TODO avoid 90 magic number */
    capBitsToCapability(false, capToBits(c) & ~(to_bits(128, 1) << 90))

function getCapBoundsBits(c) : Capability -> (CapAddrBits, CapLenBits) =
  let c_legal = getCapLegalised(c) in
  let E = unsigned(c_legal.E) in
  let a : CapAddrBits = c_legal.address in
  let (base, top) = getCapBoundsBitsUncorrected(c_legal) in
  /* Extract bits we need to make the top correction and calculate representable limit */
  let a3 = truncate(a >> (E + mantissa_width - 3), 3) in
  let B3 = truncateLSB(c_legal.B, 3) in
  let T3 = truncateLSB(c_legal.T, 3) in
  let R3 = B3 - 0b001 in /* wraps */
  /* Do address, base and top lie in the R aligned region above the one containing R? */
  let aHi = if a3 <_u R3 then 1 else 0 in
  let bHi = if B3 <_u R3 then 1 else 0 in
  let tHi = if T3 <_u R3 then 1 else 0 in
  /* Compute region corrections for top and base relative to a */
  let correction_base = bHi - aHi in
  let correction_top  = tHi - aHi in {
    base_corrected : CapLenBits = base + (to_bits(cap_len_width, correction_base) << (mantissa_width + E));
    top_corrected : CapLenBits = top + (to_bits(cap_len_width, correction_top) << (mantissa_width + E));
    /* Interpret the top relative to the address space of the base.
       This corrects for errors that happen when the representable space wraps the address space. */
    top_corrected[cap_len_width - 1 .. cap_addr_width] = top_corrected[cap_len_width - 1 .. cap_addr_width] - base_corrected[cap_len_width - 1 .. cap_addr_width];
    (truncate(base_corrected, cap_addr_width), top_corrected)
  }

function getCapBounds(cap) : Capability -> (CapAddrInt, CapLen) =
  let (base, top) = getCapBoundsBits(cap) in
  (unsigned(base), unsigned(top))

/* An 'ideal' version of setCapBounds as described in paper. */
function setCapBounds(cap, base, top) : (Capability, CapAddrBits, CapLenBits) -> (bool, Capability) = {
  /* {cap with base=base; length=(bits(64)) length; offset=0} */
  let ext_base : CapLenBits = EXTZ(base);
  let length = top - ext_base;
  /* Find an exponent that will put the most significant bit of length
   * second from the top as assumed during decoding. We ignore the bottom
   * MW bits because those are handled by the ie = 0 format.
   */
  let e = maxE - count_leading_zeros(length[cap_addr_width..mantissa_width - 1]);
  // Use use internal exponent if e is non-zero or if e is zero but
  // but the implied bit of length is not zero (denormal vs. normal case)
  let ie = (e != 0) | length[mantissa_width - 2] == bitone;

  /* The non-ie e == 0 case is easy. It is exact so just extract relevant bits. */
  Bbits = truncate(base, mantissa_width);
  Tbits = truncate(top, mantissa_width);
  lostSignificantTop : bool = false;
  lostSignificantBase : bool = false;
  incE : bool = false;

  if ie then {
    /* the internal exponent case is trickier */

    /* Extract B and T bits (we lose 3 bits of each to store the exponent) */
    B_ie = truncate(base >> (e + 3), mantissa_width - 3);
    T_ie = truncate(top >> (e + 3), mantissa_width - 3);

    /* Find out whether we have lost significant bits of base and top using a
     * mask of bits that we will lose (including 3 extra for exp).
     */
    maskLo : CapLenBits = EXTZ(ones(e+3));
    lostSignificantBase = unsigned(ext_base & maskLo) != 0;
    lostSignificantTop  = unsigned(top & maskLo) != 0;

    if lostSignificantTop then {
      /* we must increment T to make sure it is still above top even with lost bits.
         It might wrap around but if that makes B<T then decoding will compensate. */
      T_ie = T_ie + 1;
    };

    /* Has the length overflowed? We chose e so that the top two bits of len would be 0b01,
       but either because of incrementing T or losing bits of base it might have grown. */
    len_ie = T_ie - B_ie;
    if len_ie[mantissa_width - 4] == bitone then {
      /* length overflow -- increment E by one and then recalculate
         T, B etc accordingly */
      incE = true;

      lostSignificantBase = lostSignificantBase | B_ie[0] == bitone;
      lostSignificantTop  = lostSignificantTop | T_ie[0] == bitone;

      B_ie = truncate(base >> (e + 4), mantissa_width - 3);
      let incT : range(0,1) = if lostSignificantTop then 1 else 0;
      T_ie = truncate(top >> (e + 4), mantissa_width - 3) + incT;
    };

    Bbits = B_ie @ 0b000;
    Tbits = T_ie @ 0b000;
  };
  let newCap = {cap with address=base, E=to_bits(6, if incE then e + 1 else e), B=Bbits, T=Tbits, internal_e=ie};
  let exact = not(lostSignificantBase | lostSignificantTop);
  (exact, newCap)
}

function getCapPerms(cap) : Capability -> bits(31) =
    let perms : bits(15) = EXTZ(getCapHardPerms(cap)) in
    EXTZ(cap.uperms @ perms)

function setCapPerms(cap, perms) : (Capability, bits(31)) -> Capability =
    { cap with
      uperms                 = truncate(perms[30..15], uperms_width),
      /* 14..12 reserved -- ignore */
      permit_set_CID         = bit_to_bool(perms[11]),
      access_system_regs     = bit_to_bool(perms[10]),
      permit_unseal          = bit_to_bool(perms[9]),
      permit_cinvoke         = bit_to_bool(perms[8]),
      permit_seal            = bit_to_bool(perms[7]),
      permit_store_local_cap = bit_to_bool(perms[6]),
      permit_store_cap       = bit_to_bool(perms[5]),
      permit_load_cap        = bit_to_bool(perms[4]),
      permit_store           = bit_to_bool(perms[3]),
      permit_load            = bit_to_bool(perms[2]),
      permit_execute         = bit_to_bool(perms[1]),
      global                 = bit_to_bool(perms[0])
      }

/*!
Gets the architecture specific capability flags for given capability.
 */
val getCapFlags : Capability -> CFlags
function getCapFlags(cap) = bool_to_bits(cap.flag_cap_mode)

/*!
THIS`(cap, flags)` sets the architecture specific capability flags on `cap` to `flags` and returns the result as new capability.
 */
val setCapFlags : (Capability, CFlags) -> Capability
function setCapFlags(cap, flags) = {cap with flag_cap_mode = bit_to_bool(flags[0])}

/*! Tests whether the capability has a reserved otype (larger than max_otype).
    Note that this includes both sealed (e.g. sentry) and unsealed (all ones)
    otypes. */
val hasReservedOType : Capability -> bool
function hasReservedOType(cap) = unsigned(cap.otype) > max_otype

function sealCap(cap, otyp) : (Capability, bits(otype_width)) -> Capability =
    {cap with sealed=true, otype=otyp}

function unsealCap(cap) : Capability -> Capability =
    {cap with sealed=false, otype=to_bits(otype_width, otype_unsealed)}

function getCapBaseBits(c) : Capability -> CapAddrBits =
    let (base, _) = getCapBoundsBits(c) in
    base

function getCapBase(c) : Capability -> CapAddrInt =
    unsigned(getCapBaseBits(c))

function getCapTopBits(c) : Capability -> CapLenBits =
    let (_, top) = getCapBoundsBits(c) in
    top

function getCapTop (c) : Capability -> CapLen =
    unsigned(getCapTopBits(c))

function getCapOffsetBits(c) : Capability -> CapAddrBits =
    let base : CapAddrBits = getCapBaseBits(c) in
    c.address - base

function getCapOffset(c) : Capability -> CapAddrInt =
    unsigned(getCapOffsetBits(c))

function getCapLength(c) : Capability -> CapLen =
    let ('base, 'top) = getCapBounds(c) in {
        assert(top >= base);
        top - base
    }

val inCapBounds  : (Capability, CapAddrBits, CapLen) -> bool
function inCapBounds (cap, addr, size) = {
  let (base, top) = getCapBounds(cap);
  let a = unsigned(addr);
  (a >= base) & ((a + size) <= top)
}

function getCapCursor(cap) : Capability -> CapAddrInt = unsigned(cap.address)

function int_to_cap (offset) : CapAddrBits -> Capability =
    {null_cap with address = offset}

function invalidateCap(cap) : Capability -> Capability = {cap with tag=false}

function capBoundsEqual (c1, c2) : (Capability, Capability) -> bool =
    let (base1, top1) = getCapBounds(c1) in
    let (base2, top2) = getCapBounds(c2) in
    (base1 == base2) & (top1 == top2)

val setCapAddr : (Capability, CapAddrBits) -> (bool, Capability)
function setCapAddr(c, addr) =
    let newCap = { c with address = addr } in
    let representable = capBoundsEqual(c, newCap) in
    (representable, newCap)

function setCapAddrOrNull (cap, addr) : (Capability, CapAddrBits) -> Capability =
  let (representable, newCap) = setCapAddr(cap, addr) in
  if representable & not(cap.sealed) then newCap else invalidateCap(newCap)

infix 1 >>_s
overload operator >> = {sail_shiftright}
overload operator << = {sail_shiftleft}
overload operator >>_s = {sail_arith_shiftright}

function fastRepCheck(c, i) : (Capability, CapAddrBits) -> bool=
    let c_legal = getCapLegalised(c) in
    let E = unsigned(c_legal.E) in
    if (E >= maxE - 2) then
        true /* in this case representable region is whole address space */
    else
        let i_top    = signed(i >>_s (E + mantissa_width)) in
        let i_mid    = truncate(i >> E, mantissa_width)in
        let a_mid    = truncate(c_legal.address >> E, mantissa_width) in
        let B3 = truncateLSB(c_legal.B, 3) in
        let R3 = B3 - 0b001 in
        let R  = R3 @ zeros(mantissa_width - 3) in
        let diff  = R - a_mid in
        let diff1 = diff - 1 in
        /* i_top determines 1. whether the increment is inRange
           i.e. less than the size of the representable region
           (2**(E+MW)) and 2. whether it is positive or negative. To
           satisfy 1. all top bits must be the same so we are
           interested in the cases i_top is 0 or -1 */
        if (i_top == 0) then
          i_mid <_u diff1
        else if (i_top == -1) then
          (i_mid >=_u diff) & (R != a_mid)
        else
          false

function setCapOffset(c, offset) : (Capability, CapAddrBits) -> (bool, Capability) =
    let base = getCapBaseBits(c) in
    let newAddress = base + offset in
    let newCap     = { c with address = newAddress } in
    /* let representable = capBoundsEqual(c, newCap) in */
    let representable = fastRepCheck(c, (newAddress - c.address)) in
    (representable, newCap)

function setCapOffsetOrNull (cap, offset) : (Capability, CapAddrBits) -> Capability =
    let (representable, newCap) = setCapOffset(cap, offset) in
    if representable & not(cap.sealed) then newCap else invalidateCap(newCap)

function incCapOffset(c, delta) : (Capability, CapAddrBits) -> (bool, Capability) =
    let newAddress : CapAddrBits = c.address + delta in
    let newCap     = { c with address = newAddress } in
    /* let representable = capBoundsEqual(c, newCap) in */
    let representable = fastRepCheck(c, delta) in
    (representable, newCap)


val capToString : (Capability) -> string effect {escape}
function capToString (cap) = {
  let len = getCapLength(cap);
  let len_str = BitStr(to_bits(cap_len_width + 3, len));
  /* Print architectural type which is -1 for unsealed caps */
  let otype64 : CapAddrBits = if hasReservedOType(cap) then EXTS(cap.otype) else EXTZ(cap.otype);
  concat_str(" t:",
  concat_str(if cap.tag then "1" else "0",
  concat_str(" s:",
  concat_str(if cap.sealed then "1" else "0",
  concat_str(" perms:",
  concat_str(BitStr(0b0 @ getCapPerms(cap)),
  concat_str(" type:",
  concat_str(BitStr(otype64),
  concat_str(" offset:",
  concat_str(BitStr(getCapOffsetBits(cap)),
  concat_str(" base:",
  concat_str(BitStr(getCapBaseBits(cap)),
  concat_str(" length:", len_str)))))))))))))
}
function getRepresentableAlignmentMask(len) : xlenbits -> xlenbits = {
  let (exact, c) = setCapBounds(default_cap, to_bits(sizeof(xlen), 0), EXTZ(len));
  let e = min(unsigned(c.E), maxE);
  let e' = if c.internal_e then e + internal_exponent_take_bits else 0;
  ones(sizeof(xlen)-e') @ zeros(e')
}

function getRepresentableLength(len) : xlenbits -> xlenbits = {
  let m = getRepresentableAlignmentMask(len);
  (len + ~(m)) & m
}
