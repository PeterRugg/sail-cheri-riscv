/*========================================================================*/
/*                                                                        */
/*  Copyright (c) 2015-2017 Robert M. Norton                              */
/*  Copyright (c) 2015-2017 Kathyrn Gray                                  */
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

/* width of capability in bytes (excluding tag) */
type cap_size : Int = 16
let cap_size = sizeof(cap_size)
type log2_cap_size : Int = 4
let log2_cap_size = sizeof(log2_cap_size)
type CapBits = bits(8 * cap_size)
/* width of otype field in bits */
type cap_otype_width : Int = 18
let cap_otype_width = sizeof(cap_otype_width)
type cap_hperms_width : Int = 12
let cap_hperms_width = sizeof(cap_hperms_width)
type cap_uperms_width : Int = 4
let cap_uperms_width = sizeof(cap_uperms_width)
type cap_addr_width : Int = xlen
let  cap_addr_width = sizeof(cap_addr_width)
type cap_len_width : Int = cap_addr_width + 1
let  cap_len_width  = sizeof(cap_len_width)
type cap_mantissa_width : Int = 14
let  cap_mantissa_width = sizeof(cap_mantissa_width)

let MAX_ADDR = MAX(cap_addr_width)
type CapAddrInt = range(0, (2 ^ 64) - 1) /* XXX should be cap_addr_width */
type CapLen = range(0, 2 ^ 65) /* XXX sail can't handle if this is expressed as cap_len_width */

/*!
 * A partially decompressed version of a capability, populated by
 * capBitsToCapability. E is not present in all formats.
 */
struct Capability = {
  tag                    : bool    ,
  uperms                 : bits(cap_uperms_width) ,
  permit_set_CID         : bool    ,
  access_system_regs     : bool    ,
  permit_unseal          : bool    ,
  permit_cinvoke         : bool    ,
  permit_seal            : bool    ,
  permit_store_local_cap : bool    ,
  permit_store_cap       : bool    ,
  permit_load_cap        : bool    ,
  permit_store           : bool    ,
  permit_load            : bool    ,
  permit_execute         : bool    ,
  global                 : bool    ,
  reserved               : bits(2) ,
  flag_cap_mode          : bool    ,
  internal_e             : bool    ,
  E                      : bits(6) ,
  B                      : bits(cap_mantissa_width),
  T                      : bits(cap_mantissa_width),
  otype                  : bits(cap_otype_width),
  address                : bits(cap_addr_width)
}

/* Reset E and T calculated to make top 2**64. */
let maxE = 52
let internal_exponent_take_bits = 3
let resetE = to_bits(6, maxE)
let resetT = 0b01 @ 0x000 /* bit 12 set */

let null_cap : Capability = struct {
  tag                    = false,
  uperms                 = zeros(),
  permit_set_CID         = false,
  access_system_regs     = false,
  permit_unseal          = false,
  permit_cinvoke         = false,
  permit_seal            = false,
  permit_store_local_cap = false,
  permit_store_cap       = false,
  permit_load_cap        = false,
  permit_store           = false,
  permit_load            = false,
  permit_execute         = false,
  global                 = false,
  reserved               = zeros(),
  flag_cap_mode          = false,
  internal_e             = true,
  E                      = resetE,
  B                      = zeros(),
  T                      = resetT,
  otype                  = to_bits(cap_otype_width, otype_unsealed),
  address                = zeros()
}

let default_cap : Capability = struct {
  tag                    = true,
  uperms                 = ones(),
  permit_set_CID         = true,
  access_system_regs     = true,
  permit_unseal          = true,
  permit_cinvoke         = true,
  permit_seal            = true,
  permit_store_local_cap = true,
  permit_store_cap       = true,
  permit_load_cap        = true,
  permit_store           = true,
  permit_load            = true,
  permit_execute         = true,
  global                 = true,
  reserved               = zeros(),
  flag_cap_mode          = false,
  internal_e             = true,
  E                      = resetE,
  B                      = zeros(),
  T                      = resetT,
  otype                  = to_bits(cap_otype_width, otype_unsealed),
  address                = zeros()
}

/* Convert from capabilty bits (128 bits with tag) to a more convenient struct. */
function capBitsToCapability(t, c) : (bool, CapBits) -> Capability = {
  internal_exponent : bool = bit_to_bool(c[90]);
  otype : bits(18) = c[108..91];
  E : bits(6)  = zeros();
  Bs : bits(14) = zeros();
  T : bits(12) = zeros();
  lenMSBs : bits(2) = zeros();
  if internal_exponent then {
    /* Exponent stored instead of T[2..0] and B[2..0] */
    E = c[80..78] @ c [66..64];
    /* Exponent chosen so that length MSBs is 01 */
    lenMSBs = 0b01;
    T = c[89..81] @ 0b000;
    Bs = c[77..67] @ 0b000;
  } else {
    /* Exponent zero */
    lenMSBs = 0b00;
    T = c[89..78];
    Bs = c[77..64];
  };
  /* Reconstruct top two bits of T given T = B + len and:
   * 1) the top two bits of B
   * 2) most significant two bits of length derived from format above
   * 3) carry out of B[20..0] + len[20..0] that is implied if T[20..0] < B[20..0]
   */
  carry_out = if T <_u Bs[11..0] then 0b01 else 0b00;
  Ttop2 = Bs[13..12] + lenMSBs + carry_out;
  return struct {
    tag                    = t,
    uperms                 = c[127..124],
    permit_set_CID         = bit_to_bool(c[123]),
    access_system_regs     = bit_to_bool(c[122]),
    permit_unseal          = bit_to_bool(c[121]),
    permit_cinvoke         = bit_to_bool(c[120]),
    permit_seal            = bit_to_bool(c[119]),
    permit_store_local_cap = bit_to_bool(c[118]),
    permit_store_cap       = bit_to_bool(c[117]),
    permit_load_cap        = bit_to_bool(c[116]),
    permit_store           = bit_to_bool(c[115]),
    permit_load            = bit_to_bool(c[114]),
    permit_execute         = bit_to_bool(c[113]),
    global                 = bit_to_bool(c[112]),
    reserved               = c[111..110],
    flag_cap_mode          = bit_to_bool(c[109]),
    internal_e             = internal_exponent,
    E                      = E,
    B                      = Bs,
    T                      = Ttop2 @ T,
    otype                  = otype,
    address                = c[63..0]
  }
}
