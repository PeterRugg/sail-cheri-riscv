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
type cap_size : Int = 8
let cap_size = sizeof(cap_size)
type log2_cap_size : Int = 3
let log2_cap_size = sizeof(log2_cap_size)
type CapBits = bits(8 * cap_size)
/* width of otype field in bits */
type otype_width : Int = 4
let otype_width = sizeof(otype_width)
type uperms_width : Int = 0
let uperms_width = sizeof(uperms_width)
type cap_addr_width : Int = xlen
let  cap_addr_width = sizeof(cap_addr_width)
type mantissa_width : Int = 8
let mantissa_width = sizeof(mantissa_width)
type exp_width : Int = 6
let exp_width = sizeof(exp_width)
type cap_len_width : Int = cap_addr_width + 2
let  cap_len_width  = sizeof(cap_len_width)
type reserved_width : Int = 0
let  reserved_width = sizeof(reserved_width)

/* Reset E and T calculated to make top 2**32. */
let  maxE = 26
type internal_exponent_take_bits : Int = 3
let  internal_exponent_take_bits = sizeof(internal_exponent_take_bits)
let  resetE = to_bits(exp_width, maxE)
let  resetT = 0b01000000 /* bit 6 set */

/* Capability format completely compressed. Tag is out of band */
struct EncCapability = {
  perms      : bits(uperms_width + 12) ,
  otype      : bits(otype_width) ,
  reserved   : bits(reserved_width) ,
  flags      : bits(1) ,
  internal_e : bit ,
  T          : bits(mantissa_width - 2) ,
  B          : bits(mantissa_width) ,
  address    : bits(cap_addr_width)
}

function capBitsToEncCapability(c) : CapBits -> EncCapability = struct {
  perms      = c[63..52],
  reserved   = [],
  flags      = c[51..51],
  otype      = c[50..47],
  internal_e = c[46],
  T          = c[45..40],
  B          = c[39..32],
  address    = c[31..0]
}

function EncCapToBits(cap) : EncCapability -> CapBits =
  cap.perms @
  cap.reserved @
  cap.flags @
  cap.otype @
  [cap.internal_e] @
  cap.T @
  cap.B @
  cap.address
