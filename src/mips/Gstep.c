/* libunwind - a platform-independent unwind library
   Copyright (C) 2008 CodeSourcery

This file is part of libunwind.

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.  */

#include "unwind_i.h"
#include "offsets.h"

static inline int
find_sp_restore(struct cursor *c, unw_word_t pc)
{
  unw_word_t max_check = 1024 * 10;

  for (; max_check-- > 0; pc -= 4) {
    int ret;
    unw_word_t op;
    if ((ret = dwarf_get (&c->dwarf, DWARF_LOC (pc, 0), &op)) < 0)
      return ret;
    /* find move sp, s8 instruction */
    if (op == 0x3a0f021)
      return 1;
    /* find jr $ra */
    if (op == 0x3e00008)
      break;
  }

  return 0;
}

static inline int
mips_heuristic_step (struct cursor *c)
{
  /* FIXME (simon): Setup data types. */
  int ret;
  int maxcheck = 1024 * 10;
  int found = 0;
  int32_t stack_size = 0;
  int32_t stack_size_before_ra = 0;
  int32_t stack_size_after_ra = 0;
  int32_t ra_offset = 0;
  int32_t fp_offset = 0;
  unw_word_t pc;
  int use_fp = 0;
  unw_word_t ra, sp, fp = 0;
  unw_word_t old_ip, old_sp, old_fp;
  dwarf_loc_t ip_loc = DWARF_NULL_LOC;
  dwarf_loc_t fp_loc = DWARF_NULL_LOC;

  static struct {
    uint32_t insn;
    uint32_t mask;
  } frame0sig[] = {
    {0x3c1c0000, 0xffff0000}, /* lui     gp,xxxx */
    {0x279c0000, 0xffff0000}, /* addiu   gp,gp,xxxx */
    {0x039fe021, 0xffffffff}, /* addu    gp,gp,ra */
  };

  const int nframe0sig = sizeof(frame0sig)/sizeof(frame0sig[0]);
  int f0 = nframe0sig - 1;

  old_ip = c->dwarf.ip;
  old_sp = c->dwarf.cfa;
  if ((ret = dwarf_get (&c->dwarf, c->dwarf.loc[UNW_MIPS_R30], &old_fp)) < 0)
    return ret;

  Debug (2, "(ip=0x%016llx, sp=0x%016llx, fp=0x%016llx)\n", old_ip, old_sp, old_fp);

  pc = c->dwarf.use_prev_instr ? c->dwarf.ip - 4 : c->dwarf.ip;

  for (; maxcheck-- > 0 && !found; pc -= 4) {
    unw_word_t op;
    int32_t immediate;
    if ((ret = dwarf_get (&c->dwarf, DWARF_LOC (pc, 0), &op)) < 0)
      return ret;

    /* move ra, zero */
    if (op == 0x0000f821) {
      Debug (2, "'move ra, zero' stop condition at 0x%016llx\n", pc);
      return 0;
    }

    /* check frame0 */
    if ((op & frame0sig[f0].mask) == frame0sig[f0].insn) {
      if (f0 == 0) {
        Debug (2, "'frame0' stop condition at 0x%016llx\n", pc);
        return 0;
      }
      --f0;
    } else
      f0 = nframe0sig - 1;

    /* move s8, sp */
    /* FIXME (simon): Check that we have found fp already! */
    if (op == 0x3a0f021) {
      Debug (2, "sp saved to the s8 at 0x%016llx\n", pc);
      if ((ret = find_sp_restore(c, c->dwarf.ip)) < 0)
        return ret;
      if (ret) {
        Debug (2, "treat s8 as fp register\n");
        use_fp = 1;
        stack_size_after_ra = 0;
      }
    }

    switch (op & 0xffff0000) {
      case 0x27bd0000: /* addiu sp, imm */
        immediate = (((int32_t)op) << 16) >> 16;
        if (immediate < 0) {
          /* It's possible to have more than one stack adjustment
             instructions. Sum up two offsets. The first one is
             stack pointer offset from the beginning of the function.
             The second one is stack pointer offset made after we
             save return address in the stack. */
          stack_size += -immediate;
          Debug (2, "stack adjustment %d at 0x%016llx\n", stack_size, pc);
          if (ra_offset)
            stack_size_before_ra += -immediate;
          else
            stack_size_after_ra += -immediate;
        }
        break;
      case 0xafbf0000: /* sw ra, imm(sp) */
        ra_offset = (((int32_t)op) << 16) >> 16;
        Debug (2, "ra offset %d at 0x%016llx\n", ra_offset, pc);
        break;
      case 0xafbe0000: /* sw s8, imm(sp) */
        fp_offset = (((int32_t)op) << 16) >> 16;
        Debug (2, "fp offset %d at 0x%016llx\n", fp_offset, pc);
        break;
      case 0x3c1c0000: /* lui gp */
        found = 1;
        Debug (2, "'lui gp' upper function boundary at 0x%016llx\n", pc);
        break;
      default:
        break;
    }

    if (op == 0x3e00008) {
      found = 1;
      Debug (2, "'jr ra' upper function boundary at 0x%016llx\n", pc);
    }
  }

  if (found && ra_offset && !stack_size_before_ra) {
    unw_word_t op;
    /* We find 'lui gp' instruction and 'sw ra, imm(sp)' instruction
       but do not find any stack adjustment code. Let's try to check
       one instruction further. */
    Debug (2, "look up stack adjustment before 'lui gp'\n");

    if ((ret = dwarf_get (&c->dwarf, DWARF_LOC (pc, 0), &op)) < 0)
      return ret;

    if ((op & 0xffff0000) == 0x27bd0000) {
      int32_t immediate = (((int32_t)op) << 16) >> 16;
      if (immediate < 0) {
        stack_size += -immediate;
        stack_size_before_ra += -immediate;
        Debug (2, "stack adjustment %d at 0x%016llx\n", stack_size, pc);
      }
    }
  }

  if (!maxcheck) {
    Debug (2, "stop prologue look up at 0x%016llx\n", pc);
    return -UNW_EBADFRAME;
  }

  if (use_fp) {
    if ((ret = dwarf_get (&c->dwarf, c->dwarf.loc[UNW_MIPS_R30], &fp)) < 0)
      return ret;

    if (stack_size)
      sp = fp + stack_size;

    if (ra_offset) {
      ip_loc = DWARF_LOC(fp + ra_offset + stack_size_after_ra, 0);
      if ((ret = dwarf_get (&c->dwarf, ip_loc, &ra)) < 0)
        return ret;
    } else {
      stack_size_after_ra = 0;
      if ((ret = dwarf_get (&c->dwarf, c->dwarf.loc[UNW_MIPS_R31], &ra)) < 0)
        return ret;
    }
    if (fp_offset) {
      /* FIXME (simon): Remove this line. */
      Debug (2, "(fp_offset=%d, ssar=%d, fp=0x%016llx)\n", fp_offset, stack_size_after_ra, fp);
      fp_loc = DWARF_LOC(fp + fp_offset + stack_size_after_ra, 0);
      if ((ret = dwarf_get (&c->dwarf, fp_loc, &fp)) < 0)
        return ret;
    }
  } else {
    sp = c->dwarf.cfa;

    if (ra_offset) {
      ip_loc = DWARF_LOC(sp + ra_offset + stack_size_after_ra, 0);
      if ((ret = dwarf_get (&c->dwarf, ip_loc, &ra)) < 0)
        return ret;
    } else {
      if ((ret = dwarf_get (&c->dwarf, c->dwarf.loc[UNW_MIPS_R31], &ra)) < 0)
        return ret;
    }
    if (fp_offset) {
      fp_loc = DWARF_LOC(sp + fp_offset, 0);
      if ((ret = dwarf_get (&c->dwarf, fp_loc, &fp)) < 0)
        return ret;
    }

    sp += stack_size;
  }

  if (!DWARF_IS_NULL_LOC(ip_loc))
    c->dwarf.loc[UNW_MIPS_R31] = ip_loc;
  if (!DWARF_IS_NULL_LOC(fp_loc))
    c->dwarf.loc[UNW_MIPS_R30] = fp_loc;

  /* FIXME (simon): Adjust ip on four or eight(?) bytes */
  c->dwarf.cfa = sp;
  c->dwarf.ip = ra;
  c->dwarf.pi_valid = 0;

  Debug (2, "(ip=0x%016llx, sp=0x%016llx, fp=0x%016llx)\n", ra, sp, fp);

  return (ra == 0 || (old_ip == ra && old_sp == sp)) ? 0 : 1;
}

static inline int
mips_n64_heuristic_step (unw_cursor_t *cursor)
{
  struct cursor *c = (struct cursor *) cursor;
  int ret;
  char pname[32];
  unw_word_t pstart;
  unw_word_t pc;
  int32_t stack_size = 0;
  int32_t ra_offset = 0;
  int32_t fp_offset = 0;
  uint32_t sp_offset = 0;
  uint32_t v1_offset = 0;
  int use_fp = 0;
  int has_sub_v1 = 0;
  unw_word_t ra = 0, sp = 0, fp = 0;
  unw_word_t old_ip, old_sp, old_fp;
  dwarf_loc_t ip_loc = DWARF_NULL_LOC;
  dwarf_loc_t fp_loc = DWARF_NULL_LOC;

  ret = unw_get_proc_name (cursor, pname, sizeof(pname), &pstart);
  if (ret != 0)
    return 0;

  pstart = c->dwarf.ip - pstart;
  Debug (2, "Function boundary %s at 0x%016llx\n", pname, pstart);

  old_ip = c->dwarf.ip;
  old_sp = c->dwarf.cfa;
  if ((ret = dwarf_get (&c->dwarf, c->dwarf.loc[UNW_MIPS_R30], &old_fp)) < 0)
    return ret;

  Debug (2, "(ip=0x%016llx, sp=0x%016llx, fp=0x%016llx)\n", old_ip, old_sp, old_fp);

  pc = c->dwarf.use_prev_instr ? c->dwarf.ip - 4 : c->dwarf.ip;

  for (; pc >= pstart; pc -= 4) {
    unw_word_t op;
    int32_t immediate;
    if ((ret = dwarf_get (&c->dwarf, DWARF_LOC (pc, 0), &op)) < 0)
      return ret;

    op &= 0xffffffff;

    /* move ra, zero */
    if (op == 0x3e0002d) {
      Debug (2, "'move ra, zero' stop condition at 0x%016llx\n", pc);
      return 0;
    }

    /* move s8, sp */
    if (op == 0x3a0f02d) {
      Debug (2, "sp saved to the s8 at 0x%016llx\n", pc);
// FIXME (simon): Fix
//      if ((ret = find_sp_restore(c, c->dwarf.ip)) < 0)
//        return ret;
//      if (ret) {
        Debug (2, "treat s8 as fp register\n");
        use_fp = 1;
//      }
    }

    switch (op & 0xffff0000) {
      case 0x67bd0000: /* daddiu sp, imm */
        immediate = (((int32_t)op) << 16) >> 16;
        if (immediate < 0) {
          Debug (2, "stack adjustment %d at 0x%016llx\n", -immediate, pc);
          if (fp_offset || ra_offset)
            stack_size += -immediate;
          else if (use_fp)
            sp_offset += -immediate;
        }
        break;
      case 0x34030000: /* li v1,imm */
        if (has_sub_v1)
          v1_offset = op & 0xffff;
        break;
      case 0xffbf0000: /* sd ra, imm(sp) */
        ra_offset = (((int32_t)op) << 16) >> 16;
        Debug (2, "ra offset %d at 0x%016llx\n", ra_offset, pc);
        break;
      case 0xffbe0000: /* sd s8, imm(sp) */
        fp_offset = (((int32_t)op) << 16) >> 16;
        Debug (2, "fp offset %d at 0x%016llx\n", fp_offset, pc);
        break;
      default:
        break;
    }

    /* dsubu sp,sp,v1 */
    if (op == 0x3a3e82f)
      has_sub_v1 = 1;
  }

  if (use_fp) {
    if ((ret = dwarf_get (&c->dwarf, c->dwarf.loc[UNW_MIPS_R30], &fp)) < 0)
      return ret;

    fp += sp_offset + v1_offset;
    sp = fp + stack_size;

    if (ra_offset) {
      ip_loc = DWARF_LOC(fp + ra_offset, 0);
      if ((ret = dwarf_get (&c->dwarf, ip_loc, &ra)) < 0)
        return ret;
    } else {
      if ((ret = dwarf_get (&c->dwarf, c->dwarf.loc[UNW_MIPS_R31], &ra)) < 0)
        return ret;
    }
    if (fp_offset) {
      fp_loc = DWARF_LOC(fp + fp_offset, 0);
      if ((ret = dwarf_get (&c->dwarf, fp_loc, &fp)) < 0)
        return ret;
    }
  } else {
    sp = c->dwarf.cfa;

    if (ra_offset) {
      ip_loc = DWARF_LOC(sp + ra_offset, 0);
      if ((ret = dwarf_get (&c->dwarf, ip_loc, &ra)) < 0)
        return ret;
    } else {
      if ((ret = dwarf_get (&c->dwarf, c->dwarf.loc[UNW_MIPS_R31], &ra)) < 0)
        return ret;
    }

    sp += stack_size;
  }

  if (!DWARF_IS_NULL_LOC(ip_loc))
    c->dwarf.loc[UNW_MIPS_R31] = ip_loc;
  if (!DWARF_IS_NULL_LOC(fp_loc))
    c->dwarf.loc[UNW_MIPS_R30] = fp_loc;
 
  /* FIXME (simon): Adjust ip on four or eight(?) bytes */
  c->dwarf.cfa = sp;
  c->dwarf.ip = ra;
  c->dwarf.pi_valid = 0;

  Debug (2, "(ip=0x%016llx, sp=0x%016llx, fp=0x%016llx)\n", ra, sp, fp);

  return (ra == 0 || (old_ip == ra && old_sp == sp)) ? 0 : 1;
}

PROTECTED int
unw_handle_signal_frame (unw_cursor_t *cursor)
{
  struct cursor *c = (struct cursor *) cursor;
  int ret;
  unw_word_t sc_addr, sp_addr = c->dwarf.cfa;
  unw_word_t ra, fp;

  ret = unw_is_signal_frame (cursor);
  Debug(1, "unw_is_signal_frame()=%d\n", ret);

  /* FIXME (simon): Save the SP and PC to be able to return execution
     at this point later in time (unw_resume). */
  // c->sigcontext_sp = c->dwarf.cfa;
  // c->sigcontext_pc = c->dwarf.ip;

  switch (ret) {
  case 1:
    sc_addr = sp_addr + sizeof (siginfo_t) + LINUX_UC_MCONTEXT_OFF;
    break;
  case 2:
    sc_addr = sp_addr;
    break;
  default:
    return -UNW_EUNSPEC;
  }

  if (tdep_big_endian(c->dwarf.as))
    sc_addr += 4;

  c->sigcontext_addr = sc_addr;

  /* Update the dwarf cursor. */
  c->dwarf.loc[UNW_MIPS_R0]  = DWARF_LOC (sc_addr + LINUX_SC_R0_OFF, 0);
  c->dwarf.loc[UNW_MIPS_R1]  = DWARF_LOC (sc_addr + LINUX_SC_R1_OFF, 0);
  c->dwarf.loc[UNW_MIPS_R2]  = DWARF_LOC (sc_addr + LINUX_SC_R2_OFF, 0);
  c->dwarf.loc[UNW_MIPS_R3]  = DWARF_LOC (sc_addr + LINUX_SC_R3_OFF, 0);
  c->dwarf.loc[UNW_MIPS_R4]  = DWARF_LOC (sc_addr + LINUX_SC_R4_OFF, 0);
  c->dwarf.loc[UNW_MIPS_R5]  = DWARF_LOC (sc_addr + LINUX_SC_R5_OFF, 0);
  c->dwarf.loc[UNW_MIPS_R6]  = DWARF_LOC (sc_addr + LINUX_SC_R6_OFF, 0);
  c->dwarf.loc[UNW_MIPS_R7]  = DWARF_LOC (sc_addr + LINUX_SC_R7_OFF, 0);
  c->dwarf.loc[UNW_MIPS_R8]  = DWARF_LOC (sc_addr + LINUX_SC_R8_OFF, 0);
  c->dwarf.loc[UNW_MIPS_R9]  = DWARF_LOC (sc_addr + LINUX_SC_R9_OFF, 0);
  c->dwarf.loc[UNW_MIPS_R10] = DWARF_LOC (sc_addr + LINUX_SC_R10_OFF, 0);
  c->dwarf.loc[UNW_MIPS_R11] = DWARF_LOC (sc_addr + LINUX_SC_R11_OFF, 0);
  c->dwarf.loc[UNW_MIPS_R12] = DWARF_LOC (sc_addr + LINUX_SC_R12_OFF, 0);
  c->dwarf.loc[UNW_MIPS_R13] = DWARF_LOC (sc_addr + LINUX_SC_R13_OFF, 0);
  c->dwarf.loc[UNW_MIPS_R14] = DWARF_LOC (sc_addr + LINUX_SC_R14_OFF, 0);
  c->dwarf.loc[UNW_MIPS_R15] = DWARF_LOC (sc_addr + LINUX_SC_R15_OFF, 0);
  c->dwarf.loc[UNW_MIPS_R16] = DWARF_LOC (sc_addr + LINUX_SC_R16_OFF, 0);
  c->dwarf.loc[UNW_MIPS_R17] = DWARF_LOC (sc_addr + LINUX_SC_R17_OFF, 0);
  c->dwarf.loc[UNW_MIPS_R18] = DWARF_LOC (sc_addr + LINUX_SC_R18_OFF, 0);
  c->dwarf.loc[UNW_MIPS_R19] = DWARF_LOC (sc_addr + LINUX_SC_R19_OFF, 0);
  c->dwarf.loc[UNW_MIPS_R20] = DWARF_LOC (sc_addr + LINUX_SC_R20_OFF, 0);
  c->dwarf.loc[UNW_MIPS_R21] = DWARF_LOC (sc_addr + LINUX_SC_R21_OFF, 0);
  c->dwarf.loc[UNW_MIPS_R22] = DWARF_LOC (sc_addr + LINUX_SC_R22_OFF, 0);
  c->dwarf.loc[UNW_MIPS_R23] = DWARF_LOC (sc_addr + LINUX_SC_R23_OFF, 0);
  c->dwarf.loc[UNW_MIPS_R24] = DWARF_LOC (sc_addr + LINUX_SC_R24_OFF, 0);
  c->dwarf.loc[UNW_MIPS_R25] = DWARF_LOC (sc_addr + LINUX_SC_R25_OFF, 0);
  c->dwarf.loc[UNW_MIPS_R26] = DWARF_LOC (sc_addr + LINUX_SC_R26_OFF, 0);
  c->dwarf.loc[UNW_MIPS_R27] = DWARF_LOC (sc_addr + LINUX_SC_R27_OFF, 0);
  c->dwarf.loc[UNW_MIPS_R28] = DWARF_LOC (sc_addr + LINUX_SC_R28_OFF, 0);
  c->dwarf.loc[UNW_MIPS_R29] = DWARF_LOC (sc_addr + LINUX_SC_R29_OFF, 0);
  c->dwarf.loc[UNW_MIPS_R30] = DWARF_LOC (sc_addr + LINUX_SC_R30_OFF, 0);
  c->dwarf.loc[UNW_MIPS_R31] = DWARF_LOC (sc_addr + LINUX_SC_R31_OFF, 0);

  /* Set SP/CFA and PC/IP. */
  dwarf_get (&c->dwarf, c->dwarf.loc[UNW_MIPS_R29], &c->dwarf.cfa);
//  dwarf_get (&c->dwarf, c->dwarf.loc[UNW_MIPS_R31], &c->dwarf.ip);
  if ((ret = dwarf_get(&c->dwarf, DWARF_LOC(sc_addr + LINUX_SC_PC_OFF, 0), &c->dwarf.ip)) < 0)
    return ret;

  if ((ret = dwarf_get(&c->dwarf, DWARF_LOC(sc_addr + LINUX_SC_R31_OFF, 0), &ra)) < 0)
    return ret;
  if ((ret = dwarf_get(&c->dwarf, DWARF_LOC(sc_addr + LINUX_SC_R30_OFF, 0), &fp)) < 0)
    return ret;

  Debug (2, "SH (ip=0x%016llx, ra=0x%016llx, sp=0x%016llx, fp=0x%016llx)\n",
         c->dwarf.ip, ra, c->dwarf.cfa, fp);

  c->dwarf.pi_valid = 0;
  c->dwarf.use_prev_instr = 0;

  return 1;
}

PROTECTED int
unw_step (unw_cursor_t *cursor)
{
  struct cursor *c = (struct cursor *) cursor;
  int ret;

  Debug (1, "(cursor=%p, ip=0x%016llx)\n", c, c->dwarf.ip);

  ret = unw_is_signal_frame (cursor);
  if (ret < 0)
    return ret;
  if (ret > 0) {
    if ((ret = unw_handle_signal_frame (cursor)) < 0)
      return ret;
  }

  /* First, try DWARF-based unwinding. */
  ret = dwarf_step (&c->dwarf);
 
  if (unlikely (ret < 0 && ret != -UNW_ENOINFO))
     return ret;
 
  /* DWARF didn't work, try the heuristic approach. */
  if (unlikely (ret < 0))
    switch (c->dwarf.as->abi)
      {
      case UNW_MIPS_ABI_O32:
        return mips_heuristic_step (c);
      case UNW_MIPS_ABI_N64:
        return mips_n64_heuristic_step (cursor);
      default:
        return ret;
      }
 
   return (c->dwarf.ip == 0) ? 0 : 1;
}
