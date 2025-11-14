// SVA for progmem. Bind this checker to the DUT.
// Focus: functional correctness of ROM mapping, X-safety, stability, and coverage.
module progmem_sva(input logic [7:0] pc, input logic [15:0] instruction);

  // Trigger events on changes (avoids external clock/races)
  event pc_chg, instr_chg;
  always @(pc)         -> pc_chg;
  always @(instruction)-> instr_chg;

  // Golden ROM mapping
  function automatic logic [15:0] exp_instr(input logic [7:0] a);
    unique case (a)
      8'h00: exp_instr = 16'h7f00;
      8'h01: exp_instr = 16'h0100;
      8'h02: exp_instr = 16'h0101;
      8'h03: exp_instr = 16'h7200;
      8'h04: exp_instr = 16'h74ff;
      8'h05: exp_instr = 16'h0a0c;
      8'h06: exp_instr = 16'h0101;
      8'h07: exp_instr = 16'h0000;
      8'h08: exp_instr = 16'h0100;
      8'h09: exp_instr = 16'h01ff;
      8'h0a: exp_instr = 16'h0201;
      8'h0b: exp_instr = 16'h0303;
      8'h0c: exp_instr = 16'h030c;
      default: exp_instr = 16'hffff;
    endcase
  endfunction

  // Correct combinational lookup (sampled after delta to avoid races)
  property p_lookup_correct;
    @(pc_chg) ##0 (instruction == exp_instr(pc));
  endproperty
  assert property (p_lookup_correct)
    else $error("progmem: instruction mismatch for pc=%0h exp=%0h got=%0h", pc, exp_instr(pc), instruction);

  // No spurious instruction changes (only change when pc changes)
  property p_instr_changes_only_with_pc;
    @(instr_chg) ##0 $changed(pc);
  endproperty
  assert property (p_instr_changes_only_with_pc)
    else $error("progmem: instruction changed without pc change");

  // X-safety: known pc implies known instruction
  property p_no_x_on_known_pc;
    @(pc_chg) disable iff ($isunknown(pc)) ##0 !$isunknown(instruction);
  endproperty
  assert property (p_no_x_on_known_pc)
    else $error("progmem: X/Z on instruction with known pc=%0h", pc);

  // X on pc yields default 16'hffff (case semantics)
  property p_x_pc_default;
    @(pc_chg) $isunknown(pc) |-> ##0 (instruction == 16'hffff);
  endproperty
  assert property (p_x_pc_default)
    else $error("progmem: pc has X/Z but instruction != 16'hffff");

  // Functional coverage: hit each defined entry and at least one default
  cover property (@(pc_chg) ##0 (pc==8'h00 && instruction==16'h7f00));
  cover property (@(pc_chg) ##0 (pc==8'h01 && instruction==16'h0100));
  cover property (@(pc_chg) ##0 (pc==8'h02 && instruction==16'h0101));
  cover property (@(pc_chg) ##0 (pc==8'h03 && instruction==16'h7200));
  cover property (@(pc_chg) ##0 (pc==8'h04 && instruction==16'h74ff));
  cover property (@(pc_chg) ##0 (pc==8'h05 && instruction==16'h0a0c));
  cover property (@(pc_chg) ##0 (pc==8'h06 && instruction==16'h0101));
  cover property (@(pc_chg) ##0 (pc==8'h07 && instruction==16'h0000));
  cover property (@(pc_chg) ##0 (pc==8'h08 && instruction==16'h0100));
  cover property (@(pc_chg) ##0 (pc==8'h09 && instruction==16'h01ff));
  cover property (@(pc_chg) ##0 (pc==8'h0a && instruction==16'h0201));
  cover property (@(pc_chg) ##0 (pc==8'h0b && instruction==16'h0303));
  cover property (@(pc_chg) ##0 (pc==8'h0c && instruction==16'h030c));
  cover property (@(pc_chg) ##0 (!(pc inside {
    8'h00,8'h01,8'h02,8'h03,8'h04,8'h05,8'h06,8'h07,8'h08,8'h09,8'h0a,8'h0b,8'h0c
  }) && instruction==16'hffff));

endmodule

bind progmem progmem_sva u_progmem_sva(.pc(pc), .instruction(instruction));