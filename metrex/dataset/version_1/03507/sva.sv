// SVA for add_subtract_display
module add_subtract_display_sva (add_subtract_display dut);

  default clocking cb @(posedge dut.clk); endclocking

  // Reset behavior
  a_reset_clear: assert property ($rose(dut.reset) |=> (dut.add_shift_reg==7'b0 && dut.sub_shift_reg==7'b0 && dut.display_out==7'b0));
  a_reset_hold:  assert property (dut.reset |->   (dut.add_shift_reg==7'b0 && dut.sub_shift_reg==7'b0 && dut.display_out==7'b0));
  c_reset:       cover  property ($fell(dut.reset));

  // Combinational arithmetic correctness
  a_add_fn: assert property (dut.add_out == (dut.a + dut.b));
  a_sub_fn: assert property (dut.sub_out == (dut.a - dut.b));

  // Shift-register behavior (new value equals shifted previous + previous MSB of arithmetic output)
  a_add_shift: assert property ($past(!dut.reset) |-> dut.add_shift_reg == { $past(dut.add_shift_reg)[5:0], $past(dut.add_out[3]) });
  a_sub_shift: assert property ($past(!dut.reset) |-> dut.sub_shift_reg == { $past(dut.sub_shift_reg)[5:0], $past(dut.sub_out[3]) });

  // Output selection (uses pre-update regs and op from previous cycle)
  a_sel: assert property ($past(!dut.reset) |-> dut.display_out == ( $past(dut.op) ? $past(dut.sub_shift_reg) : $past(dut.add_shift_reg) ));

  // 7-seg decoder equivalence (full map + default)
  function automatic logic [6:0] seg_ref (input logic [6:0] disp);
    case (disp)
      7'b0000000: seg_ref = 7'b1111110;
      7'b0000001: seg_ref = 7'b0110000;
      7'b0000010: seg_ref = 7'b1101101;
      7'b0000011: seg_ref = 7'b1111001;
      7'b0000100: seg_ref = 7'b0110011;
      7'b0000101: seg_ref = 7'b1011011;
      7'b0000110: seg_ref = 7'b1011111;
      7'b0000111: seg_ref = 7'b1110000;
      7'b0001000: seg_ref = 7'b1111111;
      7'b0001001: seg_ref = 7'b1110011;
      default:    seg_ref = 7'b0000001;
    endcase
  endfunction
  a_dec:       assert property (dut.seg == seg_ref(dut.display_out));
  a_seg_known: assert property (!$isunknown(dut.seg));

  // Basic control coverage
  c_op0: cover property (!dut.reset && !dut.op);
  c_op1: cover property (!dut.reset &&  dut.op);

  // Cover that 0/1 bits are shifted in on both paths (LSB reflects prior MSB)
  c_add_in0: cover property ($past(!dut.reset) && $past(dut.add_out[3])==0 && dut.add_shift_reg[0]==0);
  c_add_in1: cover property ($past(!dut.reset) && $past(dut.add_out[3])==1 && dut.add_shift_reg[0]==1);
  c_sub_in0: cover property ($past(!dut.reset) && $past(dut.sub_out[3])==0 && dut.sub_shift_reg[0]==0);
  c_sub_in1: cover property ($past(!dut.reset) && $past(dut.sub_out[3])==1 && dut.sub_shift_reg[0]==1);

  // Decoder mapping assertions and coverage for digits 0..9 and default
  localparam logic [6:0] DISP_CODES [10] = '{
    7'b0000000,7'b0000001,7'b0000010,7'b0000011,7'b0000100,
    7'b0000101,7'b0000110,7'b0000111,7'b0001000,7'b0001001
  };
  localparam logic [6:0] SEG_CODES  [10] = '{
    7'b1111110,7'b0110000,7'b1101101,7'b1111001,7'b0110011,
    7'b1011011,7'b1011111,7'b1110000,7'b1111111,7'b1110011
  };
  genvar i;
  generate
    for (i=0;i<10;i++) begin : g_dec_chk
      a_dec_i: assert property (dut.display_out==DISP_CODES[i] |-> dut.seg==SEG_CODES[i]);
      c_dec_i: cover  property (dut.display_out==DISP_CODES[i] &&  dut.seg==SEG_CODES[i]);
    end
  endgenerate
  c_dash: cover property (dut.seg == 7'b0000001);

  // Wrap/borrow coverage on 4-bit arithmetic
  c_add_wrap: cover property (!dut.reset && ((dut.a + dut.b) < dut.a));
  c_sub_wrap: cover property (!dut.reset && ((dut.a - dut.b) > dut.a));

endmodule

bind add_subtract_display add_subtract_display_sva sva_add_subtract_display();