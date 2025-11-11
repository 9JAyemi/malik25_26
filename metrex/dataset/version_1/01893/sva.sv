// SVA for PSWreg
module PSWreg_sva (
    input  logic        clk,
    input  logic        rst,
    input  logic        unaligned,
    input  logic        ovf,
    input  logic [31:0] status
);
  default clocking cb @(posedge clk); endclocking

  // Reset drives full zero on next cycle
  a_reset_clears: assert property (rst |=> status == 32'h0);

  // Low bits capture inputs on next cycle when not in reset
  a_cap_lo_bits: assert property ((!rst && $past(1'b1))
                                  |=> (status[1] == $past(unaligned) && status[0] == $past(ovf)));

  // Upper bits zero right after any reset cycle
  a_upper_zero_after_reset: assert property ((!rst && $past(rst)) |-> (status[31:2] == '0));

  // Upper bits never change when not in reset
  a_upper_stable_nrst: assert property ((!rst && $past(!rst)) |-> (status[31:2] == $past(status[31:2])));

  // Only bits [1:0] may change when not in reset
  a_only_lo_bits_change: assert property ((!rst && $past(!rst))
                                          |-> (((status ^ $past(status)) & 32'hffff_fffc) == 32'h0));

  // No X/Z on status after reset release
  a_no_x_after_reset_release: assert property ((!rst && $past(rst)) |-> !$isunknown(status));

  // Coverage
  c_reset_seen:            cover property (rst ##1 !rst);
  c_ovf_updates_status0:   cover property ((!rst && $past(1'b1)) |=> status[0] == $past(ovf));
  c_unal_updates_status1:  cover property ((!rst && $past(1'b1)) |=> status[1] == $past(unaligned));
  c_both_bits_one:         cover property ((!rst && $past(1'b1)) |=> status[1:0] == 2'b11);
endmodule

bind PSWreg PSWreg_sva PSWreg_sva_i (.*);