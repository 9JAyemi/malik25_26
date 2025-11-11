// SVA checker for bin_to_bcd
// Focus: functional correctness, range, X-propagation, and key coverage.
// Bind this to the DUT and drive clk from your TB. Tie rst_n=1’b1 if unused.

module bin_to_bcd_sva (
  input logic        clk,
  input logic        rst_n,
  input logic [3:0]  bin_in,
  input logic [3:0]  bcd_out_hi,
  input logic [3:0]  bcd_out_lo
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // No X-propagation on outputs when inputs are known
  a_no_x: assert property ( !$isunknown(bin_in) |-> (!$isunknown(bcd_out_hi) && !$isunknown(bcd_out_lo)) )
    else $error("bin_to_bcd: X/Z on outputs for known input");

  // High BCD nibble must be 0 or 1 only
  a_hi_0_or_1: assert property ( bcd_out_hi inside {4'b0000,4'b0001} )
    else $error("bin_to_bcd: bcd_out_hi not 0/1");

  // Low BCD nibble within 0..9
  a_lo_range: assert property ( $unsigned(bcd_out_lo) <= 9 )
    else $error("bin_to_bcd: bcd_out_lo > 9");

  // Spec: True BCD conversion for 0..15
  a_hi_spec: assert property ( bcd_out_hi == ((bin_in >= 4'd10) ? 4'b0001 : 4'b0000) )
    else $error("bin_to_bcd: high BCD digit incorrect");

  a_lo_spec: assert property ( bcd_out_lo == ((bin_in >= 4'd10) ? (bin_in - 4'd10) : bin_in) )
    else $error("bin_to_bcd: low BCD digit incorrect");

  // Consistency: 10*hi + lo equals original input
  a_reconstructs: assert property ( $unsigned(bin_in) == (6'd10 * $unsigned(bcd_out_hi)) + $unsigned(bcd_out_lo) )
    else $error("bin_to_bcd: 10*hi + lo != bin_in");

  // Strong implication: hi==1 only for inputs >= 10
  a_hi1_implies_ge10: assert property ( (bcd_out_hi==4'b0001) |-> (bin_in >= 4'd10) )
    else $error("bin_to_bcd: hi==1 but bin_in < 10");

  // Functional coverage
  c_in_0_4:    cover property ( bin_in inside {[4'd0:4'd4]} );
  c_in_5_9:    cover property ( bin_in inside {[4'd5:4'd9]} );
  c_in_10_15:  cover property ( bin_in inside {[4'd10:4'd15]} );
  c_edge_9:    cover property ( bin_in==4'd9  && bcd_out_hi==4'b0000 && bcd_out_lo==4'd9 );
  c_edge_10:   cover property ( bin_in==4'd10 && bcd_out_hi==4'b0001 && bcd_out_lo==4'd0 );
  c_edge_15:   cover property ( bin_in==4'd15 && bcd_out_hi==4'b0001 && bcd_out_lo==4'd5 );
  c_hi0:       cover property ( bcd_out_hi==4'b0000 );
  c_hi1:       cover property ( bcd_out_hi==4'b0001 );
endmodule

// Example bind (provide a TB clock; tie rst_n high if no reset is used)
// bind bin_to_bcd bin_to_bcd_sva u_bin_to_bcd_sva(.clk(tb_clk), .rst_n(1'b1),
//   .bin_in(bin_in), .bcd_out_hi(bcd_out_hi), .bcd_out_lo(bcd_out_lo));