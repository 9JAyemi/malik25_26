// SVA for mux_adder_xor
// Bind this module to the DUT. Uses a sampling clock from TB.
module mux_adder_xor_sva (
  input logic        clk,
  input logic        rst_n,
  input logic [1:0]  a,b,c,d,
  input logic [1:0]  sel,
  input logic [1:0]  mux_out,
  input logic [1:0]  adder_out,
  input logic [1:0]  final_output
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Basic X checks
  // sel must be known to avoid incomplete case/latch behavior
  a_no_x_sel:     assert property (!$isunknown(sel));
  // If all inputs are known, outputs must be known
  a_no_x_outputs: assert property ( !$isunknown({a,b,c,d,sel}) |-> !$isunknown({mux_out,adder_out,final_output}) );

  // MUX correctness (selection mapping)
  a_mux_00: assert property (sel==2'd0 |-> mux_out==a);
  a_mux_01: assert property (sel==2'd1 |-> mux_out==b);
  a_mux_10: assert property (sel==2'd2 |-> mux_out==c);
  a_mux_11: assert property (sel==2'd3 |-> mux_out==d);

  // Adder correctness (note: design as written makes adder_out == b + 1 mod 4)
  a_adder:   assert property ( adder_out == ((b + 2'd1) & 2'b11) );

  // Final XOR correctness
  a_xor:     assert property ( final_output == (mux_out ^ adder_out) );

  // Minimal functional coverage
  c_sel_00:  cover property (sel==2'd0);
  c_sel_01:  cover property (sel==2'd1);
  c_sel_10:  cover property (sel==2'd2);
  c_sel_11:  cover property (sel==2'd3);

  // Cover adder wrap-around on b=3
  c_add_wrap: cover property ( (b==2'd3) && (adder_out==2'd0) );

  // Exercise all XOR results
  c_xor_0: cover property (final_output==2'd0);
  c_xor_1: cover property (final_output==2'd1);
  c_xor_2: cover property (final_output==2'd2);
  c_xor_3: cover property (final_output==2'd3);

endmodule

// Example bind (from testbench or a package):
// bind mux_adder_xor mux_adder_xor_sva u_sva (
//   .clk(tb_clk), .rst_n(tb_rst_n),
//   .a(a), .b(b), .c(c), .d(d), .sel(sel),
//   .mux_out(mux_out), .adder_out(adder_out), .final_output(final_output)
// );