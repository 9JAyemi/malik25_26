// SVA checker for MUX_4to1
module MUX_4to1_sva (input [3:0] in, input [1:0] sel, input out);

  // Well-formed select (no X/Z)
  a_sel_known: assert property (!$isunknown(sel))
    else $error("MUX_4to1: sel has X/Z");

  // Functional correctness whenever selection and selected bit are known
  a_func: assert property (disable iff ($isunknown(sel) || $isunknown(in[sel])) (out === in[sel]))
    else $error("MUX_4to1: out != in[sel]");

  // No X on out when selected input is known
  a_no_x_out: assert property (disable iff ($isunknown(sel) || $isunknown(in[sel])) !$isunknown(out))
    else $error("MUX_4to1: out is X with known select/data");

  // Functional coverage: see each select value and both data pass-through values
  c_sel_00: cover property (sel == 2'd0);
  c_sel_01: cover property (sel == 2'd1);
  c_sel_10: cover property (sel == 2'd2);
  c_sel_11: cover property (sel == 2'd3);

  c_pass_0_0: cover property (sel == 2'd0 && in[0] == 1'b0 && out == 1'b0);
  c_pass_0_1: cover property (sel == 2'd0 && in[0] == 1'b1 && out == 1'b1);

  c_pass_1_0: cover property (sel == 2'd1 && in[1] == 1'b0 && out == 1'b0);
  c_pass_1_1: cover property (sel == 2'd1 && in[1] == 1'b1 && out == 1'b1);

  c_pass_2_0: cover property (sel == 2'd2 && in[2] == 1'b0 && out == 1'b0);
  c_pass_2_1: cover property (sel == 2'd2 && in[2] == 1'b1 && out == 1'b1);

  c_pass_3_0: cover property (sel == 2'd3 && in[3] == 1'b0 && out == 1'b0);
  c_pass_3_1: cover property (sel == 2'd3 && in[3] == 1'b1 && out == 1'b1);

endmodule

// Bind into all instances of the DUT
bind MUX_4to1 MUX_4to1_sva u_mux_4to1_sva (.in(in), .sel(sel), .out(out));