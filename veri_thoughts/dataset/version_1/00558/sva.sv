// SVA for mux4to1
module mux4to1_sva(input logic [3:0] in,
                   input logic [1:0] sel,
                   input logic       out);

  // Sample on any relevant change
  default clocking cb @(in or sel or out); endclocking

  // Basic sanity: no X/Z on sel; and out not X/Z when inputs known
  a_no_x_sel: assert property (!$isunknown(sel))
    else $error("mux4to1: sel has X/Z");
  a_no_x_out_when_inputs_known: assert property (!$isunknown({in,sel}) |-> !$isunknown(out))
    else $error("mux4to1: out X/Z with known inputs");

  // Functional correctness: out equals the selected input bit
  a_mux_func: assert property (out == in[sel])
    else $error("mux4to1: out != in[sel]");

  // No spurious output changes unless sel or the selected input changes
  a_no_spurious_glitch: assert property ($stable(sel) && $stable(in[sel]) |-> $stable(out))
    else $error("mux4to1: out changed without sel/selected-in change");

  // Coverage: each select value seen with both output polarities
  c_sel00_out0: cover property (sel==2'b00 && out==1'b0);
  c_sel00_out1: cover property (sel==2'b00 && out==1'b1);
  c_sel01_out0: cover property (sel==2'b01 && out==1'b0);
  c_sel01_out1: cover property (sel==2'b01 && out==1'b1);
  c_sel10_out0: cover property (sel==2'b10 && out==1'b0);
  c_sel10_out1: cover property (sel==2'b10 && out==1'b1);
  c_sel11_out0: cover property (sel==2'b11 && out==1'b0);
  c_sel11_out1: cover property (sel==2'b11 && out==1'b1);

endmodule

// Bind to DUT
bind mux4to1 mux4to1_sva u_mux4to1_sva(.in(in), .sel(sel), .out(out));