// SVA for binary_to_gray. Bind this module to the DUT.
// Assumes a verification clock/reset for sampling.
module binary_to_gray_sva
(
  input logic        clk,
  input logic        rst_n,
  input logic [2:0]  in,
  input logic [2:0]  out
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Helper: expected Gray result
  function automatic logic [2:0] exp_gray(input logic [2:0] b);
    return b ^ (b >> 1);
  endfunction

  // Core functional equivalence (when input is known)
  a_func: assert property ( !$isunknown(in) |-> out == exp_gray(in) );

  // Bitwise sanity (useful debug, redundant but tight)
  a_msb:  assert property ( !$isunknown(in) |-> out[2] == in[2] );
  a_bit1: assert property ( !$isunknown(in) |-> out[1] == (in[2]^in[1]) );
  a_bit0: assert property ( !$isunknown(in) |-> out[0] == (in[1]^in[0]) );

  // No X on out when in is known
  a_no_x_out: assert property ( !$isunknown(in) |-> !$isunknown(out) );

  // Combinational sanity wrt sampling clock
  a_out_changes_only_if_in_changes: assert property ( $changed(out) |-> $changed(in) );
  a_stable_in_implies_stable_out:   assert property ( $stable(in)  |-> $stable(out)  );

  // Injectivity across sampled cycles
  a_injective: assert property ( !$isunknown({in,$past(in)}) && in != $past(in) |-> out != $past(out) );

  // Gray adjacency on +1 binary steps (optional but strong)
  a_gray_step_inc: assert property (
    !$isunknown({in,$past(in)}) && (in == $past(in) + 3'd1) |-> $onehot(out ^ $past(out))
  );

  // Full mapping coverage: see each input with the correct output
  genvar i;
  generate
    for (i = 0; i < 8; i++) begin : COV_MAP
      cover property ( (in == 3'(i)) && (out == exp_gray(3'(i))) );
    end
  endgenerate

  // Transition coverage: observe gray step on +1 increments
  cover property ( !$isunknown({in,$past(in)}) && (in == $past(in) + 3'd1) && $onehot(out ^ $past(out)) );

endmodule

// Example bind (adjust instance path/clock/reset as appropriate):
// bind binary_to_gray binary_to_gray_sva u_b2g_sva (.* , .clk(tb_clk), .rst_n(tb_rst_n));