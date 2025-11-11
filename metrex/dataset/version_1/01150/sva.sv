// SVA checker for binary_to_gray. Provide a sampling clock when binding.
module binary_to_gray_sva(
  input logic        clk,
  input logic [3:0]  bin_in,
  input logic [3:0]  gray_out
);
  default clocking cb @(posedge clk); endclocking

  function automatic logic [3:0] gray_ref(input logic [3:0] b);
    gray_ref = b ^ (b >> 1);
  endfunction

  // Correctness: gray == bin ^ (bin>>1)
  a_map:    assert property (gray_out == gray_ref(bin_in));

  // No X/Z on output when input is known
  a_no_x:   assert property (!$isunknown(bin_in) |-> !$isunknown(gray_out));

  // Pure combinational: stable input => stable output
  a_stable: assert property ($stable(bin_in) |-> $stable(gray_out));

  // Adjacent binary change (+/-1) => exactly one-bit change in Gray
  a_adj1: assert property (
    ((bin_in == $past(bin_in,1,bin_in) + 4'd1) ||
     (bin_in == $past(bin_in,1,bin_in) - 4'd1))
    |-> $onehot(gray_out ^ $past(gray_out,1,gray_out))
  );

  // Coverage: hit all 16 input codes with correct output
  genvar v;
  generate
    for (v = 0; v < 16; v++) begin : CODES
      cover property (bin_in == v[3:0] && gray_out == gray_ref(v[3:0]));
    end
  endgenerate

  // Coverage: observe +/-1 adjacency with one-bit Gray change
  c_inc: cover property ((bin_in == $past(bin_in,1,bin_in) + 4'd1) &&
                         $onehot(gray_out ^ $past(gray_out,1,gray_out)));
  c_dec: cover property ((bin_in == $past(bin_in,1,bin_in) - 4'd1) &&
                         $onehot(gray_out ^ $past(gray_out,1,gray_out)));

  // Coverage: each output bit toggles at least once
  genvar i;
  generate
    for (i = 0; i < 4; i++) begin : GT
      cover property ($changed(gray_out[i]));
    end
  endgenerate
endmodule

// Example bind (assuming a testbench clock tb_clk exists):
// bind binary_to_gray binary_to_gray_sva u_sva(.clk(tb_clk), .bin_in(bin_in), .gray_out(gray_out));