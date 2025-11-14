// SVA for module Test
// Focus: correctness of dynamic part-select, truncation into out[3:0], and mask validity

bind Test Test_sva();

module Test_sva;
  default clocking cb @(posedge clk); endclocking

  // out must equal the lower 4 bits of the 5-bit dynamic slice (X-propagation allowed)
  a_out_trunc_sel: assert property (
    out === p[15 + $past(in) - 1 -: 4]
  );

  // mask encodes which of the 4 delivered bits are in-range (relative to p[15])
  a_mask_equiv: assert property (
    mask === { ($past(in) < 2), ($past(in) < 3), ($past(in) < 4), ($past(in) < 5) }
  );

  // Each out bit must be either the corresponding p bit (if masked in) or X (if masked out)
  genvar i;
  generate
    for (i=0; i<4; i++) begin : g_mask_gate
      a_mask_gates_out: assert property (
        out[i] === ( mask[i] ? p[(15 + $past(in)) - (i+1)] : 1'bx )
      );
    end
  endgenerate

  // Coverage: all mask patterns and presence of X on out when fully out-of-range
  c_mask_1111: cover property (mask == 4'b1111); // in == 0
  c_mask_0111: cover property (mask == 4'b0111); // in == 2
  c_mask_0011: cover property (mask == 4'b0011); // in == 3
  c_mask_0001: cover property (mask == 4'b0001); // in == 4
  c_mask_0000: cover property (mask == 4'b0000); // in >= 5
  c_out_has_x:  cover property ($isunknown(out)); // any cycle with out-of-range selection
endmodule