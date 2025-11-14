// SVA for invert_msb
module invert_msb_sva (
  input logic [3:0] i_binary,
  input logic [3:0] o_inverted
);

  // Functional correctness (4-state, zero-latency)
  a_func: assert property (@(i_binary or o_inverted)
                           1'b1 |-> ##0 (o_inverted === {~i_binary[3], i_binary[2:0]}))
          else $error("invert_msb: functional mismatch");

  // Bit-level checks (redundant but pinpoint failures)
  a_msb: assert property (@(i_binary or o_inverted)
                          1'b1 |-> ##0 (o_inverted[3] === ~i_binary[3]));
  a_lsb: assert property (@(i_binary or o_inverted)
                          1'b1 |-> ##0 (o_inverted[2:0] === i_binary[2:0]));

  // No spurious output changes
  a_change_cause: assert property (@(i_binary or o_inverted)
                                   $changed(o_inverted) |-> ##0 $changed(i_binary));

  // Edge correlation
  a_msb_edge_rise: assert property (@(i_binary or o_inverted)
                                    $rose(i_binary[3]) |-> ##0 $fell(o_inverted[3]));
  a_msb_edge_fall: assert property (@(i_binary or o_inverted)
                                    $fell(i_binary[3]) |-> ##0 $rose(o_inverted[3]));

  genvar k;
  generate
    for (k=0; k<3; k++) begin : g_lsb_edges
      a_lsb_edge_r: assert property (@(i_binary or o_inverted)
                                     $rose(i_binary[k]) |-> ##0 $rose(o_inverted[k]));
      a_lsb_edge_f: assert property (@(i_binary or o_inverted)
                                     $fell(i_binary[k]) |-> ##0 $fell(o_inverted[k]));
    end
  endgenerate

  // Coverage: hit all inputs and key edge behaviors
  genvar v;
  generate
    for (v=0; v<16; v++) begin : g_in_cov
      c_in_val: cover property (@(i_binary) i_binary === 4'(v));
    end
  endgenerate
  c_msb_r: cover property (@(i_binary) $rose(i_binary[3]) ##0 $fell(o_inverted[3]));
  c_msb_f: cover property (@(i_binary) $fell(i_binary[3]) ##0 $rose(o_inverted[3]));
  generate
    for (k=0; k<3; k++) begin : g_lsb_cov
      c_lsb_r: cover property (@(i_binary) $rose(i_binary[k]) ##0 $rose(o_inverted[k]));
      c_lsb_f: cover property (@(i_binary) $fell(i_binary[k]) ##0 $fell(o_inverted[k]));
    end
  endgenerate

endmodule

// Bind into DUT
bind invert_msb invert_msb_sva u_invert_msb_sva (.i_binary(i_binary), .o_inverted(o_inverted));