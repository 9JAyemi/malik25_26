// SVA for edge_detector and top_module (concise, high-quality checks + coverage)

module edge_detector_sva;
  default clocking cb @(posedge clk); endclocking

  // History guards
  let have1 = $past(1'b1,1);
  let have3 = $past(1'b1,3);
  let have4 = $past(1'b1,4);

  // Shift pipeline correctness (compact vector form)
  a_shift_pipe: assert property (
    have3 |-> {shift_reg[2], shift_reg[1], shift_reg[0]} ==
               {$past(in,3),   $past(in,2),   $past(in)}
  );

  // edge_reg function (uses previous contents of the shift stages)
  a_edge_fn: assert property (
    have3 |-> edge_reg == (($past(in,1) ^ $past(in,3)) & $past(in,2))
  );

  // Output mapping: MSB forced to 0; LSBs are edge_reg delayed by 1
  a_out_msb0:           assert property (have1 |-> out[7] == 1'b0);
  a_out_from_edge_reg:  assert property (have1 |-> out[6:0] == $past(edge_reg[6:0]));

  // Strong closed-form check: out as a pure function of input history (4-cycle span)
  a_out_from_in: assert property (
    have4 |-> out[6:0] ==
      ( ($past(in,2)[6:0] ^ $past(in,4)[6:0]) & $past(in,3)[6:0] )
  );

  // Focused functional coverage (bit 0 patterns that should assert out[0])
  c_edge_pat_011: cover property (
    have4 && { $past(in[0],4), $past(in[0],3), $past(in[0],2) } == 3'b011 && out[0]
  );
  c_edge_pat_110: cover property (
    have4 && { $past(in[0],4), $past(in[0],3), $past(in[0],2) } == 3'b110 && out[0]
  );
  c_nonzero_out: cover property (have4 && out != 8'h00);
endmodule

bind edge_detector edge_detector_sva ed_sva();


module top_module_sva;
  default clocking cb @(posedge clk); endclocking

  // Combinational passthrough must hold
  a_top_passthru: assert property (anyedge == edge_out);
  // Interface MSB must remain 0
  a_top_msb0:     assert property ($past(1'b1,1) |-> anyedge[7] == 1'b0);

  // Top-level coverage that we see a nonzero edge vector
  c_anyedge_seen: cover property (anyedge != 8'h00);
endmodule

bind top_module top_module_sva top_sva();