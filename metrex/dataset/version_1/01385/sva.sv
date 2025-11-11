// SVA checker for top_module
module top_module_sva;
  // Bound into top_module's scope; direct access to clk,a,b,d,q,shift_reg,xor_out
  default clocking cb @(posedge clk); endclocking
  default disable iff ($initstate);

  // Basic sanity: no X/Z on key signals when sampled
  a_no_x:        assert property (!$isunknown({a,b,d,shift_reg,xor_out,q}));

  // XOR correctness
  a_xor:         assert property (xor_out == (a ^ b));

  // Shift path: due to width truncation, shift_reg loads d each cycle
  a_shift_load:  assert property (shift_reg == $past(d));

  // Output function
  a_q_func1:     assert property (q == shift_reg + xor_out);
  a_q_func2:     assert property (q == $past(d) + xor_out);

  // Specific add-by-0/1 behavior
  a_q_add1:      assert property ((xor_out == 1'b1) |-> (q == $past(d) + 8'd1));
  a_q_add0:      assert property ((xor_out == 1'b0) |-> (q == $past(d)));

  // Corner/wrap coverage
  c_xor0:        cover property (xor_out == 1'b0);
  c_xor1:        cover property (xor_out == 1'b1);
  c_xor_tog_r:   cover property ($rose(xor_out));
  c_xor_tog_f:   cover property ($fell(xor_out));
  c_wrap:        cover property (($past(d) == 8'hFF) && (xor_out == 1'b1) && (q == 8'h00));
  c_track_d:     cover property ($changed(d) ##1 (shift_reg == $past(d)));
endmodule

bind top_module top_module_sva sva_inst();