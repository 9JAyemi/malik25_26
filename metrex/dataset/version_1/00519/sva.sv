// SVA bind file for xor_module and top_module
// Focused, high-quality checks plus concise coverage

// ---------------- xor_module assertions ----------------
module xor_module_sva;
  // Combinational correctness (evaluated whenever signals change)
  always_comb begin
    assert (out_xor == (in_data ^ 3'b111))
      else $error("xor_module: out_xor != in_data ^ 3'b111");
    assert (out_inv == ~in_data)
      else $error("xor_module: out_inv != ~in_data");
    assert (out_xor == out_inv)
      else $error("xor_module: out_xor != out_inv (should be identical for 3'b111)");
  end

  // Full input space coverage (0..7)
  genvar i;
  generate
    for (i=0; i<8; i++) begin : cv_in
      cover property (in_data == i[2:0]);
    end
  endgenerate
endmodule
bind xor_module xor_module_sva xor_module_sva_i();

// ---------------- top_module assertions ----------------
module top_module_sva;
  // Catch the illegal comb loop/unknowns on ready path
  always_comb begin
    assert (!$isunknown(ready_b)) else $error("ready_b is X/Z (combinational feedback?)");
    assert (not_ready_b == ~ready_b) else $error("not_ready_b must be ~ready_b");
  end

  // Use valid_a edges as the design’s timing event
  default clocking cb @(posedge valid_a); endclocking

  // Internal transforms must be correct
  a_xforms: assert property (
      (out_xor_a == (a ^ 3'b111)) &&
      (out_xor_b == (b ^ 3'b111)) &&
      (inv_a     == ~a) &&
      (inv_b     == ~b)
  );

  // OR logic correctness
  a_or_bitwise: assert property (out_or_bitwise == (out_xor_a | out_xor_b));
  a_or_logical: assert property (out_or_logical == (|out_or_bitwise));

  // Handshake/update behavior on posedge valid_a
  a_ready_true:  assert property (ready_b  |-> ##0 (valid_b && (out_not == {inv_a, inv_b})));
  a_ready_false: assert property (!ready_b |-> ##0 (!valid_b));

  // Hold out_not when not ready (between valid_a edges)
  a_hold_on_not_ready: assert property (!ready_b |=> (out_not == $past(out_not)));

  // Concise functional coverage
  c_any_or:     cover property (out_or_logical == 1);
  c_no_or:      cover property ((out_or_logical == 0) && (out_or_bitwise == 3'b000)); // only when a==b==3'b111
  c_ready_path: cover property (ready_b && valid_a);
  c_block_path: cover property (!ready_b && valid_a);
  c_minmin:     cover property (a==3'b000 && b==3'b000);
  c_maxmax:     cover property (a==3'b111 && b==3'b111);
  c_minmax:     cover property (a==3'b000 && b==3'b111);
  c_maxmin:     cover property (a==3'b111 && b==3'b000);
endmodule
bind top_module top_module_sva top_module_sva_i();