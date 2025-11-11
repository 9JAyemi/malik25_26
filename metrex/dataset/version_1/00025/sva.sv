// SystemVerilog Assertions for the provided design
// Focused, concise, and bound to top_module

module top_module_sva (
  input logic         clk,
  input logic         reset,
  input logic [99:0]  in,
  input logic [1023:0] mux_in,
  input logic [2:0]   sel,
  input logic [3:0]   out
);

  // Default clock/reset for all properties
  // Sample on clock; ignore checks during reset
  // (Design is combinational; this just provides a sampling edge.)
  // Assertions

  // 1) Sanity/X checks
  // If all primary inputs are known, the output must be known
  assert property (@(posedge clk) disable iff (reset)
    !$isunknown({in, mux_in, sel}) |-> !$isunknown(out)
  );

  // sel must not be X/Z
  assert property (@(posedge clk) disable iff (reset)
    !$isunknown(sel)
  );

  // bitwise_op op tie-off must be 0 (top ties to 3'b000; op is 1b)
  assert property (@(posedge clk) disable iff (reset)
    bitwise_op_inst.op == 1'b0
  );

  // 2) Local module functional equivalence checks

  // bitwise_op result equals input for op=0 (and equals input for op=1 too,
  // but op is tied to 0 in top)
  assert property (@(posedge clk) disable iff (reset)
    bitwise_out == in
  );

  // mux_256_to_1 functional mapping actually used by top (sel is 3b -> 8 choices)
  assert property (@(posedge clk) disable iff (reset)
    mux_out == mux_in[{sel, 2'b00} +: 4]
  );

  // functional_module truncation/XOR behavior
  assert property (@(posedge clk) disable iff (reset)
    out == (bitwise_out[3:0] ^ mux_out)
  );

  // 3) End-to-end golden check at top level
  assert property (@(posedge clk) disable iff (reset)
    out == (in[3:0] ^ mux_in[{sel, 2'b00} +: 4])
  );

  // 4) Minimal but meaningful coverage

  // Exercise all 8 reachable select values
  genvar s;
  generate
    for (s = 0; s < 8; s++) begin : sel_cov
      cover property (@(posedge clk) disable iff (reset) sel == s[2:0]);
    end
  endgenerate

  // Observe output activity
  cover property (@(posedge clk) disable iff (reset) $changed(out));

  // Demonstrate the end-to-end XOR when mux nibble is zero
  cover property (@(posedge clk) disable iff (reset)
    mux_in[{sel,2'b00} +: 4] == 4'h0 && out == in[3:0]
  );

endmodule

bind top_module top_module_sva sva (.*);