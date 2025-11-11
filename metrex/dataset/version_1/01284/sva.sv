// SVA for mux_adder
module mux_adder_sva(
  input  logic        clk,
  input  logic        reset,
  input  logic        select,
  input  logic [2:0]  sel,
  input  logic [3:0]  data0, data1, data2, data3, data4, data5,
  input  logic [1:0]  add_in,
  input  logic [7:0]  out,
  input  logic [3:0]  mux_out,   // internal
  input  logic [1:0]  add_out    // internal
);

  // Helper functions for expected behavior
  function automatic logic [3:0] exp_mux (
    input logic [2:0] s,
    input logic [3:0] d0,d1,d2,d3,d4,d5
  );
    unique case (s)
      3'b000: exp_mux = d0;
      3'b001: exp_mux = d1;
      3'b010: exp_mux = d2;
      3'b011: exp_mux = d3;
      3'b100: exp_mux = d4;
      3'b101: exp_mux = d5;
      default: exp_mux = 4'b0;
    endcase
  endfunction

  function automatic logic [5:0] exp_sum6 (
    input logic [3:0] m,
    input logic [1:0] a
  );
    exp_sum6 = {2'b00, m} + {2'b00, a};
  endfunction

  default clocking cb @ (posedge clk); endclocking

  // Control/data X-checks (during functional operation)
  assert property (disable iff (reset)
    !$isunknown({select, sel, add_in})
  );

  // Reset behavior (async assertion, and while asserted)
  assert property (@(posedge reset) out == 8'h00);
  assert property (reset |-> out == 8'h00);

  // Internal combinational correctness (mux and add gating)
  assert property (disable iff (reset)
    mux_out == exp_mux(sel, data0,data1,data2,data3,data4,data5)
  );
  assert property (disable iff (reset)
    (!select) |-> (add_out == 2'b00)
  );
  assert property (disable iff (reset)
    ( select) |-> (add_out == add_in)
  );

  // Out next-state functional correctness (independent of internals)
  assert property (disable iff (reset)
    (!select) |-> out == {4'b0000, exp_mux(sel, data0,data1,data2,data3,data4,data5)}
  );
  assert property (disable iff (reset)
    ( select) |-> (out[7:6] == 2'b00 &&
                   out[5:0] == exp_sum6(exp_mux(sel, data0,data1,data2,data3,data4,data5), add_in))
  );

  // Structural zero-extension checks
  assert property (disable iff (reset)
    (!select) |-> (out[7:4] == 4'b0000)
  );

  // Coverage
  cover property (disable iff (reset) !select && (sel inside {3'b000,3'b001,3'b010,3'b011,3'b100,3'b101}));
  cover property (disable iff (reset) !select && (sel inside {3'b110,3'b111}) && out == 8'h00);
  cover property (disable iff (reset) select && add_in != 2'b00);
  cover property (disable iff (reset) select && out[5]); // carry into bit5 of 6-bit sum
  cover property (disable iff (reset) !select ##1 select); // 0->1 toggle
  cover property (disable iff (reset)  select ##1 !select); // 1->0 toggle
  cover property ($rose(reset) ##1 !reset); // reset deassertion observed

endmodule

bind mux_adder mux_adder_sva sva_i (.*);