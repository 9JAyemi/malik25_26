// SystemVerilog Assertions for shift_register

module shift_register_sva(input logic clk, input logic d, input logic q, input logic [2:0] reg_data);

  // Track $past validity for depths 1..3
  logic [2:0] pv;
  always_ff @(posedge clk) pv <= {pv[1:0], 1'b1};

  // Core functional check: 3-bit shift with new LSB = d
  assert property (@(posedge clk) disable iff (!pv[0])
                   reg_data == {$past(reg_data[1:0]), $past(d)});

  // Bit-to-bit shift consistency
  assert property (@(posedge clk) disable iff (!pv[0])
                   reg_data[2:1] == $past(reg_data[1:0]));

  // Output wiring correctness
  assert property (@(posedge clk) q === reg_data[0]);

  // Registered d-to-q behavior (flop equivalence)
  assert property (@(posedge clk) disable iff (!pv[0])
                   q == $past(d));

  // Deeper latency checks from d pipeline
  assert property (@(posedge clk) disable iff (!pv[1])
                   reg_data[1] == $past(d,2));
  assert property (@(posedge clk) disable iff (!pv[2])
                   reg_data[2] == $past(d,3));

  // Coverage: exercise both polarities and full 3-stage propagation
  cover property (@(posedge clk) $rose(q));
  cover property (@(posedge clk) $fell(q));
  cover property (@(posedge clk) d ##1 reg_data[0] ##1 reg_data[1] ##1 reg_data[2]);
  cover property (@(posedge clk) !d ##1 !reg_data[0] ##1 !reg_data[1] ##1 !reg_data[2]);
  cover property (@(posedge clk) reg_data == 3'b000);
  cover property (@(posedge clk) reg_data == 3'b111);
  cover property (@(posedge clk) reg_data == 3'b101);
  cover property (@(posedge clk) reg_data == 3'b010);

endmodule

// Bind into the DUT
bind shift_register shift_register_sva sva_i(.clk(clk), .d(d), .q(q), .reg_data(reg_data));