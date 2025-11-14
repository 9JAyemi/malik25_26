// SystemVerilog Assertions for the provided design
// Bind-ready, concise, with key checks and coverage

// BCD counter SVA
module bcd_counter_sva (
  input logic       clk,
  input logic       reset,
  input logic [3:0] q
);
  default clocking cb @(posedge clk); endclocking

  // Basic sanity
  assert property (cb !$isunknown(q));

  // Reset drives 0 on the next cycle
  assert property (cb reset |=> q == 4'd0);

  // Output always a valid BCD digit
  assert property (cb q inside {[4'd0:4'd9]});

  // Next-state function
  assert property (cb $past(!reset) |-> q == (($past(q)==4'd9) ? 4'd0 : $past(q)+4'd1));

  // Coverage: full decade and wrap
  cover property (cb disable iff (reset)
                  (q==4'd0 ##1 4'd1 ##1 4'd2 ##1 4'd3 ##1 4'd4
                   ##1 4'd5 ##1 4'd6 ##1 4'd7 ##1 4'd8 ##1 4'd9 ##1 4'd0));

  cover property (cb disable iff (reset) (q==4'd9 ##1 q==4'd0));
endmodule


// Priority encoder SVA (combinational)
module priority_encoder_sva (
  input  logic [3:0] in,
  input  logic [1:0] out
);
  // Functional equivalence on any change
  assert property (@(in or out) out == {(|in[3:2]), (|in[1:0])});
  assert property (@(in or out) !$isunknown(out));

  // Coverage of all output codes
  cover property (@(in or out) out == 2'b00);
  cover property (@(in or out) out == 2'b01);
  cover property (@(in or out) out == 2'b10);
  cover property (@(in or out) out == 2'b11);
endmodule


// Multiplier SVA (combinational)
module multiplier_sva (
  input  logic [3:0] in,
  input  logic [7:0] out
);
  // Shift-left by 4 (x16) correctness
  assert property (@(in or out) out == {in, 4'b0000});
  assert property (@(in or out) !$isunknown(out));

  // Coverage of a few representative values
  cover property (@(in or out) out == 8'h00);
  cover property (@(in or out) out == 8'h90); // 9 * 16
  cover property (@(in or out) out == 8'hF0); // 15 * 16
endmodule


// Top-level integration SVA
module top_sva (
  input  logic       clk,
  input  logic       reset,
  input  logic [3:0] bcd_out,
  input  logic [1:0] ena_wire,
  input  logic [3:0] ena,
  input  logic [7:0] mult_out,
  input  logic [7:0] q
);
  default clocking cb @(posedge clk); endclocking

  // No X on key observable signals at clock edges
  assert property (cb !$isunknown({ena, q, bcd_out, ena_wire, mult_out}));

  // Encoder function and top wiring
  assert property (cb ena_wire == {(|bcd_out[3:2]), (|bcd_out[1:0])});
  assert property (cb ena[1:0] == ena_wire && ena[3:2] == 2'b00);

  // Multiplier function and top wiring
  assert property (cb mult_out == {bcd_out, 4'b0000});
  assert property (cb q == mult_out);

  // Integration coverage: observe all encoder outputs through top wiring
  cover property (cb ena[1:0] == 2'b00);
  cover property (cb ena[1:0] == 2'b01);
  cover property (cb ena[1:0] == 2'b10);
  cover property (cb ena[1:0] == 2'b11);
endmodule


// Bind statements
bind bcd_counter       bcd_counter_sva      bcd_counter_sva_i(.clk(clk), .reset(reset), .q(q));
bind priority_encoder  priority_encoder_sva priority_encoder_sva_i(.in(in), .out(out));
bind multiplier        multiplier_sva       multiplier_sva_i(.in(in), .out(out));
bind top_module        top_sva              top_sva_i(.clk(clk), .reset(reset),
                                                     .bcd_out(bcd_out), .ena_wire(ena_wire),
                                                     .ena(ena), .mult_out(mult_out), .q(q));