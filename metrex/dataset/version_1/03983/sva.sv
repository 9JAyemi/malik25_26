// SVA for shift_adder
module shift_adder_sva(
  input  logic        clk,
  input  logic        load,
  input  logic [31:0] a,
  input  logic [31:0] b,
  input  logic        sub,
  input  logic [31:0] sum,
  input  logic [7:0]  shift_reg,
  input  logic [31:0] adder_input,
  input  logic [31:0] adder_output
);
  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Basic X checks
  assert property (past_valid |-> !$isunknown(sum));

  // Adder path correctness
  assert property (adder_output == (sub ? (32'h0 - adder_input) : adder_input));
  assert property (sum == (sub ? (32'h0 - adder_input) : adder_input));

  // Width/truncation behavior (as coded): adder_input is exactly b
  assert property (adder_input == b);

  // Shift register load and rotate-left-by-1 behavior
  assert property (past_valid && $past(load)  |-> shift_reg == $past(a[7:0]));
  assert property (past_valid && !$past(load) |-> shift_reg == {$past(shift_reg)[6:0], $past(shift_reg)[7]});

  // 8-step rotation returns to the loaded value if no further loads occur
  logic [7:0] v;
  always @(posedge clk) if (load) v <= a[7:0];
  assert property (load ##1 (!load)[*8] |-> shift_reg == v);

  // Ensure shift_reg changes never affect adder_input (confirms truncation bug/behavior)
  assert property (past_valid && $changed(shift_reg) |-> $stable(adder_input));

  // Minimal coverage
  cover property (load);
  cover property (!load);
  cover property ($rose(sub));
  cover property ($fell(sub));
  cover property (!sub && (sum == b));
  cover property (sub && (sum == (32'h0 - b)));
  cover property (load ##1 (!load)[*8] ##1 (shift_reg == v));
  cover property ($changed(shift_reg) && (adder_input == b));
endmodule

bind shift_adder shift_adder_sva sva_inst (
  .clk(clk),
  .load(load),
  .a(a),
  .b(b),
  .sub(sub),
  .sum(sum),
  .shift_reg(shift_reg),
  .adder_input(adder_input),
  .adder_output(adder_output)
);