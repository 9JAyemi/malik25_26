// SVA for barrel_shifter
// Bindable assertions with concise, high-quality checks and coverage

module barrel_shifter_asserts (
  input  logic        clk,
  input  logic        load,
  input  logic [1:0]  ena,
  input  logic [15:0] data,
  input  logic [15:0] q,
  input  logic [15:0] shift_reg,
  input  logic [2:0]  mod_output,
  input  logic [2:0]  final_output
);

  logic past_valid, seen_load;
  initial begin past_valid = 1'b0; seen_load = 1'b0; end
  always @(posedge clk) begin
    past_valid <= 1'b1;
    if (load) seen_load <= 1'b1;
  end

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Basic input X check
  assert property (!$isunknown({load, ena, data}))) else $error("Input X/Z detected");

  // Load behavior
  assert property (load |-> (q == data && shift_reg == data))
    else $error("Load did not copy data into q/shift_reg");

  // q follows previous shift_reg when not loading
  assert property (seen_load && !load |-> q == $past(shift_reg))
    else $error("q did not reflect previous shift_reg on no-load");

  // Rotation behavior (after first load so $past(shift_reg) is known)
  assert property (seen_load && !load && ena==2'b00 |-> shift_reg == {$past(shift_reg)[13:0], $past(shift_reg)[15:14]})
    else $error("Rotate left by 2 failed (ena=00)");

  assert property (seen_load && !load && ena==2'b01 |-> shift_reg == {$past(shift_reg)[14:0], $past(shift_reg)[15]})
    else $error("Rotate left by 1 failed (ena=01)");

  assert property (seen_load && !load && ena==2'b10 |-> shift_reg == {$past(shift_reg)[1:0], $past(shift_reg)[15:2]})
    else $error("Rotate right by 2 failed (ena=10)");

  assert property (seen_load && !load && ena==2'b11 |-> shift_reg == {$past(shift_reg)[2:0], $past(shift_reg)[15:3]})
    else $error("Rotate right by 3 failed (ena=11)");

  // Modulo/comb output checks
  assert property (mod_output == shift_reg[2:0])
    else $error("mod_output != shift_reg[2:0] (mod 8 redundancy broken)");
  assert property (final_output == ~mod_output && final_output == ~shift_reg[2:0])
    else $error("final_output mismatch");

  // Outputs become known after first load
  assert property (seen_load |-> !$isunknown({q, shift_reg, final_output}))
    else $error("Outputs contain X/Z after load");

  // Functional coverage
  cover property (load);
  cover property (seen_load && !load && ena==2'b00);
  cover property (seen_load && !load && ena==2'b01);
  cover property (seen_load && !load && ena==2'b10);
  cover property (seen_load && !load && ena==2'b11);
  cover property (seen_load && !load && ena==2'b00 ##1 !load && ena==2'b01 ##1 !load && ena==2'b10 ##1 !load && ena==2'b11);

endmodule

bind barrel_shifter barrel_shifter_asserts u_barrel_shifter_asserts (
  .clk(clk),
  .load(load),
  .ena(ena),
  .data(data),
  .q(q),
  .shift_reg(shift_reg),
  .mod_output(mod_output),
  .final_output(final_output)
);