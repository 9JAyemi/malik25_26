// SVA checker for fourBitAdder
// Assumes a sampling clock 'clk' from the environment.
// Bind example (provide a clock in your env):
//   bind fourBitAdder fourBitAdder_sva u_sva(.clk(clk), .in(in), .out(out));

module fourBitAdder_sva(
  input  logic       clk,
  input  logic [3:0] in,
  input  logic [1:0] out
);
  default clocking cb @ (posedge clk); endclocking

  // Helper: low 2 bits of (in[3:2] + in[1:0]) with explicit 3-bit add
  function automatic logic [1:0] sum2_low(input logic [3:0] vin);
    sum2_low = ({1'b0,vin[3:2]} + {1'b0,vin[1:0]})[1:0];
  endfunction

  // Basic sanity: no X/Z on pins
  assert property (!$isunknown(in));
  assert property (!$isunknown(out));

  // Functional correctness (split for better debug)
  assert property ( (in <= 4'd2) |-> (out == 2'b00) );
  assert property ( (in >= 4'd3) |-> (out == sum2_low(in)) );

  // Output stability when input is stable
  assert property ( $stable(in) |-> $stable(out) );

  // Coverage: both branches taken
  cover property (in inside {[0:2]} && out == 2'b00);
  cover property (in inside {[3:15]} && out == sum2_low(in));

  // Coverage: detect carry (sum >= 4) and no-carry cases in add path
  cover property ( (in >= 4'd3) && (({1'b0,in[3:2]} + {1'b0,in[1:0]})[2] == 1'b0) );
  cover property ( (in >= 4'd3) && (({1'b0,in[3:2]} + {1'b0,in[1:0]})[2] == 1'b1) );

  // Coverage: all possible output codes, from both regions where applicable
  cover property (out == 2'b00);
  cover property (out == 2'b01);
  cover property (out == 2'b10);
  cover property (out == 2'b11);

  // Boundary/edge cases
  cover property (in == 4'd0 && out == 2'b00);
  cover property (in == 4'd2 && out == 2'b00);
  cover property (in == 4'd3 && out == sum2_low(in));
  cover property (in == 4'd15 && out == sum2_low(in));
endmodule