// SystemVerilog Assertions for priority_encoder.v
// Created: 2025-10-22

`timescale 1ns/1ps

module priority_encoder_sva();

  // Clock and DUT signals declared as interface-slice for formal checking
  logic clk;
  logic [3:0] I;
  logic [1:0] O;

  // Instantiate DUT (behavioral connection for SVA checks)
  // The DUT in the RTL is named priority_encoder and has clocked behavior
  priority_encoder dut (
    .I(I),
    .clk(clk),
    .O(O)
  );

  // Simple clock generator for simulation-based assertion checking
  initial clk = 0;
  always #5 clk = ~clk; // 100MHz-like for checks

  // ==================================================================
  // Helper predicates
  // ==================================================================

  // Input one-hot or zero (allow zero vector). Exactly one or zero bits set.
  function automatic bit is_onehot_or_zero(logic [3:0] v);
    int unsigned cnt;
    cnt = $countones(v);
    return (cnt == 1) || (cnt == 0);
  endfunction

  // Map I to expected 2-bit code. If zero -> 2'b00 (as in RTL default)
  function automatic logic [1:0] expected_code(logic [3:0] v);
    case (v)
      4'b0001: expected_code = 2'b00;
      4'b0010: expected_code = 2'b01;
      4'b0100: expected_code = 2'b10;
      4'b1000: expected_code = 2'b11;
      default: expected_code = 2'b00;
    endcase
  endfunction

  // ==================================================================
  // Interface checks
  // ==================================================================

  // Check: input is always one-hot or zero (design may accept else but assert
  // can flag unexpected multi-hot inputs). Use immediate assert in clock domain.
  always @(posedge clk) begin
    // If this fires, the testbench is driving illegal multi-hot input
    assert (is_onehot_or_zero(I)) else $error("I is not one-hot or zero: %b", I);
  end

  // ==================================================================
  // Functional properties
  // ==================================================================

  // Property 1: The registered output O must always equal expected_code of the
  // stage1_out from previous combinational mapping (i.e., one-cycle delayed).
  // We encode: if I at cycle N is code C, then O at cycle N+1 must be C.
  property p_output_follows_input;
    @(posedge clk) disable iff (0) $rose(clk) |-> ##1 (O == expected_code(I));
  endproperty
  // Bind and assert
  assert property (p_output_follows_input) else $error("O did not follow expected code from I on next cycle: I=%b O=%b", I, O);

  // Property 2: O must be stable within the clock cycle except at the register update
  // (i.e., no mid-cycle changes). We sample O on posedge and negedge to check stability.
  logic [1:0] O_posedge;
  always @(posedge clk) O_posedge <= O;
  always @(negedge clk) begin
    assert (O == O_posedge) else $error("O changed in the clock half-cycle: posedge O=%b negedge O=%b", O_posedge, O);
  end

  // Property 3: If I is zero, O should be 2'b00 after the clock edge (default behavior)
  property p_zero_input_sets_zero_output;
    @(posedge clk) disable iff (0) (I == 4'b0000) |-> ##1 (O == 2'b00);
  endproperty
  assert property (p_zero_input_sets_zero_output) else $error("Zero input did not produce O==00 next cycle when expected: I=%b O=%b", I, O);

  // Cover some scenarios for simulation-based coverage
  initial begin
    // randomize inputs a few times to exercise assertions in simulation
    I = 4'b0000; #20;
    I = 4'b0001; #20;
    I = 4'b0010; #20;
    I = 4'b0100; #20;
    I = 4'b1000; #20;
    // multi-hot input to show assertion trigger (optional)
    I = 4'b0011; #20;
    $finish;
  end

endmodule
