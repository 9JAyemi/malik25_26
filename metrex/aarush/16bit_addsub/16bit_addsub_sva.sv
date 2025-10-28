`timescale 1ns/1ps

module tb_addsub_16bit;

  // DUT signals
  logic clk;
  logic reset;
  logic [15:0] a, b;
  logic sub;
  logic [15:0] result;
  logic overflow;

  // Instantiate DUT
  addsub_16bit dut (
    .clk(clk),
    .reset(reset),
    .a(a),
    .b(b),
    .sub(sub),
    .result(result),
    .overflow(overflow)
  );

  // ==============================================================
  // Clock Generation
  // ==============================================================
  always #5 clk = ~clk;

  // ==============================================================
  // Stimulus
  // ==============================================================
  initial begin
    clk = 0;
    reset = 1;
    a = 0;
    b = 0;
    sub = 0;
    #10;
    reset = 0;

    // Run a mix of add/sub operations
    repeat (10) begin
      @(posedge clk);
      a = $random;
      b = $random;
      sub = $urandom_range(0, 1);
    end

    #20;
    $finish;
  end

  // ==============================================================
  // SYSTEMVERILOG ASSERTIONS
  // ==============================================================

  // 1. Reset behavior: temp and carry (implied through result) must reset
  property p_reset_behavior;
    @(posedge clk) reset |-> (result == 16'b0 && overflow == 0);
  endproperty
  assert property (p_reset_behavior)
    else $error("Reset failed to clear outputs");

  // 2. Correct arithmetic for ADD and SUB
  // We compute the expected result using SystemVerilog logic
  logic signed [16:0] expected_sum;
  always_comb begin
    if (sub)
      expected_sum = $signed(a) - $signed(b) + dut.carry;
    else
      expected_sum = $signed(a) + $signed(b) + dut.carry;
  end

  property p_arithmetic_correct;
    @(posedge clk) disable iff (reset)
      result == expected_sum[15:0];
  endproperty
  assert property (p_arithmetic_correct)
    else $error("Arithmetic result mismatch: a=%0d b=%0d sub=%b", a, b, sub);

  // 3. Overflow correctness
  logic signed [15:0] b_effective;
  always_comb begin
    b_effective = (sub) ? (~b + 1'b1) : b;
  end

  property p_overflow_correct;
    @(posedge clk) disable iff (reset)
      overflow == ((a[15] == b_effective[15]) && (result[15] != a[15]));
  endproperty
  assert property (p_overflow_correct)
    else $error("Overflow signal incorrect: a=%0h b=%0h result=%0h sub=%b",
                a, b, result, sub);

  // 4. No X/Z values on outputs
  property p_no_xz_outputs;
    @(posedge clk) !$isunknown({result, overflow});
  endproperty
  assert property (p_no_xz_outputs)
    else $error("Unknown (X/Z) value detected on outputs!");

  // 5. Outputs change only on clock edges
  // Capture result before clock and check for mid-cycle glitches
  logic [15:0] prev_result;
  logic prev_overflow;
  always @(posedge clk) begin
    prev_result <= result;
    prev_overflow <= overflow;
  end
  always @(result or overflow) begin
    if ($time > 0 && !$isunknown(result))
      assert ($time % 10 == 0)
        else $error("Glitch detected on result/overflow outside clock edge");
  end

endmodule
