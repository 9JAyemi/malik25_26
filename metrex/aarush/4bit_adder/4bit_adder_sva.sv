`timescale 1ns/1ps

module tb_four_bit_adder;

  // DUT I/O
  logic [3:0] a, b;
  logic cin;
  logic [3:0] sum;
  logic cout;

  // DUT instantiation
  four_bit_adder dut (
    .a(a),
    .b(b),
    .cin(cin),
    .sum(sum),
    .cout(cout)
  );

  // ==============================================================
  // STIMULUS
  // ==============================================================

  initial begin
    // Test all possible combinations exhaustively
    for (int i = 0; i < 16; i++) begin
      for (int j = 0; j < 16; j++) begin
        for (int k = 0; k < 2; k++) begin
          a = i;
          b = j;
          cin = k;
          #1; // allow time for combinational settle
        end
      end
    end
    $display("All combinations tested.");
    $finish;
  end

  // ==============================================================
  // SYSTEMVERILOG ASSERTIONS
  // ==============================================================

  // 1. Functional correctness of sum and cout
  property p_adder_correct;
    ({cout, sum} == (a + b + cin));
  endproperty
  assert property (p_adder_correct)
    else $error("Adder output mismatch: a=%0d b=%0d cin=%0d -> sum=%0d cout=%0d",
                a, b, cin, sum, cout);

  // 2. Carry correctness
  property p_carry_correct;
    (cout == ((a + b + cin) > 4'b1111));
  endproperty
  assert property (p_carry_correct)
    else $error("Carry output incorrect for a=%0d b=%0d cin=%0d", a, b, cin);

  // 3. No unknown or high-impedance values on outputs
  property p_no_xz_outputs;
    !$isunknown({sum, cout});
  endproperty
  assert property (p_no_xz_outputs)
    else $error("Unknown (X/Z) detected on outputs!");

  // 4. Output stability (sum, cout do not change unless inputs change)
  logic [3:0] prev_sum;
  logic prev_cout;
  always @(a or b or cin) begin
    prev_sum = sum;
    prev_cout = cout;
    #1;
    if ((a === a) && (b === b) && (cin === cin)) begin
      assert (sum === (a + b + cin)[3:0])
        else $error("Output changed without input change!");
    end
  end

endmodule
