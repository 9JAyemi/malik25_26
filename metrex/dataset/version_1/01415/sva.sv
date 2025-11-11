// SVA checker for adder_subtractor_4bit
module adder_subtractor_4bit_sva (
  input logic        clk,            // supply any free-running TB clock
  input logic [3:0]  A,
  input logic [3:0]  B,
  input logic        SUB,
  input logic [3:0]  result,
  input logic        OVFL
);
  default clocking cb @(posedge clk); endclocking

  // Sized arithmetic to avoid width pitfalls
  logic [4:0] sum5, diff5, twosB5, add_twos5;
  logic [3:0] exp_add, exp_sub, exp_sub_twos;
  logic       known_in, known_out;

  always_comb begin
    sum5        = {1'b0, A} + {1'b0, B};
    diff5       = {1'b0, A} - {1'b0, B};
    twosB5      = {1'b0, ~B} + 5'd1;
    add_twos5   = {1'b0, A} + twosB5;

    exp_add     = sum5[3:0];
    exp_sub     = diff5[3:0];
    exp_sub_twos= add_twos5[3:0];

    known_in    = !$isunknown({A,B,SUB});
    known_out   = !$isunknown({result,OVFL});
  end

  // Outputs must be known when inputs are known
  assert property (known_in |-> ##0 known_out)
    else $error("adder_subtractor_4bit: X/Z on outputs with known inputs");

  // ADD mode: result == (A+B)%16 and OVFL mirrors MSB of result
  assert property (known_in && !SUB |-> ##0 (result == exp_add && OVFL == result[3]))
    else $error("adder_subtractor_4bit: ADD mismatch");

  // SUB mode: result == (A-B)%16 and OVFL mirrors MSB of result
  assert property (known_in &&  SUB |-> ##0 (result == exp_sub && OVFL == result[3]))
    else $error("adder_subtractor_4bit: SUB mismatch");

  // Cross-check: SUB equals A + (~B + 1) modulo 16
  assert property (known_in && SUB |-> ##0 (result == exp_sub_twos))
    else $error("adder_subtractor_4bit: SUB two's-complement mismatch");

  // Combinational stability: stable inputs imply stable outputs
  assert property (known_in && $stable({A,B,SUB}) |-> ##0 $stable({result,OVFL}))
    else $error("adder_subtractor_4bit: outputs glitch with stable inputs");

  // Functional coverage
  cover property (known_in && !SUB && sum5[3] == 1'b0); // add, MSB=0
  cover property (known_in && !SUB && sum5[3] == 1'b1); // add, MSB=1
  cover property (known_in &&  SUB && diff5[3]== 1'b0); // sub, MSB=0
  cover property (known_in &&  SUB && diff5[3]== 1'b1); // sub, MSB=1
  cover property (known_in &&  SUB && (A < B));         // subtract wrap-around
  cover property (known_in && !SUB && (A==4'hF && B==4'hF)); // add high-high
  cover property (known_in &&  SUB && (A==4'h0 && B==4'h1)); // sub underflow edge
  cover property ($rose(SUB));
  cover property ($fell(SUB));

endmodule

// Bind example (connect .clk to any TB clock):
// bind adder_subtractor_4bit adder_subtractor_4bit_sva u_sva (.* , .clk(tb_clk));