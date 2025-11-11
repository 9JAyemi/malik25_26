// SVA checkers for top_module and its submodules.
// Bind these in your testbench and drive clk from your TB clock.

module top_module_sva (
    input  logic              clk,
    input  logic [15:0]       A,
    input  logic [15:0]       B,
    input  logic              EN,
    input  logic [15:0]       Y,
    input  logic              overflow,
    input  logic [15:0]       sum,
    input  logic [15:0]       decoder_output
);
  default clocking cb @(posedge clk); endclocking

  // Helper expressions
  logic [16:0] sum17;
  logic [3:0]  nib;
  logic [15:0] dec_mask;
  logic        inputs_known;
  assign sum17       = {1'b0, A} + {1'b0, B};
  assign nib         = sum17[15:12];
  assign dec_mask    = 16'h1 << nib;
  assign inputs_known = !$isunknown({A,B,EN});

  // Adder correctness (sum and overflow)
  assert property (inputs_known |-> {overflow, sum} == sum17);

  // Decoder correctness
  assert property (inputs_known && EN  |-> $onehot(decoder_output) && (decoder_output == dec_mask));
  assert property (inputs_known && !EN |-> decoder_output == 16'h0000);

  // Y mirrors decoder_output
  assert property (inputs_known |-> Y == decoder_output);

  // No X/Z on outputs when inputs are known
  assert property (inputs_known |-> !$isunknown({sum, overflow, decoder_output, Y}));

  // Functional coverage
  cover property (EN && $onehot(decoder_output));
  cover property (!EN && decoder_output == 16'h0000);
  cover property (overflow);
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : cov_bits
      cover property (EN && decoder_output[i]);
    end
  endgenerate
endmodule


module ripple_carry_adder_sva (
    input  logic              clk,
    input  logic [15:0]       A,
    input  logic [15:0]       B,
    input  logic              Cin,
    input  logic [15:0]       Sum,
    input  logic              Cout
);
  default clocking cb @(posedge clk); endclocking

  logic [16:0] exp_sum;
  logic        inputs_known;
  assign exp_sum = {1'b0, A} + {1'b0, B} + Cin;
  assign inputs_known = !$isunknown({A,B,Cin});

  assert property (inputs_known |-> {Cout, Sum} == exp_sum);
  assert property (inputs_known |-> !$isunknown({Sum, Cout}));

  cover property (Cout);
endmodule


module decoder_4to16_sva (
    input  logic              clk,
    input  logic [3:0]        A,
    input  logic              EN,
    input  logic [15:0]       Y
);
  default clocking cb @(posedge clk); endclocking

  logic [15:0] exp_Y;
  logic        inputs_known;
  assign exp_Y = EN ? (16'h1 << A) : 16'h0;
  assign inputs_known = !$isunknown({A,EN});

  assert property (inputs_known && EN  |-> $onehot(Y) && (Y == exp_Y));
  assert property (inputs_known && !EN |-> Y == 16'h0000);
  assert property (inputs_known |-> !$isunknown(Y)));

  // Coverage: each output line asserted at least once
  genvar j;
  generate
    for (j = 0; j < 16; j++) begin : cov_line
      cover property (EN && (Y == (16'h1 << j)));
    end
  endgenerate
endmodule

// Example binds (hook clk to your TB clock):
// bind top_module           top_module_sva        u_top_sva(.clk(tb_clk), .A(A), .B(B), .EN(EN), .Y(Y), .overflow(overflow), .sum(sum), .decoder_output(decoder_output));
// bind ripple_carry_adder   ripple_carry_adder_sva u_rca_sva(.clk(tb_clk), .A(A), .B(B), .Cin(Cin), .Sum(Sum), .Cout(Cout));
// bind decoder_4to16        decoder_4to16_sva      u_dec_sva(.clk(tb_clk), .A(A), .EN(EN), .Y(Y));