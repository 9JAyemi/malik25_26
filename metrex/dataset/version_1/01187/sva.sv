// SVA checker for pipelined_adder
// Bind-only; no DUT edits required.

`ifndef PIPELINED_ADDER_SVA
`define PIPELINED_ADDER_SVA

module pipelined_adder_sva (
  input  logic [7:0] a,
  input  logic [7:0] b,
  input  logic [7:0] s,
  input  logic       overflow,
  input  logic [7:0] p,
  input  logic [7:0] g,
  input  logic [7:0] c
);
  // Expected internal signals
  logic [7:0] exp_p, exp_g;
  logic [7:0] exp_c;
  logic [8:0] sum9;
  logic [7:0] exp_sum;
  logic       exp_ovf, exp_cout;

  assign exp_p = a ^ b;
  assign exp_g = a & b;

  // Carry chain expected from a,b (c[i] is carry-out of bit i-1, c[0]=0)
  assign exp_c[0] = 1'b0;
  genvar i;
  generate
    for (i=1; i<8; i++) begin : GEN_C
      assign exp_c[i] = (a[i-1] & b[i-1]) | ((a[i-1] ^ b[i-1]) & exp_c[i-1]);
    end
  endgenerate

  assign sum9    = {1'b0, a} + {1'b0, b};
  assign exp_sum = sum9[7:0];
  assign exp_cout = (a[7] & b[7]) | ((a[7] ^ b[7]) & exp_c[7]);
  assign exp_ovf = (a[7] == b[7]) && (exp_sum[7] != a[7]);

  default clocking cb @(*); endclocking

  // Only check when inputs are known
  property inputs_known; !$isunknown({a,b}); endproperty

  // X/Z-free on outputs and internal nets when inputs are known
  assert property (inputs_known |-> !$isunknown({s, overflow, p, g, c}));

  // Internal signal correctness
  assert property (inputs_known |-> (p == exp_p));
  assert property (inputs_known |-> (g == exp_g));
  assert property (inputs_known |-> (c[0] == 1'b0));
  generate
    for (genvar j=1; j<8; j++) begin : C_REC
      // Recurrence as coded
      assert property (inputs_known |-> c[j] == (g[j-1] | (p[j-1] & c[j-1])));
      // Recurrence versus re-derived from a,b
      assert property (inputs_known |-> c[j] == exp_c[j]);
    end
  endgenerate

  // Numeric sum must match a+b (mod 256)
  assert property (inputs_known |-> s == exp_sum);

  // Bitwise sum must match p ^ exp_c
  assert property (inputs_known |-> s == ((a ^ b) ^ exp_c));

  // Final carry-out consistency
  assert property (inputs_known |-> sum9[8] == exp_cout);

  // Signed overflow must match true a+b overflow
  assert property (inputs_known |-> overflow == exp_ovf);

  // Concise functional coverage
  cover property (inputs_known && (a==8'h00) && (b==8'h00) && (s==8'h00) && !overflow);         // zero+zero
  cover property (inputs_known && (a==8'h7F) && (b==8'h01) && overflow);                        // + overflow
  cover property (inputs_known && (a==8'h80) && (b==8'h80) && overflow);                        // - overflow
  cover property (inputs_known && (g==8'h00) && (s==(a^b)) && !overflow);                       // no-carry case
  cover property (inputs_known && exp_c[7]);                                                    // carry into MSB
  cover property (inputs_known && exp_cout);                                                    // carry-out set
endmodule

// Bind to all instances of pipelined_adder; connects internal nets p,g,c
bind pipelined_adder pipelined_adder_sva i_pipelined_adder_sva (
  .a(a), .b(b), .s(s), .overflow(overflow), .p(p), .g(g), .c(c)
);

`endif