// SVA checker for four_bit_adder
module four_bit_adder_sva (
  input logic [3:0] a,
  input logic [3:0] b,
  input logic [3:0] sum,
  input logic       carry_out
);

  // Functional correctness when inputs are known
  property p_add_correct;
    @(a or b) (!$isunknown({a,b})) |-> ##0 ({carry_out, sum} == a + b);
  endproperty
  a_add_correct: assert property (p_add_correct);

  // Outputs must be known when inputs are known
  a_outputs_known: assert property (@(a or b)
    (!$isunknown({a,b})) |-> ##0 (!$isunknown({carry_out,sum})));

  // No spurious output changes (outputs only change when inputs change)
  a_no_spurious_output: assert property (@(sum or carry_out)
    1 |-> ($changed(a) || $changed(b)));

  // Coverage: carry cases and key corners
  c_carry0: cover property (@(a or b) (!$isunknown({a,b})) ##0 (carry_out == 1'b0));
  c_carry1: cover property (@(a or b) (!$isunknown({a,b})) ##0 (carry_out == 1'b1));

  c_zero_zero:     cover property (@(a or b) (a==4'd0  && b==4'd0 ) ##0 ({carry_out,sum} == 5'd0));
  c_max_plus_max:  cover property (@(a or b) (a==4'hF && b==4'hF) ##0 ({carry_out,sum} == 5'd30));
  c_f_plus_1:      cover property (@(a or b) (a==4'hF && b==4'd1) ##0 (carry_out && sum==4'h0));
  c_0_plus_f:      cover property (@(a or b) (a==4'd0  && b==4'hF) ##0 (carry_out==1'b0 && sum==4'hF));

  // Coverage: hit every possible 5-bit result (0..30)
  genvar r;
  generate
    for (r = 0; r <= 30; r++) begin : gen_res_cov
      cover property (@(a or b) (!$isunknown({a,b})) ##0 ({carry_out, sum} == r[4:0]));
    end
  endgenerate

  // Optional complete input cross coverage (SV covergroup; enable with +define+ADDER_CG)
`ifdef ADDER_CG
  covergroup cg_add @(a or b);
    coverpoint a { bins all[] = {[0:15]}; }
    coverpoint b { bins all[] = {[0:15]}; }
    cross a, b;
    coverpoint {carry_out,sum} iff (!$isunknown({a,b})) { bins all[] = {[0:30]}; }
  endgroup
  cg_add cg_inst = new();
`endif

endmodule

// Bind the checker to the DUT
bind four_bit_adder four_bit_adder_sva sva_i(.a(a), .b(b), .sum(sum), .carry_out(carry_out));