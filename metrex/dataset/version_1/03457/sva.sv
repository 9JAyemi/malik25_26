// SVA for module asr
// Bind example (in TB/top): bind asr asr_sva u_asr_sva(.clk(clk), .rst_n(rst_n), .*);

module asr_sva(
  input  logic        clk,
  input  logic        rst_n,
  input  logic [31:0] value1,
  input  logic [31:0] value2,
  input  logic [3:0]  shift_hex,
  input  logic [31:0] value_out,
  input  logic        EN
);

  default clocking cb @(posedge clk); endclocking

  function automatic logic or_unary_f(input logic [31:0] v2);
    return |v2[31:5];
  endfunction

  function automatic logic [4:0] exp_shift_amt(input logic [31:0] v2, input logic [3:0] sh);
    logic [4:0] shr  = v2[4:0];
    logic [4:0] sh5  = {1'b0, sh};
    return (shr == 5'd0) ? (sh5 + 5'd1) : (shr + sh5); // 5-bit wrap
  endfunction

  function automatic logic [31:0] asr_res(input logic [31:0] v1, input logic [4:0] sa);
    return $signed(v1) >>> sa;
  endfunction

  // Known output when inputs are known
  property p_known_out;
    disable iff (!rst_n || $isunknown({value1,value2,shift_hex}))
    !$isunknown(value_out);
  endproperty
  assert property (p_known_out);

  // or_unary high forces zero
  property p_or1_zero;
    disable iff (!rst_n || $isunknown({value1,value2,shift_hex}))
    or_unary_f(value2) |-> (value_out == 32'd0);
  endproperty
  assert property (p_or1_zero);

  // or_unary low => arithmetic right shift by computed amount
  property p_or0_asr;
    disable iff (!rst_n || $isunknown({value1,value2,shift_hex}))
    !or_unary_f(value2) |-> (value_out == asr_res(value1, exp_shift_amt(value2, shift_hex)));
  endproperty
  assert property (p_or0_asr);

  // Special corner checks (concise)
  property p_sa0_passthru;
    disable iff (!rst_n || $isunknown({value1,value2,shift_hex}))
    (!or_unary_f(value2) && (exp_shift_amt(value2,shift_hex)==5'd0)) |-> (value_out == value1);
  endproperty
  assert property (p_sa0_passthru);

  property p_sa31_signfill;
    disable iff (!rst_n || $isunknown({value1,value2,shift_hex}))
    (!or_unary_f(value2) && (exp_shift_amt(value2,shift_hex)==5'd31)) |-> (value_out == {32{value1[31]}});
  endproperty
  assert property (p_sa31_signfill);

  // EN should not affect output when inputs are stable (since DUT ignores EN)
  property p_en_ignored_when_inputs_stable;
    disable iff (!rst_n || $isunknown({value1,value2,shift_hex,EN,$past(EN)}))
    $stable({value1,value2,shift_hex}) && (EN != $past(EN)) |-> $stable(value_out);
  endproperty
  assert property (p_en_ignored_when_inputs_stable);

  // Coverage
  cover property (disable iff (!rst_n)  or_unary_f(value2));
  cover property (disable iff (!rst_n) !or_unary_f(value2));

  // Cover all 32 possible effective shift amounts when or_unary==0
  genvar i;
  generate
    for (i=0; i<32; i++) begin : C_SA
      cover property (disable iff (!rst_n)
        !or_unary_f(value2) && (exp_shift_amt(value2,shift_hex) == 5'(i)));
    end
  endgenerate

  // Cover both sign cases through a few representative shift amounts
  cover property (disable iff (!rst_n)
    !or_unary_f(value2) && (value1[31]==1'b0) && (exp_shift_amt(value2,shift_hex) inside {5'd0,5'd1,5'd31}));
  cover property (disable iff (!rst_n)
    !or_unary_f(value2) && (value1[31]==1'b1) && (exp_shift_amt(value2,shift_hex) inside {5'd0,5'd1,5'd31}));

  // Cover 5-bit addition wraparound case (non-zero value2[4:0] plus shift_hex wraps)
  cover property (disable iff (!rst_n)
    !or_unary_f(value2) &&
    (value2[4:0] != 5'd0) &&
    (((value2[4:0] + {1'b0,shift_hex})[4:0]) < value2[4:0]));

endmodule