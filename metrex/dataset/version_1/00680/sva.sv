// SVA for or1200_fpu_pre_norm_mul
// Concise checks for exponent pre-sum and 24-bit significand outputs.

module or1200_fpu_pre_norm_mul_sva
  #(parameter FP_WIDTH=32, parameter FRAC_WIDTH=23, parameter EXP_WIDTH=8)
  (input  logic                      clk_i,
   input  logic [FP_WIDTH-1:0]       opa_i,
   input  logic [FP_WIDTH-1:0]       opb_i,
   input  logic [EXP_WIDTH+1:0]      exp_10_o,
   input  logic [FRAC_WIDTH:0]       fracta_24_o,
   input  logic [FRAC_WIDTH:0]       fractb_24_o);

  default clocking cb @(posedge clk_i); endclocking

  // past-valid guard for $past usage
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk_i) past_valid <= 1'b1;

  localparam int SUMW = EXP_WIDTH + 2;
  localparam logic [SUMW-1:0] BIAS = 127;

  function automatic logic [SUMW-1:0]
    exp10_ref(input logic [EXP_WIDTH-1:0] ea, input logic [EXP_WIDTH-1:0] eb);
    logic dn_a, dn_b;
    logic [SUMW-1:0] ea10, eb10;
    begin
      dn_a     = (ea == '0);
      dn_b     = (eb == '0);
      ea10     = {2'b00, ea} + dn_a;
      eb10     = {2'b00, eb} + dn_b;
      exp10_ref = ea10 + eb10 - BIAS;
    end
  endfunction

  // Core function: registered exponent sum with denorm adjustment and bias subtraction
  property p_exp10;
    past_valid |-> exp_10_o == $past(exp10_ref(opa_i[30:23], opb_i[30:23]));
  endproperty
  assert property(p_exp10);

  // 24-bit significand formation: leading 1 for normal, 0 for denorm; fraction passthrough
  assert property (fracta_24_o[FRAC_WIDTH] == (opa_i[30:23] != 8'd0));
  assert property (fractb_24_o[FRAC_WIDTH] == (opb_i[30:23] != 8'd0));
  assert property (fracta_24_o[FRAC_WIDTH-1:0] == opa_i[22:0]);
  assert property (fractb_24_o[FRAC_WIDTH-1:0] == opb_i[22:0]);

  // Combinational outputs stable if inputs stable (sanity on pure combinational paths)
  assert property ($stable(opa_i) |-> $stable(fracta_24_o));
  assert property ($stable(opb_i) |-> $stable(fractb_24_o));

  // Minimal but meaningful coverage
  cover property ((opa_i[30:23]==8'd0) && (opb_i[30:23]==8'd0)); // both denorm
  cover property ((opa_i[30:23]!=8'd0) && (opb_i[30:23]!=8'd0)); // both normal
  cover property ((opa_i[30:23]==8'd0) && (opb_i[30:23]!=8'd0)); // a denorm, b normal
  cover property ((opa_i[30:23]!=8'd0) && (opb_i[30:23]==8'd0)); // a normal, b denorm
  cover property (past_valid && exp_10_o == '0);                  // exponent sum hits zero
  cover property (past_valid && exp_10_o[SUMW-1]);                // negative (two's complement)
  cover property (past_valid && !exp_10_o[SUMW-1]);               // non-negative
  cover property (opa_i[30:23]==8'hFF || opb_i[30:23]==8'hFF);    // INF/NaN exponent inputs

endmodule

bind or1200_fpu_pre_norm_mul
  or1200_fpu_pre_norm_mul_sva #(.FP_WIDTH(FP_WIDTH),
                                .FRAC_WIDTH(FRAC_WIDTH),
                                .EXP_WIDTH(EXP_WIDTH))
  i_or1200_fpu_pre_norm_mul_sva (.*);