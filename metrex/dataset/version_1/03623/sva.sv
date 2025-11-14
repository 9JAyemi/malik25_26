// SVA for acl_fp_fptosi
// Bind into the DUT so we can see internals.
bind acl_fp_fptosi acl_fp_fptosi_sva sva();

module acl_fp_fptosi_sva;

  // Default clock/reset
  default clocking cb @(posedge clock); endclocking
  default disable iff (!resetn);

  // Helper reference function (matches DUT semantics)
  function automatic logic [31:0] ref_fptosi(input logic [31:0] din);
    logic       sign;
    logic [7:0] exp;
    logic [22:0] frac;
    logic [23:0] imp;
    logic [7:0]  E;
    logic [30:0] man1, mag;
    logic [31:0] val;
    {sign,exp,frac} = din;
    imp = {1'b1, frac};
    if (exp < 8'd127) begin
      man1 = 31'd0; E = 8'd0;
    end else begin
      man1 = {imp, 7'd0}; E = exp - 8'd127;
    end
    if (E <= 8'd30) mag = (man1 >> (30 - E));
    else            mag = 31'h7FFF_FFFF;
    val = {1'b0, mag};
    if (sign) val = (~val) + 32'd1;
    return val;
  endfunction

  // Basic structural checks
  assert property (1 |-> ({sign_0, exp_0, man_0} == dataa));
  assert property (1 |-> (implied_man_0 == {1'b1, man_0}));
  assert property (result == result_3);

  // Reset values (checked even during reset)
  assert property (@(posedge clock) !resetn |-> (sign_1==0 && man_1==0 && shift_amount_1==0
                                              && sign_2==0 && result_2==0 && result_3==0));

  // Hold when enable deasserted
  assert property (!enable |=> $stable({sign_1, man_1, shift_amount_1, sign_2, result_2, result_3}));

  // Stage 1: decode/prepare
  assert property (enable |-> (sign_1 == sign_0));
  assert property (enable && (exp_0 < 8'd127) |-> (man_1==31'd0 && shift_amount_1==8'd0));
  assert property (enable && (exp_0 >= 8'd127) |-> (man_1=={implied_man_0,7'd0} && shift_amount_1==exp_0-8'd127));

  // Stage 2: shift/saturate
  assert property (enable |-> (sign_2 == sign_1));
  assert property (enable && (shift_amount_1 <= 8'd30)
                   |-> (result_2 == (man_1 >> (30 - shift_amount_1))));
  assert property (enable && (shift_amount_1 > 8'd30)
                   |-> (result_2 == 31'h7FFF_FFFF));

  // Stage 3: apply sign (two's complement)
  assert property (enable |-> (result_3 == (sign_2 ? ((~{1'b0,result_2}) + 32'd1)
                                                    :  ({1'b0,result_2}))));

  // End-to-end check for 3 consecutive enables
  assert property (enable ##1 enable ##1 enable |-> result == ref_fptosi($past(dataa,2)));

  // Corner-case assertions
  // Exactly E=0 -> magnitude is 1
  assert property (enable && (exp_0==8'd127) |=> (result_2==31'd1));
  // Large exponent saturates
  assert property (enable && (exp_0>=8'd158) ##1 enable ##1 enable
                   |-> (result == (sign_0 ? 32'hFF80_0001 : 32'h007F_FFFF)));

  // Functional coverage
  cover property (enable && (exp_0 < 8'd127));            // tiny -> 0
  cover property (enable && (exp_0 == 8'd127));           // E=0
  cover property (enable && (exp_0 == 8'd150));           // E=23
  cover property (enable && (exp_0 == 8'd157));           // E=30
  cover property (enable && (exp_0 >= 8'd158));           // saturate
  cover property (enable && sign_0);                      // negative path
  cover property (enable ##1 enable ##1 enable
                  && ($past(exp_0,2) >= 8'd127) && !$past(sign_0,2)); // + path full latency
  cover property (enable ##1 enable ##1 enable
                  && ($past(exp_0,2) >= 8'd127) &&  $past(sign_0,2)); // - path full latency
  cover property (enable && (exp_0==8'd0) && (man_0!=0)); // subnormal treated as 0
  cover property (!enable [*3]);                          // stall scenario

endmodule