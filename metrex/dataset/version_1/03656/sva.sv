// SVA for addition_module
module addition_module_sva (
  input logic        clk,
  input logic        reset,
  input logic [7:0]  A,
  input logic [7:0]  B,
  input logic [15:0] C
);
  default clocking cb @(posedge clk); endclocking

  // Next-state function: on previous cycle reset -> 0, else sum of previous A,B (zero-extended)
  property p_reset_updates_zero;
    $past(reset) |-> (C == 16'h0000);
  endproperty
  assert property (p_reset_updates_zero)
    else $error("C must be 0 one cycle after reset=1");

  property p_sum_updates_correctly;
    !$past(reset) |-> (C == ($past({8'b0,A}) + $past({8'b0,B})));
  endproperty
  assert property (p_sum_updates_correctly)
    else $error("C must equal zero-extended A+B from previous cycle when reset=0");

  // Optional sanity: while reset remains asserted, C stays 0
  assert property (reset |-> ##1 (C == 16'h0000))
    else $error("C must remain 0 while reset is held");

  // Functional coverage
  cover property (reset);                                 // saw reset
  cover property ($past(reset) && (C == 16'h0000));       // observed reset effect
  cover property (!$past(reset) &&
                  (C == ($past({8'b0,A}) + $past({8'b0,B})))); // observed a valid sum
  cover property (!$past(reset) &&
                  ($past(A)==8'h00) && ($past(B)==8'h00) &&
                  (C==16'h0000));                         // 0 + 0 -> 0
  cover property (!$past(reset) &&
                  ($past(A)==8'hFF) && ($past(B)==8'hFF) &&
                  (C==16'd510));                          // 255 + 255 -> 510
endmodule

bind addition_module addition_module_sva
  (.clk(clk), .reset(reset), .A(A), .B(B), .C(C));