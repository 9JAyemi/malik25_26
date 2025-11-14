// SVA for ripple_add_sub
// Bind into the DUT instance or module scope as needed.

module ripple_add_sub_sva #(parameter W=16) (
  input logic               clk,
  input logic               reset,
  input logic [W-1:0]       A,
  input logic [W-1:0]       B,
  input logic               select,
  input logic [W-1:0]       S,
  input logic               O
);

  // Helpers with reset-safe $past
  function automatic [W:0] add17(input logic [W-1:0] a, b);
    add17 = {1'b0,a} + {1'b0,b};
  endfunction
  function automatic [W:0] sub17(input logic [W-1:0] a, b);
    sub17 = {1'b0,a} + {1'b0,(~b + 1'b1)};
  endfunction

  // Reset behavior: clear and hold at zero
  property p_reset_clears;
    @(posedge clk) reset |=> (S == '0 && O == 1'b0);
  endproperty
  assert property(p_reset_clears);

  property p_reset_holds;
    @(posedge clk) reset |-> (S == '0 && O == 1'b0);
  endproperty
  assert property(p_reset_holds);

  // No X/Z on outputs when out of reset
  property p_no_xz_outputs;
    @(posedge clk) disable iff (reset) !$isunknown({S,O});
  endproperty
  assert property(p_no_xz_outputs);

  // Addition mode: result and carry-out
  property p_add_result_and_carry;
    @(posedge clk) disable iff (reset)
      (select == 1'b0) |=> {O,S} == $past(add17(A,B), 1, reset);
  endproperty
  assert property(p_add_result_and_carry);

  // Subtraction mode: result matches A + (~B+1)
  property p_sub_result;
    @(posedge clk) disable iff (reset)
      (select == 1'b1) |=> S == $past(sub17(A,B)[W-1:0], 1, reset);
  endproperty
  assert property(p_sub_result);

  // Subtraction mode: O matches DUT's intended overflow (Cout xor result sign)
  property p_sub_overflow_bit16_xor_msb;
    @(posedge clk) disable iff (reset)
      (select == 1'b1) |=> O == ($past(sub17(A,B), 1, reset)[W] ^ $past(sub17(A,B), 1, reset)[W-1]);
  endproperty
  assert property(p_sub_overflow_bit16_xor_msb);

  // Cross-check: subtraction overflow equals signed overflow formula
  property p_sub_overflow_equiv;
    @(posedge clk) disable iff (reset)
      (select == 1'b1) |-> O == ( ($past(A,1,reset)[W-1] ^ $past(B,1,reset)[W-1])
                                & ($past(A,1,reset)[W-1] ^ S[W-1]) );
  endproperty
  assert property(p_sub_overflow_equiv);

  // Basic functional covers
  // Addition: no carry
  cover property (@(posedge clk) disable iff (reset)
    (select==1'b0) |=> ($past(add17(A,B),1,reset)[W] == 1'b0));

  // Addition: with carry
  cover property (@(posedge clk) disable iff (reset)
    (select==1'b0) |=> ($past(add17(A,B),1,reset)[W] == 1'b1));

  // Subtraction: positive result (no sign)
  cover property (@(posedge clk) disable iff (reset)
    (select==1'b1) |=> (S[W-1] == 1'b0));

  // Subtraction: negative result (sign set)
  cover property (@(posedge clk) disable iff (reset)
    (select==1'b1) |=> (S[W-1] == 1'b1));

  // Subtraction: signed overflow occurs
  cover property (@(posedge clk) disable iff (reset)
    (select==1'b1) |=> O);

  // Mode toggle coverage
  cover property (@(posedge clk) disable iff (reset)
    $past(select,1,reset)==0 && select==1);
  cover property (@(posedge clk) disable iff (reset)
    $past(select,1,reset)==1 && select==0);

endmodule

// Bind into the DUT (instance or module). For module-level bind:
bind ripple_add_sub ripple_add_sub_sva #(.W(16)) sva_i (
  .clk(clk), .reset(reset), .A(A), .B(B), .select(select), .S(S), .O(O)
);