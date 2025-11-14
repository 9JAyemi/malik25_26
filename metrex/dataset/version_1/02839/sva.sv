// SVA for shift_register_4bit
module shift_register_4bit_sva (
  input logic [3:0] D,
  input logic       LD,
  input logic       CLK,
  input logic       CLR,
  input logic [3:0] Q
);

  // Asynchronous clear takes immediate effect
  property p_async_reset_immediate;
    @(posedge CLR) ##0 (Q == 4'b0000);
  endproperty
  assert property (p_async_reset_immediate);

  // Reset dominates at clock edge
  assert property (@(posedge CLK) CLR |-> (Q == 4'b0000));

  // Load on clock when not reset
  assert property (@(posedge CLK) disable iff (CLR)
                   LD |=> (Q == $past(D)));

  // Rotate-left by 1 on clock when not reset and not load
  assert property (@(posedge CLK) disable iff (CLR)
                   !LD |=> (Q == {$past(Q[2:0]), $past(Q[3])}));

  // After 4 consecutive shifts, value returns to original
  assert property (@(posedge CLK) disable iff (CLR)
                   (!LD)[*4] |=> (Q == $past(Q,4)));

  // Basic functional coverage
  cover property (@(posedge CLR) ##0 (Q == 4'b0000));                            // async reset seen
  cover property (@(posedge CLK) disable iff (CLR) LD && (Q == $past(D)));       // load taken
  cover property (@(posedge CLK) disable iff (CLR) !LD &&
                  (Q == {$past(Q[2:0]), $past(Q[3])}));                          // rotate taken
  cover property (@(posedge CLK) disable iff (CLR) (!LD)[*4]);                   // 4 consecutive rotates

endmodule

// Bind the SVA to the DUT
bind shift_register_4bit shift_register_4bit_sva sva_inst (
  .D(D), .LD(LD), .CLK(CLK), .CLR(CLR), .Q(Q)
);