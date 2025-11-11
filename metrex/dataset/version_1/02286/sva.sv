// SVA checker for binary_counter
module binary_counter_sva (
  input logic        clk,
  input logic [3:0]  Q,
  input logic [3:0]  Q_reg1,
  input logic [3:0]  Q_reg2,
  input logic [3:0]  Q_reg3
);

  default clocking cb @(posedge clk); endclocking

  // helper for modulo-16 increment
  function automatic logic [3:0] incr4 (input logic [3:0] x);
    incr4 = (x == 4'hF) ? 4'h0 : x + 4'h1;
  endfunction

  // Pipeline stage checks (1-cycle shifts)
  assert property (!$isunknown($past(Q))      |-> (Q_reg1 == $past(Q)));
  assert property (!$isunknown($past(Q_reg1)) |-> (Q_reg2 == $past(Q_reg1)));
  assert property (!$isunknown($past(Q_reg2)) |-> (Q_reg3 == $past(Q_reg2)));

  // Counter update from 3rd pipeline stage
  assert property (!$isunknown(Q_reg3) |-> (Q == incr4(Q_reg3)));

  // End-to-end functional behavior: Q(t) = Q(t-4) + 1 (mod 16)
  assert property (!$isunknown($past(Q,4)) |-> (Q == incr4($past(Q,4))));

  // Safety: avoid X on observable output once 4-cycle history exists
  assert property (!$isunknown($past(Q,4)) |-> !$isunknown(Q));

  // Coverage: normal increment and wrap
  cover property (!$isunknown($past(Q,4)) && ($past(Q,4) != 4'hF) && (Q == $past(Q,4) + 4'h1));
  cover property (!$isunknown($past(Q,4)) && ($past(Q,4) == 4'hF) && (Q == 4'h0));

  // Coverage: see all 16 states on Q
  generate
    genvar v;
    for (v = 0; v < 16; v++) begin : CODES
      cover property (Q == v[3:0]);
    end
  endgenerate

endmodule

// Bind into the DUT (connects to internal regs by name)
bind binary_counter binary_counter_sva u_binary_counter_sva (.*);