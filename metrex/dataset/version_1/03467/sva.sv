// SVA for top_module and its combinational sub-functions.
// Concise, high-quality checks with essential coverage.

module top_module_sva
(
  input logic        clk,
  input logic [3:0]  D,
  input logic        SEL,
  input logic [3:0]  OUT,
  input logic [3:0]  Y,
  input logic [3:0]  C,
  input logic [3:0]  ADD_OUT
);

  default clocking @(posedge clk); endclocking

  // Helpers
  let known_inputs        = !$isunknown({SEL,D});
  let known_dec_inputs    = !$isunknown({D[3],SEL});
  let known_comb_all      = !$isunknown({D,SEL,Y,C,ADD_OUT});

  // Decoder: mapping and one-hot when inputs known
  assert property (known_dec_inputs |-> (Y === (4'b0001 << {D[3],SEL})));
  assert property (known_dec_inputs |-> $onehot(Y));

  // Two's complement converter: exact function
  assert property (!$isunknown(D) |-> (C === (~D + 4'b0001)));
  // Equivalently, modulo-16 sum must be zero
  assert property (!$isunknown(D) |-> ((D + C) [3:0] == 4'b0000));

  // Adder: exact function (4-bit truncation)
  assert property (!$isunknown({Y,C}) |-> (ADD_OUT === ({1'b0,Y} + {1'b0,C})[3:0]));

  // Top selection behavior on the clock edge
  // SEL==0 path: OUT mirrors indexed Y bit, zero-extended to 4 bits
  assert property (known_inputs && !$isunknown(Y) && !SEL
                   |=> (OUT === {3'b000, Y[D[1:0]]}));
  // Ensure indexed bit is known when inputs are known
  assert property (!$isunknown({Y,D[1:0]}) |-> !$isunknown(Y[D[1:0]]));
  // OUT constrained to 0 or 1 on SEL==0 path
  assert property (known_inputs && !SEL |=> (OUT inside {4'h0,4'h1}));

  // SEL==1 path: OUT equals ADD_OUT
  assert property (known_inputs && SEL && !$isunknown(ADD_OUT) |=> (OUT === ADD_OUT));

  // End-to-end arithmetic consistency (Y + two's_comp(D)) == ADD_OUT and (ADD_OUT + D) == Y (mod 16)
  assert property (known_comb_all |-> (ADD_OUT === ({1'b0,Y} + {1'b0,C})[3:0]));
  assert property (known_comb_all |-> ((({1'b0,ADD_OUT} + {1'b0,D})[3:0]) === Y));

  // Output should not be X when inputs are known at the sampling edge
  assert property (known_inputs |-> !$isunknown(OUT));

  // Minimal but useful coverage
  cover property (SEL==0);
  cover property (SEL==1);
  cover property (Y == 4'b0001);
  cover property (Y == 4'b0010);
  cover property (Y == 4'b0100);
  cover property (Y == 4'b1000);
  // Exercise the SEL==0 path producing 1
  cover property (!SEL && (D[1:0] == {D[3],SEL}));
  // Exercise adder overflow
  cover property (({1'b0,Y} + {1'b0,C})[4] == 1'b1);

endmodule

// Bind to DUT
bind top_module top_module_sva i_top_module_sva
(
  .clk     (clk),
  .D       (D),
  .SEL     (SEL),
  .OUT     (OUT),
  .Y       (Y),
  .C       (C),
  .ADD_OUT (ADD_OUT)
);