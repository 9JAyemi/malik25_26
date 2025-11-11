// SVA checker for RegisterAdd_parameterized8
module RegisterAdd_parameterized8_sva
(
  input logic        clk,
  input logic        rst,
  input logic        load,
  input logic [7:0]  D1,
  input logic [7:0]  D2,
  input logic [7:0]  Q,
  input logic [7:0]  reg1,
  input logic [7:0]  reg2
);

  // clocking and past-valid
  default clocking cb @(posedge clk); endclocking
  bit past_valid; initial past_valid = 0; always_ff @(posedge clk) past_valid <= 1'b1;

  // Reset behavior
  assert property (@(posedge clk) rst |-> (reg1 == 8'h00 && reg2 == 8'h00));

  // Load captures inputs into reg1/reg2 (use pre-edge values)
  assert property (disable iff (!past_valid || rst)
                   load |-> (reg1 == $past(D1) && reg2 == $past(D2)));

  // When not loading, internal regs hold
  assert property (disable iff (!past_valid || rst)
                   !load |-> (reg1 == $past(reg1) && reg2 == $past(reg2)));

  // Q updates only in the else branch (not during rst or load)
  assert property (@(posedge clk) $changed(Q) |-> (!rst && !load));

  // Functional: Q equals sum of reg1/reg2 from previous cycle when else branch executes
  assert property (disable iff (!past_valid || rst)
                   !load |-> (Q == ($past(reg1) + $past(reg2))));

  // While loading, Q is held
  assert property (disable iff (!past_valid || rst)
                   load |-> $stable(Q));

  // Control signals must be known at sampling
  assert property (@(posedge clk) !$isunknown({rst, load}));

  // Coverage: reset then load then compute
  cover property (past_valid && rst ##1 !rst ##1 load ##1 !load);

  // Coverage: consecutive loads
  cover property (disable iff (rst) load [*2]);

  // Coverage: an update cycle where addition wraps (overflow)
  cover property (disable iff (!past_valid || rst)
                  (!load && (Q < $past(reg1) || Q < $past(reg2))));

endmodule

// Bind into the DUT (accesses internal reg1/reg2)
bind RegisterAdd_parameterized8
  RegisterAdd_parameterized8_sva u_regadd8_sva
  (
    .clk  (clk),
    .rst  (rst),
    .load (load),
    .D1   (D1),
    .D2   (D2),
    .Q    (Q),
    .reg1 (reg1),
    .reg2 (reg2)
  );