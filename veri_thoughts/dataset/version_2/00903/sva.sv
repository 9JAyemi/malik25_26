module RegisterAdd_4_sva (
  input logic clk,
  input logic rst,
  input logic load,
  input logic [3:0] D,
  input logic [3:0] Q
);

  ///// Environment assumptions /////
  // Assume reset does not glitch between clock edges.
  assume_stable_reset: assume property (
    @(posedge clk) $stable(rst)
  );

  ///// Reset behavior /////
  // While reset is asserted, Q must be 0.
  reset_forces_zero: assert property (
    @(posedge clk) rst |-> (Q == 4'b0000)
  );

  ///// Load and accumulate behaviors /////
  // If load is HIGH, next Q equals current D.
  load_writes_D_to_Q: assert property (
    @(posedge clk) disable iff (rst) load |=> (Q == $past(D))
  );

  // If load is LOW, next Q equals current Q + D modulo 16.
  add_when_not_load: assert property (
    @(posedge clk) disable iff (rst) !load |=> (Q == (($past(Q) + $past(D))[3:0]))
  );

  // If load is LOW and D is 0, Q holds its value.
  hold_when_addend_zero: assert property (
    @(posedge clk) disable iff (rst) (!load && (D == 4'b0000)) |=> (Q == $past(Q))
  );

  // If load is HIGH and D is 0, Q becomes 0.
  load_zero_clears: assert property (
    @(posedge clk) disable iff (rst) (load && (D == 4'b0000)) |=> (Q == 4'b0000)
  );

  // If load is LOW and D is nonzero, Q must change (modulo 16).
  add_nonzero_changes_Q: assert property (
    @(posedge clk) disable iff (rst) (!load && (D != 4'b0000)) |=> (Q != $past(Q))
  );

  ///// Useful arithmetic corner checks (mod-16 wrap) /////
  // When Q=15 and D=1 with load LOW, next Q wraps to 0.
  wrap_15_plus_1_to_0: assert property (
    @(posedge clk) disable iff (rst) ($past(!load) && ($past(Q) == 4'hF) && ($past(D) == 4'h1)) |-> (Q == 4'h0)
  );

  // When Q=8 and D=8 with load LOW, next Q wraps to 0.
  wrap_8_plus_8_to_0: assert property (
    @(posedge clk) disable iff (rst) ($past(!load) && ($past(Q) == 4'h8) && ($past(D) == 4'h8)) |-> (Q == 4'h0)
  );

endmodule