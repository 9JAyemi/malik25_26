module mux_3to4_enable_sva (
  input logic clk,
  input logic reset,
  input logic enable,
  input logic [2:0] A,
  input logic [2:0] B,
  input logic [2:0] C,
  input logic [2:0] W,
  input logic [2:0] X,
  input logic [2:0] Y,
  input logic [2:0] Z
);
  // Clock: clk; Reset: reset (active-high, synchronous)
  // Logic: sequential; outputs registered on posedge clk
  // Function: if enable then W=A, X=Y=B, Z=0; else W=X=Y=0, Z=C (visible next cycle)

  // Synchronous reset drives all outputs to zero on the next cycle.
  reset_clears_outputs_next: assert property (
    @(posedge clk) reset |=> (W == 3'b000) && (X == 3'b000) && (Y == 3'b000) && (Z == 3'b000)
  );

  // W next-cycle equals A when enable is 1, else 0.
  w_next_matches_enable: assert property (
    @(posedge clk) disable iff (reset)
      1'b1 |-> ##1 (W == ($past(enable) ? $past(A) : 3'b000))
  );

  // X next-cycle equals B when enable is 1, else 0.
  x_next_matches_enable: assert property (
    @(posedge clk) disable iff (reset)
      1'b1 |-> ##1 (X == ($past(enable) ? $past(B) : 3'b000))
  );

  // Y next-cycle equals B when enable is 1, else 0.
  y_next_matches_enable: assert property (
    @(posedge clk) disable iff (reset)
      1'b1 |-> ##1 (Y == ($past(enable) ? $past(B) : 3'b000))
  );

  // Z next-cycle equals 0 when enable is 1, else C.
  z_next_matches_enable: assert property (
    @(posedge clk) disable iff (reset)
      1'b1 |-> ##1 (Z == ($past(enable) ? 3'b000 : $past(C)))
  );

  // X and Y are always equal from the next cycle onward.
  x_equals_y_next_cycle: assert property (
    @(posedge clk) disable iff (reset)
      1'b1 |-> ##1 (X == Y)
  );
endmodule