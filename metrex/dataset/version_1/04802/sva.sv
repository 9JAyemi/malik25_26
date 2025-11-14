// SVA for MUX4X1
// Assumes a free-running clk and active-high rst_n for sampling.
// Bind example (edit clock/reset names as needed):
//   bind MUX4X1 MUX4X1_sva u_mux4x1_sva(.clk(tb_clk), .rst_n(tb_rst_n), .*);

module MUX4X1_sva(
  input logic              clk,
  input logic              rst_n,
  // DUT ports
  input logic [3:0]        A, B, C, D,
  input logic [1:0]        S0, S1,
  input logic              Y
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Functional equivalence (matches DUT semantics inc. X-propagation and truncation to LSB)
  // Note: Only bit [0] of A/B/C/D affects Y due to DUT widths.
  property p_func;
    Y === ((S0 == 2'b00)
            ? ((S1 == 2'b00) ? A[0] : B[0])
            : ((S1 == 2'b00) ? C[0] : D[0]));
  endproperty
  ap_func: assert property (p_func)
    else $error("MUX4X1 functional mismatch");

  // Basic X/Z hygiene
  ap_no_x_sel: assert property (!$isunknown(S0) && !$isunknown(S1))
    else $error("MUX4X1 select lines contain X/Z");

  ap_no_x_y: assert property (!$isunknown(Y))
    else $error("MUX4X1 output Y is X/Z");

  // Selected data must be known when used
  ap_no_x_A_when_sel: assert property ((S0==2'b00 && S1==2'b00) |-> !$isunknown(A[0]))
    else $error("MUX4X1 A[0] X/Z when selected");
  ap_no_x_B_when_sel: assert property ((S0==2'b00 && S1!=2'b00) |-> !$isunknown(B[0]))
    else $error("MUX4X1 B[0] X/Z when selected");
  ap_no_x_C_when_sel: assert property ((S0!=2'b00 && S1==2'b00) |-> !$isunknown(C[0]))
    else $error("MUX4X1 C[0] X/Z when selected");
  ap_no_x_D_when_sel: assert property ((S0!=2'b00 && S1!=2'b00) |-> !$isunknown(D[0]))
    else $error("MUX4X1 D[0] X/Z when selected");

  // Stability: if selects are stable and the selected input LSB is stable, Y must be stable
  ap_stable: assert property (
    $stable(S0) && $stable(S1) &&
    ((S0==2'b00 && S1==2'b00) ? $stable(A[0]) :
     (S0==2'b00 && S1!=2'b00) ? $stable(B[0]) :
     (S0!=2'b00 && S1==2'b00) ? $stable(C[0]) :
                                $stable(D[0]))
    |-> $stable(Y)
  ) else $error("MUX4X1 Y unstable despite stable selects and selected input");

  // Minimal functional coverage: hit each selection path and observe correct Y
  cp_sel_A: cover property (S0==2'b00 && S1==2'b00 && Y===A[0]);
  cp_sel_B: cover property (S0==2'b00 && S1!=2'b00 && Y===B[0]);
  cp_sel_C: cover property (S0!=2'b00 && S1==2'b00 && Y===C[0]);
  cp_sel_D: cover property (S0!=2'b00 && S1!=2'b00 && Y===D[0]);

endmodule