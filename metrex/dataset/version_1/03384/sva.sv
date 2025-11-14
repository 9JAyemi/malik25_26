// SVA for mux_4to1 (bindable checker)
// Notes: DUT drives 1-bit Y from 4-bit A/B/C/D; assertions check LSB routing.
// Uses event-based sampling with ##0 to allow combinational settle.

module mux_4to1_sva (
  input logic [3:0] A, B, C, D,
  input logic [1:0] S,
  input logic       Y
);

  function automatic logic exp_y;
    unique case (S)
      2'b00: exp_y = A[0];
      2'b01: exp_y = B[0];
      2'b10: exp_y = C[0];
      2'b11: exp_y = D[0];
      default: exp_y = 1'bx;
    endcase
  endfunction

  // Select must be 2-state (avoid latch behavior on X/Z)
  a_sel_2state: assert property (@(S) !$isunknown(S));

  // Correct muxing: Y equals selected input LSB after delta
  a_mux_func: assert property (@(A or B or C or D or S)
                               !$isunknown(S) |-> ##0 (Y === exp_y()));

  // If selected data bit is known, Y must be known and equal
  a_no_x_on_y: assert property (@(A or B or C or D or S)
                                (!$isunknown(S) && !$isunknown(exp_y())) |-> ##0 (Y === exp_y()));

  // Functional coverage: each select value exercised with correct output
  c_sel_00: cover property (@(S) (S==2'b00) ##0 (Y===A[0]));
  c_sel_01: cover property (@(S) (S==2'b01) ##0 (Y===B[0]));
  c_sel_10: cover property (@(S) (S==2'b10) ##0 (Y===C[0]));
  c_sel_11: cover property (@(S) (S==2'b11) ##0 (Y===D[0]));

  // Optional: observe select transitions
  c_sel_change: cover property (@(S) $changed(S));

endmodule

bind mux_4to1 mux_4to1_sva u_mux_4to1_sva(.A(A),.B(B),.C(C),.D(D),.S(S),.Y(Y));