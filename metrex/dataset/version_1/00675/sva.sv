// SVA for sky130_fd_sc_ls__nor2 / sky130_fd_sc_ls__nor2_1
// Concise, full functional checking with coverage

module sky130_nor2_sva (input logic A, B, Y);

  // Sample on any edge of inputs or output
  localparam string ID = "sky130_nor2_sva";
  `define NOR2_EVT (posedge A or negedge A or posedge B or negedge B or posedge Y or negedge Y)

  // Functional equivalence (4-state aware)
  a_func: assert property (@(`NOR2_EVT) (Y === ~(A | B)))
    else $error("%s: NOR2 functional mismatch: Y=%b A=%b B=%b", ID, Y, A, B);

  // Known outputs from known inputs
  a_known: assert property (@(`NOR2_EVT) (!$isunknown({A,B})) |-> !$isunknown(Y))
    else $error("%s: Y is X/Z while inputs are known: A=%b B=%b Y=%b", ID, A, B, Y);

  // Output changes only when at least one input changes
  a_causality: assert property (@(`NOR2_EVT) $changed(Y) |-> ($changed(A) || $changed(B)))
    else $error("%s: Y changed without A/B change: A=%b B=%b Y=%b", ID, A, B, Y);

  // Truth-table coverage
  c_tt00: cover property (@(`NOR2_EVT) (A==0 && B==0 && Y==1));
  c_tt01: cover property (@(`NOR2_EVT) (A==0 && B==1 && Y==0));
  c_tt10: cover property (@(`NOR2_EVT) (A==1 && B==0 && Y==0));
  c_tt11: cover property (@(`NOR2_EVT) (A==1 && B==1 && Y==0));

  // Output toggle coverage
  c_y_rise: cover property (@(`NOR2_EVT) $rose(Y));
  c_y_fall: cover property (@(`NOR2_EVT) $fell(Y));

  // Simultaneous input change coverage
  c_ab_same_cycle: cover property (@(`NOR2_EVT) $changed(A) && $changed(B));

  `undef NOR2_EVT
endmodule

// Bind to both the base cell and the wrapper
bind sky130_fd_sc_ls__nor2     sky130_nor2_sva nor2_sva_i (.A(A), .B(B), .Y(Y));
bind sky130_fd_sc_ls__nor2_1   sky130_nor2_sva nor2_1_sva_i (.A(A), .B(B), .Y(Y));