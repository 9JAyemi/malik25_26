// SVA for mux4to1
// Bind into DUT: bind mux4to1 mux4to1_sva sva_mux4to1 (.*);

module mux4to1_sva(
  input logic [3:0] A, B, C, D,
  input logic [1:0] S,
  input logic       Y
);

  default clocking cb @ (A or B or C or D or S); endclocking

  // Select must be fully known (avoid latch-on-X)
  a_sel_known: assert property ( !$isunknown(S) );

  // Functional mapping (Y is the LSB of selected input)
  a_map_00: assert property ( (S===2'b00 && !$isunknown(A[0])) |-> ##0 (Y===A[0]) );
  a_map_01: assert property ( (S===2'b01 && !$isunknown(B[0])) |-> ##0 (Y===B[0]) );
  a_map_10: assert property ( (S===2'b10 && !$isunknown(C[0])) |-> ##0 (Y===C[0]) );
  a_map_11: assert property ( (S===2'b11 && !$isunknown(D[0])) |-> ##0 (Y===D[0]) );

  // Output follows selected data in same cycle
  a_follow_A: assert property ( (S===2'b00 && $changed(A[0]) && !$isunknown(A[0])) |-> ##0 (Y===A[0] && $changed(Y)) );
  a_follow_B: assert property ( (S===2'b01 && $changed(B[0]) && !$isunknown(B[0])) |-> ##0 (Y===B[0] && $changed(Y)) );
  a_follow_C: assert property ( (S===2'b10 && $changed(C[0]) && !$isunknown(C[0])) |-> ##0 (Y===C[0] && $changed(Y)) );
  a_follow_D: assert property ( (S===2'b11 && $changed(D[0]) && !$isunknown(D[0])) |-> ##0 (Y===D[0] && $changed(Y)) );

  // No spurious Y changes: any Y change must be caused by S or the active input
  a_change_has_cause: assert property ( disable iff ($isunknown(S))
    $changed(Y) |-> ( $changed(S)
                   || (S===2'b00 && $changed(A[0]))
                   || (S===2'b01 && $changed(B[0]))
                   || (S===2'b10 && $changed(C[0]))
                   || (S===2'b11 && $changed(D[0])) ) );

  // Coverage
  c_sel_00: cover property ( S===2'b00 );
  c_sel_01: cover property ( S===2'b01 );
  c_sel_10: cover property ( S===2'b10 );
  c_sel_11: cover property ( S===2'b11 );

  c_map_00: cover property ( (S===2'b00 && !$isunknown(A[0])) ##0 (Y===A[0]) );
  c_map_01: cover property ( (S===2'b01 && !$isunknown(B[0])) ##0 (Y===B[0]) );
  c_map_10: cover property ( (S===2'b10 && !$isunknown(C[0])) ##0 (Y===C[0]) );
  c_map_11: cover property ( (S===2'b11 && !$isunknown(D[0])) ##0 (Y===D[0]) );

  c_y_rise: cover property ( !$isunknown(S) && $rose(Y) );
  c_y_fall: cover property ( !$isunknown(S) && $fell(Y) );

endmodule