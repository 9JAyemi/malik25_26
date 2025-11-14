// SVA for sky130_fd_sc_hd__bufinv: Y should be logical NOT of A
module sky130_fd_sc_hd__bufinv_sva (input logic A, input logic Y);

  // Functional correctness on output activity; tolerant of gate delays
  property p_y_equals_not_a_on_y_edges;
    @(posedge Y or negedge Y)
      !$isunknown({A,Y}) && (Y === ~A);
  endproperty
  assert property (p_y_equals_not_a_on_y_edges)
    else $error("bufinv SVA: Y != ~A (or X/Z) when Y changed");

  // No spurious X/Z on Y when A is known
  property p_no_spurious_x_on_y;
    @(posedge Y or negedge Y or posedge A or negedge A)
      $isunknown(Y) |-> $isunknown(A);
  endproperty
  assert property (p_no_spurious_x_on_y)
    else $error("bufinv SVA: Y is X/Z while A is known");

  // Coverage: both output edges observed
  cover property (@(posedge Y) 1);
  cover property (@(negedge Y) 1);

  // Coverage: both valid steady states observed
  cover property (@(posedge Y or negedge Y) !$isunknown({A,Y}) && (A==0 && Y==1));
  cover property (@(posedge Y or negedge Y) !$isunknown({A,Y}) && (A==1 && Y==0));

endmodule

bind sky130_fd_sc_hd__bufinv sky130_fd_sc_hd__bufinv_sva bufinv_sva_i (.A(A), .Y(Y));