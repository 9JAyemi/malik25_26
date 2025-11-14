// SVA for twos_complement
module twos_complement_sva (input logic [3:0] A, input logic [3:0] OUT);

  // Functional correctness (delta-cycle after A changes)
  property p_twos_function;
    @(A) !$isunknown(A) |-> ##0 (OUT == (~A + 4'h1));
  endproperty
  assert property (p_twos_function);

  // Invariant: A + OUT == 0 (mod 16) whenever both are known
  property p_sum_zero;
    @(A or OUT) (!$isunknown(A) && !$isunknown(OUT)) |-> ##0 ((A + OUT) == 4'h0);
  endproperty
  assert property (p_sum_zero);

  // OUT shall not be X/Z when A is known
  property p_no_x_out;
    @(A or OUT) !$isunknown(A) |-> ##0 !$isunknown(OUT);
  endproperty
  assert property (p_no_x_out);

  // OUT changes only due to a change on A (this or immediately prior event)
  property p_out_change_has_cause;
    @(A or OUT) $changed(OUT) |-> ($changed(A) or $past($changed(A)));
  endproperty
  assert property (p_out_change_has_cause);

  // Corner-case coverage
  cover property (@(A) ##0 (A == 4'h0 && OUT == 4'h0)); // -0=0
  cover property (@(A) ##0 (A == 4'h8 && OUT == 4'h8)); // self-inverse
  cover property (@(A) ##0 (A == 4'hF && OUT == 4'h1)); // max magnitude

  // Bit toggle coverage on A
  genvar i;
  generate
    for (i=0; i<4; i++) begin : a_toggles
      cover property (@(posedge A[i]) 1);
      cover property (@(negedge A[i]) 1);
    end
  endgenerate

endmodule

bind twos_complement twos_complement_sva sva_i (.A(A), .OUT(OUT));