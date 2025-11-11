// Bind these SVA to the DUT
bind barrel_shifter barrel_shifter_sva sva_inst (.*);

module barrel_shifter_sva (
  input [3:0] A,
  input [1:0] shift_amount,
  input       shift_dir,
  input [3:0] Y
);

  // Sample on any combinational change
  event comb_ev;
  always @* -> comb_ev;

  // Golden model
  function automatic [3:0] exp_y(input [3:0] a, input [1:0] sa, input sd);
    exp_y = sd ? (a << sa) : (a >> sa);
  endfunction

  // No-X propagation: if inputs are known, output must be known
  assert property (@(comb_ev)
    !$isunknown({A,shift_amount,shift_dir}) |-> !$isunknown(Y)
  );

  // Functional correctness: logical shift with zero-fill
  assert property (@(comb_ev)
    disable iff ($isunknown({A,shift_amount,shift_dir}))
    Y == exp_y(A, shift_amount, shift_dir)
  );

  // Key edge cases
  assert property (@(comb_ev)
    disable iff ($isunknown({A,shift_amount,shift_dir}))
    (shift_amount == 2'd0) |-> (Y == A)
  );

  assert property (@(comb_ev)
    disable iff ($isunknown({A,shift_amount,shift_dir}))
    (shift_amount == 2'd3 &&  shift_dir) |-> (Y == {A[0],3'b000})
  );

  assert property (@(comb_ev)
    disable iff ($isunknown({A,shift_amount,shift_dir}))
    (shift_amount == 2'd3 && !shift_dir) |-> (Y == {3'b000,A[3]})
  );

  // Functional coverage: all dir/amount combos seen with known inputs
  cover property (@(comb_ev) !$isunknown({A,shift_amount,shift_dir}) && (shift_dir==0) && (shift_amount==2'd0));
  cover property (@(comb_ev) !$isunknown({A,shift_amount,shift_dir}) && (shift_dir==0) && (shift_amount==2'd1));
  cover property (@(comb_ev) !$isunknown({A,shift_amount,shift_dir}) && (shift_dir==0) && (shift_amount==2'd2));
  cover property (@(comb_ev) !$isunknown({A,shift_amount,shift_dir}) && (shift_dir==0) && (shift_amount==2'd3));
  cover property (@(comb_ev) !$isunknown({A,shift_amount,shift_dir}) && (shift_dir==1) && (shift_amount==2'd0));
  cover property (@(comb_ev) !$isunknown({A,shift_amount,shift_dir}) && (shift_dir==1) && (shift_amount==2'd1));
  cover property (@(comb_ev) !$isunknown({A,shift_amount,shift_dir}) && (shift_dir==1) && (shift_amount==2'd2));
  cover property (@(comb_ev) !$isunknown({A,shift_amount,shift_dir}) && (shift_dir==1) && (shift_amount==2'd3));

  // Targeted edge-data coverage to observe zero-fill behavior
  cover property (@(comb_ev) !$isunknown({A,shift_amount,shift_dir}) && A==4'b1000 &&  shift_dir && (shift_amount inside {[1:3]}));
  cover property (@(comb_ev) !$isunknown({A,shift_amount,shift_dir}) && A==4'b0001 && !shift_dir && (shift_amount inside {[1:3]}));

endmodule