// SVA checkers and binds for the provided DUTs

// Ripple-carry adder checks
module rca_sva (
  input [3:0] A, B, OUT
);
  // No X/Z on interface
  a_kn_in:  assert property (@(A or B) !$isunknown({A,B}));
  a_kn_out: assert property (@(OUT)     !$isunknown(OUT));

  // Functional equivalence (4-bit truncation)
  a_func:   assert property (@(A or B or OUT) OUT == ((A + B) & 4'hF));

  // Zero-latency combinational response
  a_0lat:   assert property (@(A or B or OUT)
                             $changed({A,B}) |-> ##0 (OUT == ((A + B) & 4'hF)));

  // Coverage
  c_zero:      cover property (@(A or B) (A==4'h0 && B==4'h0));
  c_overflow:  cover property (@(A or B) (A + B > 4'hF));
  c_max:       cover property (@(A or B) (A==4'hF && B==4'hF));
endmodule

bind ripple_carry_adder rca_sva rca_sva_i (.A(A), .B(B), .OUT(OUT));


// Barrel shifter checks
module bs_sva (
  input [15:0] data, q,
  input [3:0]  shift_amount,
  input        direction
);
  // No X/Z on interface
  b_kn_in:  assert property (@(data or shift_amount or direction)
                             !$isunknown({data,shift_amount,direction}));
  b_kn_out: assert property (@(q) !$isunknown(q));

  // Functional equivalence
  b_func:   assert property (@(data or shift_amount or direction or q)
                             q == (direction ? (data >> shift_amount)
                                             : (data << shift_amount)));

  // Shift-by-zero identity
  b_s0:     assert property (@(data or shift_amount or direction or q)
                             (shift_amount==0) |-> (q == data));

  // Zero-latency combinational response
  b_0lat:   assert property (@(data or shift_amount or direction or q)
                             $changed({data,shift_amount,direction}) |-> ##0
                             (q == (direction ? (data >> shift_amount)
                                              : (data << shift_amount))));

  // Coverage
  c_dir0_s0:  cover property (@(shift_amount or direction) (!direction && shift_amount==4'd0));
  c_dir0_s15: cover property (@(shift_amount or direction) (!direction && shift_amount==4'd15));
  c_dir1_s15: cover property (@(shift_amount or direction) ( direction && shift_amount==4'd15));
  c_onehot:   cover property (@(data) $onehot(data));
endmodule

bind barrel_shifter bs_sva bs_sva_i (.data(data), .shift_amount(shift_amount), .direction(direction), .q(q));


// Top-level composition checks
module top_sva (
  input [3:0]  A, B,
  input [15:0] data, q, shifted_data,
  input [3:0]  shift_amount,
  input        direction,
  input [3:0]  adder_out
);
  // No X/Z on primary inputs and output
  t_kn_in:  assert property (@(A or B or data or shift_amount or direction)
                             !$isunknown({A,B,data,shift_amount,direction}));
  t_kn_out: assert property (@(q) !$isunknown(q));

  // Composition: q = shifted_data + zero-extended adder_out
  t_comp:   assert property (@(adder_out or shifted_data or q)
                             q == (shifted_data + {12'b0, adder_out}));

  // End-to-end from inputs
  t_e2e:    assert property (@(A or B or data or shift_amount or direction or q)
                             q == ((direction ? (data >> shift_amount)
                                              : (data << shift_amount))
                                   + {12'b0, ((A + B) & 4'hF)}));

  // Zero-latency from top inputs
  t_0lat:   assert property (@(A or B or data or shift_amount or direction or q)
                             $changed({A,B,data,shift_amount,direction}) |-> ##0
                             (q == ((direction ? (data >> shift_amount)
                                               : (data << shift_amount))
                                    + {12'b0, ((A + B) & 4'hF)})));

  // Coverage: combined interesting corners
  c_overflow_dir0_maxshift: cover property (@(A or B or shift_amount or direction)
                                            (A+B > 4'hF) && !direction && (shift_amount==4'd15));
  c_dir1:                   cover property (@(direction) direction);
endmodule

bind top_module top_sva top_sva_i (
  .A(A), .B(B),
  .data(data), .shift_amount(shift_amount), .direction(direction), .q(q),
  .adder_out(adder_out), .shifted_data(shifted_data)
);