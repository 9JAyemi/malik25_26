// SVA for decoder: concise, full functional checking and coverage.
// Bind into the DUT (no changes to DUT required).

module decoder_sva (
  input  logic [2:0] ABC,
  input  logic [7:0] Y
);

  // Functional equivalence: for known ABC, Y must be exactly 1 << ABC (same-cycle)
  ap_decode_eq: assert property (@(ABC or Y)
    !$isunknown(ABC) |-> ##0 (Y == (8'b1 << ABC))
  );

  // Y is always zero-or-one-hot (never more than one bit set)
  ap_onehot0: assert property (@(ABC or Y) $onehot0(Y));

  // Y must never contain X/Z
  ap_y_known: assert property (@(ABC or Y) !$isunknown(Y));

  // The default branch is only taken when ABC is X/Z (Y == 0 iff ABC unknown)
  ap_zero_only_when_abc_unknown: assert property (@(ABC or Y)
    (Y == 8'b0) |-> ##0 $isunknown(ABC)
  );

  // Coverage: see every valid input value produce the corresponding one-hot output
  generate
    genvar i;
    for (i = 0; i < 8; i++) begin : cov_decodes
      cp_map_i: cover property (@(ABC or Y)
        (!$isunknown(ABC) && ABC == i) ##0 (Y == (8'b1 << i))
      );
    end
  endgenerate

  // Coverage: observe unknown input drives default zero
  cp_unknown_to_zero: cover property (@(ABC or Y)
    $isunknown(ABC) ##0 (Y == 8'b0)
  );

endmodule

bind decoder decoder_sva u_decoder_sva (.ABC(ABC), .Y(Y));