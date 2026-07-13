module Span12Mux_s5_v_sva (
    input logic [11:0] I,
    input logic O
);

    // O matches the one-hot decode implemented in the RTL.
    check_output_matches_decode: assert property (
        @($global_clock)
        O == ((I == 12'b000000000001) ||
              (I == 12'b000000000100) ||
              (I == 12'b000000010000) ||
              (I == 12'b000001000000) ||
              (I == 12'b000100000000) ||
              (I == 12'b010000000000))
    );

    // Enabled one-hot input values drive O high.
    check_enabled_onehot_values_drive_high: assert property (
        @($global_clock)
        ((I == 12'b000000000001) ||
         (I == 12'b000000000100) ||
         (I == 12'b000000010000) ||
         (I == 12'b000001000000) ||
         (I == 12'b000100000000) ||
         (I == 12'b010000000000)) |-> (O == 1'b1)
    );

    // Disabled one-hot input values drive O low.
    check_disabled_onehot_values_drive_low: assert property (
        @($global_clock)
        ((I == 12'b000000000010) ||
         (I == 12'b000000001000) ||
         (I == 12'b000000100000) ||
         (I == 12'b000010000000) ||
         (I == 12'b001000000000) ||
         (I == 12'b100000000000)) |-> (O == 1'b0)
    );

    // Inputs outside the listed one-hot values drive O low.
    check_non_onehot_values_drive_low: assert property (
        @($global_clock)
        !((I == 12'b000000000001) ||
          (I == 12'b000000000010) ||
          (I == 12'b000000000100) ||
          (I == 12'b000000001000) ||
          (I == 12'b000000010000) ||
          (I == 12'b000000100000) ||
          (I == 12'b000001000000) ||
          (I == 12'b000010000000) ||
          (I == 12'b000100000000) ||
          (I == 12'b001000000000) ||
          (I == 12'b010000000000) ||
          (I == 12'b100000000000)) |-> (O == 1'b0)
    );

    // A high output can only come from an enabled one-hot input value.
    check_output_high_implies_enabled_onehot_value: assert property (
        @($global_clock)
        O |-> ((I == 12'b000000000001) ||
               (I == 12'b000000000100) ||
               (I == 12'b000000010000) ||
               (I == 12'b000001000000) ||
               (I == 12'b000100000000) ||
               (I == 12'b010000000000))
    );

endmodule