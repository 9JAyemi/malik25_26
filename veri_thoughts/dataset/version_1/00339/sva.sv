module xor_system_sva (
    input logic a,
    input logic b,
    input logic out
);

    // Out matches the implemented not/xor datapath.
    check_out_matches_implemented_datapath: assert property (
        @($global_clock) out == ((~a) ^ b)
    );

    // Equal inputs drive the output high.
    check_equal_inputs_drive_high: assert property (
        @($global_clock) (a == b) |-> (out == 1'b1)
    );

    // Different inputs drive the output low.
    check_different_inputs_drive_low: assert property (
        @($global_clock) (a != b) |-> (out == 1'b0)
    );

    // With a low, the output is the inversion of b.
    check_a_low_inverts_b: assert property (
        @($global_clock) (!a) |-> (out == (~b))
    );

    // With a high, the output follows b.
    check_a_high_follows_b: assert property (
        @($global_clock) a |-> (out == b)
    );

    // With b low, the output is the inversion of a.
    check_b_low_inverts_a: assert property (
        @($global_clock) (!b) |-> (out == (~a))
    );

    // With b high, the output follows a.
    check_b_high_follows_a: assert property (
        @($global_clock) b |-> (out == a)
    );

    // Both inputs low produce a high output.
    check_00_maps_to_1: assert property (
        @($global_clock) ((!a) && (!b)) |-> (out == 1'b1)
    );

    // Only a high produces a low output.
    check_10_maps_to_0: assert property (
        @($global_clock) (a && (!b)) |-> (out == 1'b0)
    );

    // Only b high produces a low output.
    check_01_maps_to_0: assert property (
        @($global_clock) ((!a) && b) |-> (out == 1'b0)
    );

    // Both inputs high produce a high output.
    check_11_maps_to_1: assert property (
        @($global_clock) (a && b) |-> (out == 1'b1)
    );

endmodule