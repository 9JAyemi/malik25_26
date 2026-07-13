module mask_generator_sva (
    input logic [9:0] id0_m,
    input logic [9:0] id1_m,
    input logic [9:0] id2_m,
    input logic [9:0] id3_m,
    input logic [3:0] mask_id
);

    // No RTL clock or reset; sample the combinational interface on the formal global clock.

    // mask_id[0] must equal the reduction XOR of id0_m.
    check_mask0_parity: assert property (
        @($global_clock) mask_id[0] == ^id0_m
    );

    // mask_id[1] must equal the reduction XOR of id1_m.
    check_mask1_parity: assert property (
        @($global_clock) mask_id[1] == ^id1_m
    );

    // mask_id[2] must equal the reduction XOR of id2_m.
    check_mask2_parity: assert property (
        @($global_clock) mask_id[2] == ^id2_m
    );

    // mask_id[3] must equal the reduction XOR of id3_m.
    check_mask3_parity: assert property (
        @($global_clock) mask_id[3] == ^id3_m
    );

    // mask_id[0] must remain stable when id0_m remains stable.
    check_mask0_stable_when_id0_stable: assert property (
        @($global_clock) $stable(id0_m) |-> $stable(mask_id[0])
    );

    // mask_id[1] must remain stable when id1_m remains stable.
    check_mask1_stable_when_id1_stable: assert property (
        @($global_clock) $stable(id1_m) |-> $stable(mask_id[1])
    );

    // mask_id[2] must remain stable when id2_m remains stable.
    check_mask2_stable_when_id2_stable: assert property (
        @($global_clock) $stable(id2_m) |-> $stable(mask_id[2])
    );

    // mask_id[3] must remain stable when id3_m remains stable.
    check_mask3_stable_when_id3_stable: assert property (
        @($global_clock) $stable(id3_m) |-> $stable(mask_id[3])
    );

endmodule