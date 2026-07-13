module section2_schematic_sva (
    input logic n63,
    input logic Z_B,
    input logic n62,
    input logic Len_int,
    input logic Ren_int
);

    // Len_int is the OR of the two product terms.
    check_len_int_function: assert property (
        @($global_clock) Len_int == ((n63 & Z_B) | ((~n63) & (~n62) & (~Z_B)))
    );

    // Ren_int is the OR of the two product terms.
    check_ren_int_function: assert property (
        @($global_clock) Ren_int == ((~n63) & (~n62) & (~Z_B)) | ((~n63) & (~n62) & (Z_B))
    );

    // When Z_B is low, both outputs must be low.
    check_zb_low_forces_outputs_low: assert property (
        @($global_clock) (Z_B == 1'b0) |-> ((Len_int == 1'b0) && (Ren_int == 1'b0))
    );

    // When n62 is low, both outputs must be low.
    check_n62_low_forces_outputs_low: assert property (
        @($global_clock) (n62 == 1'b0) |-> ((Len_int == 1'b0) && (Ren_int == 1'b0))
    );

    // When n63 is high, Len_int must be high.
    check_n63_high_sets_len_int: assert property (
        @($global_clock) (n63 == 1'b1) |-> (Len_int == 1'b1)
    );

    // When n63 is low, Ren_int must be high.
    check_n63_low_sets_ren_int: assert property (
        @($global_clock) (n63 == 1'b0) |-> (Ren_int == 1'b1)
    );

    // When Z_B is high, Len_int must be high.
    check_zb_high_sets_len_int: assert property (
        @($global_clock) (Z_B == 1'b1) |-> (Len_int == 1'b1)
    );

    // When n62 is high, Ren_int must be high.
    check_n62_high_sets_ren_int: assert property (
        @($global_clock) (n62 == 1'b1) |-> (Ren_int == 1'b1)
    );

endmodule