module my_nand3_sva (
    input logic o,
    input logic i0,
    input logic i1,
    input logic i2
);

    // o matches the RTL's nested NAND implementation.
    check_output_nested_nand: assert property (
        @($global_clock) o == ~(~(i0 & i1) & i2)
    );

    // When i2 is low, the output is forced high.
    check_i2_low_forces_high: assert property (
        @($global_clock) (i2 == 1'b0) |-> (o == 1'b1)
    );

    // When i2 is high, the output equals i0 AND i1.
    check_i2_high_reduces_to_and: assert property (
        @($global_clock) (i2 == 1'b1) |-> (o == (i0 & i1))
    );

    // If both i0 and i1 are high, the output is high.
    check_i0_i1_high_drive_high: assert property (
        @($global_clock) ((i0 == 1'b1) && (i1 == 1'b1)) |-> (o == 1'b1)
    );

    // If i2 is high and i0 is low, the output is low.
    check_i2_high_i0_low_drives_low: assert property (
        @($global_clock) ((i2 == 1'b1) && (i0 == 1'b0)) |-> (o == 1'b0)
    );

    // If i2 is high and i1 is low, the output is low.
    check_i2_high_i1_low_drives_low: assert property (
        @($global_clock) ((i2 == 1'b1) && (i1 == 1'b0)) |-> (o == 1'b0)
    );

    // A low output only occurs when i2 is high and at least one input is low.
    check_output_low_condition: assert property (
        @($global_clock) (o == 1'b0) |-> ((i2 == 1'b1) && ((i0 == 1'b0) || (i1 == 1'b0)))
    );

endmodule