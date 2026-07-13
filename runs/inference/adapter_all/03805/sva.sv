module Test6_sva (
    input logic       OE,
    input logic [3:0] Z10
);

    // No RTL clock or reset; sample on the formal global clock.

    // When OE is high, the low two bits are forced to 10.
    check_oe_high_forces_low_bits: assert property (
        @($global_clock) OE |-> (Z10[1:0] == 2'b10)
    );

    // When OE is low, the low two bits are forced to 01.
    check_oe_low_forces_low_bits: assert property (
        @($global_clock) !OE |-> (Z10[1:0] == 2'b01)
    );

    // The upper two bits are always driven to 10 when OE is high.
    check_oe_high_forces_high_bits: assert property (
        @($global_clock) OE |-> (Z10[3:2] == 2'b10)
    );

    // The upper two bits are always driven to 01 when OE is low.
    check_oe_low_forces_high_bits: assert property (
        @($global_clock) !OE |-> (Z10[3:2] == 2'b01)
    );

    // The full output bus is always 1010 regardless of OE.
    check_full_output_pattern: assert property (
        @($global_clock) Z10 == 4'b1010
    );

endmodule