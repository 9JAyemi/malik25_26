module sel_to_bin_sva (
    input logic [2:0] sel,
    input logic [1:0] bin
);

    // No RTL clock or reset; sample combinational behavior on the formal global clock.

    // sel 000 maps to bin 00.
    check_sel_000_maps_to_00: assert property (
        @($global_clock) (sel == 3'b000) |-> (bin == 2'b00)
    );

    // sel 001 maps to bin 01.
    check_sel_001_maps_to_01: assert property (
        @($global_clock) (sel == 3'b001) |-> (bin == 2'b01)
    );

    // sel 010 maps to bin 10.
    check_sel_010_maps_to_10: assert property (
        @($global_clock) (sel == 3'b010) |-> (bin == 2'b10)
    );

    // sel 011 maps to bin 11.
    check_sel_011_maps_to_11: assert property (
        @($global_clock) (sel == 3'b011) |-> (bin == 2'b11)
    );

    // All upper-half selections use the default bin value 00.
    check_upper_sel_default_maps_to_00: assert property (
        @($global_clock) (sel[2] == 1'b1) |-> (bin == 2'b00)
    );

endmodule