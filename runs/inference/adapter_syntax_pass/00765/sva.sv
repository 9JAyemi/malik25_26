module mux_4to1_sva (
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] sel,
    input logic enable,
    input logic [3:0] out
);

    // When sel is 00 and enable is high, out must equal in0.
    check_sel_00_enabled_routes_in0: assert property (
        @($global_clock) (sel == 2'b00 && enable) |-> (out == in0)
    );

    // When sel is 00 and enable is low, out must be zero.
    check_sel_00_disabled_drives_zero: assert property (
        @($global_clock) (sel == 2'b00 && !enable) |-> (out == 4'b0000)
    );

    // When sel is 01 and enable is high, out must equal in1.
    check_sel_01_enabled_routes_in1: assert property (
        @($global_clock) (sel == 2'b01 && enable) |-> (out == in1)
    );

    // When sel is 01 and enable is low, out must be zero.
    check_sel_01_disabled_drives_zero: assert property (
        @($global_clock) (sel == 2'b01 && !enable) |-> (out == 4'b0000)
    );

    // When sel is 10 and enable is high, out must equal in2.
    check_sel_10_enabled_routes_in2: assert property (
        @($global_clock) (sel == 2'b10 && enable) |-> (out == in2)
    );

    // When sel is 10 and enable is low, out must be zero.
    check_sel_10_disabled_drives_zero: assert property (
        @($global_clock) (sel == 2'b10 && !enable) |-> (out == 4'b0000)
    );

    // When sel is 11 and enable is high, out must equal in3.
    check_sel_11_enabled_routes_in3: assert property (
        @($global_clock) (sel == 2'b11 && enable) |-> (out == in3)
    );

    // When sel is 11 and enable is low, out must be zero.
    check_sel_11_disabled_drives_zero: assert property (
        @($global_clock) (sel == 2'b11 && !enable) |-> (out == 4'b0000)
    );

endmodule