module decimal_to_binary_sva (
    input logic [3:0] in_value,
    input logic [3:0] out_value
);

    // 0 maps to 0.
    check_map_0: assert property (
        @($global_clock) (in_value == 4'b0000) |-> (out_value == 4'b0000)
    );

    // 1 maps to 1.
    check_map_1: assert property (
        @($global_clock) (in_value == 4'b0001) |-> (out_value == 4'b0001)
    );

    // 2 maps to 2.
    check_map_2: assert property (
        @($global_clock) (in_value == 4'b0010) |-> (out_value == 4'b0010)
    );

    // 3 maps to 3.
    check_map_3: assert property (
        @($global_clock) (in_value == 4'b0011) |-> (out_value == 4'b0011)
    );

    // 4 maps to 4.
    check_map_4: assert property (
        @($global_clock) (in_value == 4'b0100) |-> (out_value == 4'b0100)
    );

    // 5 maps to 5.
    check_map_5: assert property (
        @($global_clock) (in_value == 4'b0101) |-> (out_value == 4'b0101)
    );

    // 6 maps to 6.
    check_map_6: assert property (
        @($global_clock) (in_value == 4'b0110) |-> (out_value == 4'b0110)
    );

    // 7 maps to 7.
    check_map_7: assert property (
        @($global_clock) (in_value == 4'b0111) |-> (out_value == 4'b0111)
    );

    // 8 maps to 8.
    check_map_8: assert property (
        @($global_clock) (in_value == 4'b1000) |-> (out_value == 4'b1000)
    );

    // 9 maps to 9.
    check_map_9: assert property (
        @($global_clock) (in_value == 4'b1001) |-> (out_value == 4'b1001)
    );

    // Values 10 through 15 drive X.
    check_default_x: assert property (
        @($global_clock) (in_value >= 4'b1010) |-> (out_value == 4'bXXXX)
    );

endmodule