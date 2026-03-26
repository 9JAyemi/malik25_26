module top_module_sva (
    input logic [3:0] in,
    input logic [1:0] pos
);

    // 0001 maps to 00.
    check_encode_0001: assert property (
        @($global_clock) (in == 4'b0001) |-> (pos == 2'b00)
    );

    // 0010 maps to 01.
    check_encode_0010: assert property (
        @($global_clock) (in == 4'b0010) |-> (pos == 2'b01)
    );

    // 0100 maps to 10.
    check_encode_0100: assert property (
        @($global_clock) (in == 4'b0100) |-> (pos == 2'b10)
    );

    // 1000 maps to 11.
    check_encode_1000: assert property (
        @($global_clock) (in == 4'b1000) |-> (pos == 2'b11)
    );

    // All other input patterns map to the default 00.
    check_encode_default: assert property (
        @($global_clock)
        ((in != 4'b0001) && (in != 4'b0010) && (in != 4'b0100) && (in != 4'b1000)) |-> (pos == 2'b00)
    );

endmodule