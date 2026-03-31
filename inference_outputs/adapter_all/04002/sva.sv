module decoder_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic [15:0] O
);

    // When A and B are both 0, O0 must be high and all other outputs must be low.
    check_decode_00: assert property (
        @(posedge clk) ({A, B} == 2'b00) |-> (O == 16'h0001)
    );

    // When A is 0 and B is 1, O1 must be high and all other outputs must be low.
    check_decode_01: assert property (
        @(posedge clk) ({A, B} == 2'b01) |-> (O == 16'h0002)
    );

    // When A is 1 and B is 0, O2 must be high and all other outputs must be low.
    check_decode_10: assert property (
        @(posedge clk) ({A, B} == 2'b10) |-> (O == 16'h0004)
    );

    // When A and B are both 1, O3 must be high and all other outputs must be low.
    check_decode_11: assert property (
        @(posedge clk) ({A, B} == 2'b11) |-> (O == 16'h0008)
    );

    // For all other input combinations, O must be zero.
    check_default_zero: assert property (
        @(posedge clk) !(({A, B} inside {2'b00, 2'b01, 2'b10, 2'b11})) |-> (O == 16'h0000)
    );

    // The upper 12 bits of O must always be zero.
    check_upper_bits_zero: assert property (
        @(posedge clk) (O[15:4] == 12'h000)
    );

    // O must always be one of the four valid decoder outputs.
    check_output_valid_set: assert property (
        @(posedge clk) (O inside {16'h0001, 16'h0002, 16'h0004, 16'h0008})
    );

endmodule