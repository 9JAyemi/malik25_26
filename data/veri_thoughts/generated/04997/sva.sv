module decoder_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic [7:0] Y
);

    // 000 selects Y[0] low.
    check_decode_000: assert property (
        @(posedge clk) ({A, B, C} == 3'b000) |-> (Y == 8'b11111110)
    );

    // 001 selects Y[1] low.
    check_decode_001: assert property (
        @(posedge clk) ({A, B, C} == 3'b001) |-> (Y == 8'b11111101)
    );

    // 010 selects Y[2] low.
    check_decode_010: assert property (
        @(posedge clk) ({A, B, C} == 3'b010) |-> (Y == 8'b11111011)
    );

    // 011 selects Y[3] low.
    check_decode_011: assert property (
        @(posedge clk) ({A, B, C} == 3'b011) |-> (Y == 8'b11110111)
    );

    // 100 selects Y[4] low.
    check_decode_100: assert property (
        @(posedge clk) ({A, B, C} == 3'b100) |-> (Y == 8'b11101111)
    );

    // 101 selects Y[5] low.
    check_decode_101: assert property (
        @(posedge clk) ({A, B, C} == 3'b101) |-> (Y == 8'b11011111)
    );

    // 110 selects Y[6] low.
    check_decode_110: assert property (
        @(posedge clk) ({A, B, C} == 3'b110) |-> (Y == 8'b10111111)
    );

    // 111 selects Y[7] low.
    check_decode_111: assert property (
        @(posedge clk) ({A, B, C} == 3'b111) |-> (Y == 8'b01111111)
    );

    // Output is always active-low one-hot.
    check_active_low_onehot: assert property (
        @(posedge clk) $onehot(~Y)
    );

endmodule