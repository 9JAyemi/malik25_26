module decoder_2to4_with_enable_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic EN,
    input logic [3:0] Y
);

    // Combinational decoder sampled on an external clock; no reset in the RTL.

    // When disabled, all outputs must be low.
    check_disable_drives_zero: assert property (
        @(posedge clk) !EN |-> (Y == 4'b0000)
    );

    // Y[0] is high exactly when EN=1 and AB=00.
    check_y0_decode: assert property (
        @(posedge clk) Y[0] == (EN && !A && !B)
    );

    // Y[1] is high exactly when EN=1 and AB=01.
    check_y1_decode: assert property (
        @(posedge clk) Y[1] == (EN && !A && B)
    );

    // Y[2] is high exactly when EN=1 and AB=10.
    check_y2_decode: assert property (
        @(posedge clk) Y[2] == (EN && A && !B)
    );

    // Y[3] is high exactly when EN=1 and AB=11.
    check_y3_decode: assert property (
        @(posedge clk) Y[3] == (EN && A && B)
    );

    // When enabled, the output must be one of the four one-hot decode values.
    check_enabled_output_code: assert property (
        @(posedge clk) EN |-> ((Y == 4'b0001) || (Y == 4'b0010) || (Y == 4'b0100) || (Y == 4'b1000))
    );

    // The output must always be zero or a valid one-hot decode value.
    check_output_legal_values: assert property (
        @(posedge clk) (Y == 4'b0000) || (Y == 4'b0001) || (Y == 4'b0010) || (Y == 4'b0100) || (Y == 4'b1000)
    );

endmodule