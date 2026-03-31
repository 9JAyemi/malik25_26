module decoder_2to4_with_enable_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic EN,
    input logic [3:0] Y
);

// When EN is low, Y must be 0.
    check_disable_clears_output: assert property (
        @(posedge clk) !EN |-> (Y == 4'b0000)
    );

// When EN is high and A=0, B=0, Y must be 0001.
    check_enable_a0_b0: assert property (
        @(posedge clk) (EN && !A && !B) |-> (Y == 4'b0001)
    );

// When EN is high and A=0, B=1, Y must be 0010.
    check_enable_a0_b1: assert property (
        @(posedge clk) (EN && !A && B) |-> (Y == 4'b0010)
    );

// When EN is high and A=1, B=0, Y must be 0100.
    check_enable_a1_b0: assert property (
        @(posedge clk) (EN && A && !B) |-> (Y == 4'b0100)
    );

// When EN is high and A=1, B=1, Y must be 1000.
    check_enable_a1_b1: assert property (
        @(posedge clk) (EN && A && B) |-> (Y == 4'b1000)
    );

// Y can only be one of the four enabled encodings or zero.
    check_output_legal_values: assert property (
        @(posedge clk) Y inside {4'b0000, 4'b0001, 4'b0010, 4'b0100, 4'b1000}
    );

// If Y is non-zero, EN must be high.
    check_nonzero_output_requires_enable: assert property (
        @(posedge clk) (Y != 4'b0000) |-> EN
    );

// If Y is 0001, A=0, B=0, and EN=1.
    check_decode_0001: assert property (
        @(posedge clk) (Y == 4'b0001) |-> (EN && !A && !B)
    );

// If Y is 0010, A=0, B=1, and EN=1.
    check_decode_0010: assert property (
        @(posedge clk) (Y == 4'b0010) |-> (EN && !A && B)
    );

// If Y is 0100, A=1, B=0, and EN=1.
    check_decode_0100: assert property (
        @(posedge clk) (Y == 4'b0100) |-> (EN && A && !B)
    );

// If Y is 1000, A=1, B=1, and EN=1.
    check_decode_1000: assert property (
        @(posedge clk) (Y == 4'b1000) |-> (EN && A && B)
    );

endmodule
