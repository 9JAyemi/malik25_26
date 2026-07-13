module decoder_3to8_sva (
    input logic clk,
    input logic [2:0] A,
    input logic [2:0] B,
    input logic [2:0] C,
    input logic EN,
    input logic [7:0] Y
);

    // EN low forces the output low.
    check_disabled_zero: assert property (
        @(posedge clk) (EN == 1'b0) |-> (Y == 8'b00000000)
    );

    // Enabled decode of A=0, B=0, C=0 sets bit 0.
    check_decode_c000: assert property (
        @(posedge clk) (EN == 1'b1 && A == 3'b000 && B == 3'b000 && C == 3'b000) |-> (Y == 8'b00000001)
    );

    // Enabled decode of A=0, B=0, C=1 sets bit 1.
    check_decode_c001: assert property (
        @(posedge clk) (EN == 1'b1 && A == 3'b000 && B == 3'b000 && C == 3'b001) |-> (Y == 8'b00000010)
    );

    // Enabled decode of A=0, B=0, C=2 sets bit 2.
    check_decode_c010: assert property (
        @(posedge clk) (EN == 1'b1 && A == 3'b000 && B == 3'b000 && C == 3'b010) |-> (Y == 8'b00000100)
    );

    // Enabled decode of A=0, B=0, C=3 sets bit 3.
    check_decode_c011: assert property (
        @(posedge clk) (EN == 1'b1 && A == 3'b000 && B == 3'b000 && C == 3'b011) |-> (Y == 8'b00001000)
    );

    // Enabled decode of A=0, B=0, C=4 sets bit 4.
    check_decode_c100: assert property (
        @(posedge clk) (EN == 1'b1 && A == 3'b000 && B == 3'b000 && C == 3'b100) |-> (Y == 8'b00010000)
    );

    // Enabled decode of A=0, B=0, C=5 sets bit 5.
    check_decode_c101: assert property (
        @(posedge clk) (EN == 1'b1 && A == 3'b000 && B == 3'b000 && C == 3'b101) |-> (Y == 8'b00100000)
    );

    // Enabled decode of A=0, B=0, C=6 sets bit 6.
    check_decode_c110: assert property (
        @(posedge clk) (EN == 1'b1 && A == 3'b000 && B == 3'b000 && C == 3'b110) |-> (Y == 8'b01000000)
    );

    // Enabled decode of A=0, B=0, C=7 sets bit 7.
    check_decode_c111: assert property (
        @(posedge clk) (EN == 1'b1 && A == 3'b000 && B == 3'b000 && C == 3'b111) |-> (Y == 8'b10000000)
    );

    // Any other enabled input combination drives zero.
    check_enabled_default_zero: assert property (
        @(posedge clk) (EN == 1'b1 && (A != 3'b000 || B != 3'b000)) |-> (Y == 8'b00000000)
    );

endmodule