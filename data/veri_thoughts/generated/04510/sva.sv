module decoder_4to16_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic [15:0] Y
);

    // External clk samples a purely combinational DUT with no reset.

    // 0000 decodes to Y[0].
    check_decode_0000: assert property (
        @(posedge clk) ({A,B,C,D} === 4'b0000) |-> (Y === 16'h0001)
    );

    // 0001 decodes to Y[1].
    check_decode_0001: assert property (
        @(posedge clk) ({A,B,C,D} === 4'b0001) |-> (Y === 16'h0002)
    );

    // 0010 decodes to Y[2].
    check_decode_0010: assert property (
        @(posedge clk) ({A,B,C,D} === 4'b0010) |-> (Y === 16'h0004)
    );

    // 0011 decodes to Y[3].
    check_decode_0011: assert property (
        @(posedge clk) ({A,B,C,D} === 4'b0011) |-> (Y === 16'h0008)
    );

    // 0100 decodes to Y[4].
    check_decode_0100: assert property (
        @(posedge clk) ({A,B,C,D} === 4'b0100) |-> (Y === 16'h0010)
    );

    // 0101 decodes to Y[5].
    check_decode_0101: assert property (
        @(posedge clk) ({A,B,C,D} === 4'b0101) |-> (Y === 16'h0020)
    );

    // 0110 decodes to Y[6].
    check_decode_0110: assert property (
        @(posedge clk) ({A,B,C,D} === 4'b0110) |-> (Y === 16'h0040)
    );

    // 0111 decodes to Y[7].
    check_decode_0111: assert property (
        @(posedge clk) ({A,B,C,D} === 4'b0111) |-> (Y === 16'h0080)
    );

    // 1000 decodes to Y[8].
    check_decode_1000: assert property (
        @(posedge clk) ({A,B,C,D} === 4'b1000) |-> (Y === 16'h0100)
    );

    // 1001 decodes to Y[9].
    check_decode_1001: assert property (
        @(posedge clk) ({A,B,C,D} === 4'b1001) |-> (Y === 16'h0200)
    );

    // 1010 decodes to Y[10].
    check_decode_1010: assert property (
        @(posedge clk) ({A,B,C,D} === 4'b1010) |-> (Y === 16'h0400)
    );

    // 1011 decodes to Y[11].
    check_decode_1011: assert property (
        @(posedge clk) ({A,B,C,D} === 4'b1011) |-> (Y === 16'h0800)
    );

    // 1100 decodes to Y[12].
    check_decode_1100: assert property (
        @(posedge clk) ({A,B,C,D} === 4'b1100) |-> (Y === 16'h1000)
    );

    // 1101 decodes to Y[13].
    check_decode_1101: assert property (
        @(posedge clk) ({A,B,C,D} === 4'b1101) |-> (Y === 16'h2000)
    );

    // 1110 decodes to Y[14].
    check_decode_1110: assert property (
        @(posedge clk) ({A,B,C,D} === 4'b1110) |-> (Y === 16'h4000)
    );

    // 1111 decodes to Y[15].
    check_decode_1111: assert property (
        @(posedge clk) ({A,B,C,D} === 4'b1111) |-> (Y === 16'h8000)
    );

    // Stable inputs keep the decoded output stable.
    check_stable_inputs_stable_output: assert property (
        @(posedge clk) $stable({A,B,C,D}) |-> $stable(Y)
    );

endmodule