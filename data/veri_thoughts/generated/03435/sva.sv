module decoder_3to8_assertions (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic Y0,
    input logic Y1,
    input logic Y2,
    input logic Y3,
    input logic Y4,
    input logic Y5,
    input logic Y6,
    input logic Y7
);

    // Y0 decodes input 000.
    check_y0_decode: assert property (
        @(posedge clk) Y0 == (~A & ~B & ~C)
    );

    // Y1 decodes input 001.
    check_y1_decode: assert property (
        @(posedge clk) Y1 == (~A & ~B & C)
    );

    // Y2 decodes input 010.
    check_y2_decode: assert property (
        @(posedge clk) Y2 == (~A & B & ~C)
    );

    // Y3 decodes input 011.
    check_y3_decode: assert property (
        @(posedge clk) Y3 == (~A & B & C)
    );

    // Y4 decodes input 100.
    check_y4_decode: assert property (
        @(posedge clk) Y4 == (A & ~B & ~C)
    );

    // Y5 decodes input 101.
    check_y5_decode: assert property (
        @(posedge clk) Y5 == (A & ~B & C)
    );

    // Y6 decodes input 110.
    check_y6_decode: assert property (
        @(posedge clk) Y6 == (A & B & ~C)
    );

    // Y7 decodes input 111.
    check_y7_decode: assert property (
        @(posedge clk) Y7 == (A & B & C)
    );

    // Exactly one output is asserted for any input combination.
    check_outputs_onehot: assert property (
        @(posedge clk) $onehot({Y7, Y6, Y5, Y4, Y3, Y2, Y1, Y0})
    );

    // The output vector matches the binary value of {A,B,C}.
    check_output_vector_decode: assert property (
        @(posedge clk) {Y7, Y6, Y5, Y4, Y3, Y2, Y1, Y0} == (8'b0000_0001 << {A, B, C})
    );

endmodule