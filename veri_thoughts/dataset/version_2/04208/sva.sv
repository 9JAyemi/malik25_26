module decoder_3to8_sva (
    input logic clk,
    input logic Y7,
    input logic Y6,
    input logic Y5,
    input logic Y4,
    input logic Y3,
    input logic Y2,
    input logic Y1,
    input logic Y0,
    input logic A2,
    input logic A1,
    input logic A0
);

    // Pure combinational decoder sampled on clk; RTL has no reset.

    // Y7 is high only for input 111.
    check_y7_decode: assert property (
        @(posedge clk) Y7 == (A2 & A1 & A0)
    );

    // Y6 is high only for input 110.
    check_y6_decode: assert property (
        @(posedge clk) Y6 == (A2 & A1 & ~A0)
    );

    // Y5 is high only for input 101.
    check_y5_decode: assert property (
        @(posedge clk) Y5 == (A2 & ~A1 & A0)
    );

    // Y4 is high only for input 100.
    check_y4_decode: assert property (
        @(posedge clk) Y4 == (A2 & ~A1 & ~A0)
    );

    // Y3 is high only for input 011.
    check_y3_decode: assert property (
        @(posedge clk) Y3 == (~A2 & A1 & A0)
    );

    // Y2 is high only for input 010.
    check_y2_decode: assert property (
        @(posedge clk) Y2 == (~A2 & A1 & ~A0)
    );

    // Y1 is high only for input 001.
    check_y1_decode: assert property (
        @(posedge clk) Y1 == (~A2 & ~A1 & A0)
    );

    // Y0 is high only for input 000.
    check_y0_decode: assert property (
        @(posedge clk) Y0 == (~A2 & ~A1 & ~A0)
    );

    // The output vector matches the decoded input value.
    check_output_vector_decode: assert property (
        @(posedge clk) {Y7, Y6, Y5, Y4, Y3, Y2, Y1, Y0} == (8'b0000_0001 << {A2, A1, A0})
    );

    // Exactly one output is asserted for every input combination.
    check_outputs_onehot: assert property (
        @(posedge clk) $onehot({Y7, Y6, Y5, Y4, Y3, Y2, Y1, Y0})
    );

endmodule