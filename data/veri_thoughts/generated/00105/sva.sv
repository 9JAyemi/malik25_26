module decoder_3to8_sva (
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

    // Y0 is low only for input 3'b000.
    check_y0_decode: assert property (
        @($global_clock) Y0 == (A | B | C)
    );

    // Y1 is low only for input 3'b001.
    check_y1_decode: assert property (
        @($global_clock) Y1 == (A | B | ~C)
    );

    // Y2 is low only for input 3'b010.
    check_y2_decode: assert property (
        @($global_clock) Y2 == (A | ~B | C)
    );

    // Y3 is low only for input 3'b011.
    check_y3_decode: assert property (
        @($global_clock) Y3 == (A | ~B | ~C)
    );

    // Y4 is low only for input 3'b100.
    check_y4_decode: assert property (
        @($global_clock) Y4 == (~A | B | C)
    );

    // Y5 is low only for input 3'b101.
    check_y5_decode: assert property (
        @($global_clock) Y5 == (~A | B | ~C)
    );

    // Y6 is low only for input 3'b110.
    check_y6_decode: assert property (
        @($global_clock) Y6 == (~A | ~B | C)
    );

    // Y7 is low only for input 3'b111.
    check_y7_decode: assert property (
        @($global_clock) Y7 == (~A | ~B | ~C)
    );

    // Exactly one output is active low at any time.
    check_single_active_low: assert property (
        @($global_clock) $onehot({~Y7, ~Y6, ~Y5, ~Y4, ~Y3, ~Y2, ~Y1, ~Y0})
    );

    // The output bus matches the active-low one-hot decode of {A,B,C}.
    check_output_vector_decode: assert property (
        @($global_clock) {Y7, Y6, Y5, Y4, Y3, Y2, Y1, Y0} == ~(8'b00000001 << {A, B, C})
    );

endmodule