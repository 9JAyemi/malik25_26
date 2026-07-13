module decoder_assertions (
    input logic A,
    input logic B,
    input logic C,
    input logic EN,
    input logic Y0,
    input logic Y1,
    input logic Y2,
    input logic Y3,
    input logic Y4,
    input logic Y5,
    input logic Y6,
    input logic Y7
);

    // Outputs are all low when the decoder is disabled.
    check_disabled_all_zero: assert property (
        @($global_clock) !EN |-> (!Y0 && !Y1 && !Y2 && !Y3 && !Y4 && !Y5 && !Y6 && !Y7)
    );

    // Y0 is asserted only for enabled input 000.
    check_y0_decode: assert property (
        @($global_clock) (Y0 == (EN && !A && !B && !C))
    );

    // Y1 is asserted only for enabled input 001.
    check_y1_decode: assert property (
        @($global_clock) (Y1 == (EN && !A && !B && C))
    );

    // Y2 is asserted only for enabled input 010.
    check_y2_decode: assert property (
        @($global_clock) (Y2 == (EN && !A && B && !C))
    );

    // Y3 is asserted only for enabled input 011.
    check_y3_decode: assert property (
        @($global_clock) (Y3 == (EN && !A && B && C))
    );

    // Y4 is asserted only for enabled input 100.
    check_y4_decode: assert property (
        @($global_clock) (Y4 == (EN && A && !B && !C))
    );

    // Y5 is asserted only for enabled input 101.
    check_y5_decode: assert property (
        @($global_clock) (Y5 == (EN && A && !B && C))
    );

    // Y6 is asserted only for enabled input 110.
    check_y6_decode: assert property (
        @($global_clock) (Y6 == (EN && A && B && !C))
    );

    // Y7 is asserted only for enabled input 111.
    check_y7_decode: assert property (
        @($global_clock) (Y7 == (EN && A && B && C))
    );

endmodule