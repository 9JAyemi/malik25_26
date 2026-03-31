module zet_bitlog_sva (
    input logic [15:0] x,
    input logic [15:0] o,
    input logic        cfo,
    input logic        ofo
);

    // o is the bitwise inverse of x.
    check_output_is_inverse: assert property (
        @($global_clock) o == ~x
    );

    // cfo is tied low.
    check_cfo_tied_low: assert property (
        @($global_clock) cfo == 1'b0
    );

    // ofo is tied low.
    check_ofo_tied_low: assert property (
        @($global_clock) ofo == 1'b0
    );

endmodule