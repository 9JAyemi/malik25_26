module zet_bitlog_sva (
    input logic        clk,
    input logic [15:0] x,
    input logic [15:0] o,
    input logic        cfo,
    input logic        ofo
);

    // Output is the bitwise inverse of the input.
    check_output_inverts_input: assert property (
        @(posedge clk) o == ~x
    );

    // Carry flag is tied low.
    check_cfo_tied_low: assert property (
        @(posedge clk) cfo == 1'b0
    );

    // Overflow flag is tied low.
    check_ofo_tied_low: assert property (
        @(posedge clk) ofo == 1'b0
    );

endmodule