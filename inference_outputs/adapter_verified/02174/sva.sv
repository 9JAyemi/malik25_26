module zet_bitlog_sva (
    input logic        clk,
    input logic [15:0] x,
    input logic [15:0] o,
    input logic        cfo,
    input logic        ofo
);

// Output is bitwise complement of input.
    check_output_complement: assert property (
        @(posedge clk) o == ~x
    );

// Carry flag is forced low.
    check_cfo_low: assert property (
        @(posedge clk) cfo == 1'b0
    );

// Overflow flag is forced low.
    check_ofo_low: assert property (
        @(posedge clk) ofo == 1'b0
    );

endmodule
