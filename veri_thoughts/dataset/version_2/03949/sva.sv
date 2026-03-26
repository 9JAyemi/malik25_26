module decoders38_sva (
    input logic clk,
    input logic [0:2] in,
    input logic [0:2] en,
    input logic [0:7] out
);

    // When the decoder is not enabled, all outputs remain HIGH.
    check_disabled_outputs_high: assert property (
        @(posedge clk)
        (!en[0] || en[1] || en[2]) |-> (out[0] && out[1] && out[2] && out[3] && out[4] && out[5] && out[6] && out[7])
    );

    // When enabled with input 000, only out[0] is LOW.
    check_decode_000: assert property (
        @(posedge clk)
        (en[0] && !en[1] && !en[2] && !in[2] && !in[1] && !in[0]) |-> (!out[0] && out[1] && out[2] && out[3] && out[4] && out[5] && out[6] && out[7])
    );

    // When enabled with input 001, only out[1] is LOW.
    check_decode_001: assert property (
        @(posedge clk)
        (en[0] && !en[1] && !en[2] && !in[2] && !in[1] &&  in[0]) |-> (out[0] && !out[1] && out[2] && out[3] && out[4] && out[5] && out[6] && out[7])
    );

    // When enabled with input 010, only out[2] is LOW.
    check_decode_010: assert property (
        @(posedge clk)
        (en[0] && !en[1] && !en[2] && !in[2] &&  in[1] && !in[0]) |-> (out[0] && out[1] && !out[2] && out[3] && out[4] && out[5] && out[6] && out[7])
    );

    // When enabled with input 011, only out[3] is LOW.
    check_decode_011: assert property (
        @(posedge clk)
        (en[0] && !en[1] && !en[2] && !in[2] &&  in[1] &&  in[0]) |-> (out[0] && out[1] && out[2] && !out[3] && out[4] && out[5] && out[6] && out[7])
    );

    // When enabled with input 100, only out[4] is LOW.
    check_decode_100: assert property (
        @(posedge clk)
        (en[0] && !en[1] && !en[2] &&  in[2] && !in[1] && !in[0]) |-> (out[0] && out[1] && out[2] && out[3] && !out[4] && out[5] && out[6] && out[7])
    );

    // When enabled with input 101, only out[5] is LOW.
    check_decode_101: assert property (
        @(posedge clk)
        (en[0] && !en[1] && !en[2] &&  in[2] && !in[1] &&  in[0]) |-> (out[0] && out[1] && out[2] && out[3] && out[4] && !out[5] && out[6] && out[7])
    );

    // When enabled with input 110, only out[6] is LOW.
    check_decode_110: assert property (
        @(posedge clk)
        (en[0] && !en[1] && !en[2] &&  in[2] &&  in[1] && !in[0]) |-> (out[0] && out[1] && out[2] && out[3] && out[4] && out[5] && !out[6] && out[7])
    );

    // When enabled with input 111, only out[7] is LOW.
    check_decode_111: assert property (
        @(posedge clk)
        (en[0] && !en[1] && !en[2] &&  in[2] &&  in[1] &&  in[0]) |-> (out[0] && out[1] && out[2] && out[3] && out[4] && out[5] && out[6] && !out[7])
    );

endmodule