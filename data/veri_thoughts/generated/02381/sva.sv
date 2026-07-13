module ad_b2g_sva #(
    parameter int DATA_WIDTH = 8
) (
    input  logic                         clk,
    input  logic [DATA_WIDTH-1:0]        din,
    input  logic [DATA_WIDTH-1:0]        dout
);

    // MSB passes through unmodified.
    gen_msb: if (DATA_WIDTH > 0) begin
        check_msb_passthrough: assert property (
            @(posedge clk) dout[DATA_WIDTH-1] == din[DATA_WIDTH-1]
        );
    end

    // Each Gray bit equals XOR of adjacent binary bits.
    gen_bits: if (DATA_WIDTH > 1) begin
        genvar k;
        for (k = 0; k < DATA_WIDTH-1; k++) begin : gen_gray_xor
            check_gray_xor_bit: assert property (
                @(posedge clk) dout[k] == (din[k+1] ^ din[k])
            );
        end
    end

    // Vector mapping equals {MSB, XOR of adjacent bits}.
    gen_vec: if (DATA_WIDTH > 1) begin
        check_vector_mapping: assert property (
            @(posedge clk) dout == {din[DATA_WIDTH-1], (din[DATA_WIDTH-1:1] ^ din[DATA_WIDTH-2:0])}
        );
    end

endmodule