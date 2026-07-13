module prior_enc_sva #(
    parameter int WIDTH = 64,
    parameter int N = (WIDTH <= 1) ? 1 : $clog2(WIDTH)
) (
    input logic                 clk,
    input logic [WIDTH-1:0]     data_in,
    input logic [N-1:0]         encode_out,
    input logic                 enable_out
);

    // Combinational DUT sampled on an external clock.

    // enable_out must be the reduction-OR of data_in.
    check_enable_matches_input: assert property (
        @(posedge clk) enable_out == (|data_in)
    );

    // With no asserted input bits, the encoder must output zero and deassert enable.
    check_zero_input_outputs_zero: assert property (
        @(posedge clk) (data_in == '0) |-> (!enable_out && (encode_out == '0))
    );

    // A valid encoded output must always be within the input index range.
    check_code_in_range_when_enabled: assert property (
        @(posedge clk) enable_out |-> (encode_out < WIDTH)
    );

    genvar gi;
    generate
        for (gi = 0; gi < WIDTH; gi = gi + 1) begin : gen_highest_set
            localparam logic [N-1:0] IDX = gi;

            if (gi == WIDTH-1) begin : gen_top_bit
                // If the top input bit is set, it must be selected.
                check_highest_set_encodes_index: assert property (
                    @(posedge clk) data_in[gi] |-> (enable_out && (encode_out == IDX))
                );
            end else begin : gen_mid_bits
                // If bit gi is the highest asserted input, it must be selected.
                check_highest_set_encodes_index: assert property (
                    @(posedge clk) (data_in[gi] && ~(|data_in[WIDTH-1:gi+1])) |-> (enable_out && (encode_out == IDX))
                );
            end
        end
    endgenerate

    generate
        for (gi = 0; gi < WIDTH; gi = gi + 1) begin : gen_output_decode
            localparam logic [N-1:0] IDX = gi;

            if (gi == WIDTH-1) begin : gen_top_code
                // If gi is encoded, that input bit must be set.
                check_encoded_index_matches_input: assert property (
                    @(posedge clk) (enable_out && (encode_out == IDX)) |-> data_in[gi]
                );
            end else begin : gen_mid_codes
                // If gi is encoded, no higher input bit may be set.
                check_encoded_index_matches_input: assert property (
                    @(posedge clk) (enable_out && (encode_out == IDX)) |-> (data_in[gi] && ~(|data_in[WIDTH-1:gi+1]))
                );
            end
        end
    endgenerate

endmodule