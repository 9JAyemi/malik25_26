module ring_counter_sva #(parameter int m = 4) (
    input logic clk,
    input logic [m-1:0] out
);

    localparam logic [m-1:0] ALL_ONES  = {m{1'b1}};
    localparam logic [m-1:0] ALL_ZEROS = {m{1'b0}};

    // An all-ones state clears to all zeros on the next clock.
    check_all_ones_wraps_to_zero: assert property (
        @(posedge clk) (out == ALL_ONES) |=> (out == ALL_ZEROS)
    );

    // An all-zero state remains all zero on the next clock.
    check_all_zero_holds: assert property (
        @(posedge clk) (out == ALL_ZEROS) |=> (out == ALL_ZEROS)
    );

    generate
        if (m > 1) begin : gen_multi_bit
            // On non-wrap cycles, bit 0 takes the previous MSB.
            check_lsb_wraparound: assert property (
                @(posedge clk) (out != ALL_ONES) |=> (out[0] == $past(out[m-1]))
            );

            for (genvar i = 1; i < m; i++) begin : gen_shift_bits
                // On non-wrap cycles, each upper bit takes the previous lower bit.
                check_shift_from_lower: assert property (
                    @(posedge clk) (out != ALL_ONES) |=> (out[i] == $past(out[i-1]))
                );
            end
        end else begin : gen_single_bit
            // A 1-bit instance always becomes zero after a clock edge.
            check_single_bit_clears: assert property (
                @(posedge clk) 1'b1 |=> (out == 1'b0)
            );
        end
    endgenerate

endmodule