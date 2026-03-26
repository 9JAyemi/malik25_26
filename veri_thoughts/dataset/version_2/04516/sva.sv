module ring_counter_sva #(
    parameter n = 4
)(
    input logic clk,
    input logic [n-1:0] out
);

    genvar i;
    generate
        if (n > 1) begin : gen_multi_bit_checks
            // Output rotates by one bit on each rising clock edge.
            check_out_rotates: assert property (
                @(posedge clk) 1'b1 |=> out == {$past(out[n-2:0]), $past(out[n-1])}
            );

            // Bit 0 takes the previous cycle's top bit.
            check_wrap_bit: assert property (
                @(posedge clk) 1'b1 |=> out[0] == $past(out[n-1])
            );

            for (i = 1; i < n; i++) begin : gen_shift_bit_checks
                // Each upper bit takes the previous cycle's next lower bit.
                check_shift_bit_relation: assert property (
                    @(posedge clk) 1'b1 |=> out[i] == $past(out[i-1])
                );
            end
        end else begin : gen_single_bit_checks
            // A 1-bit configuration holds its value each cycle.
            check_single_bit_holds: assert property (
                @(posedge clk) 1'b1 |=> out[0] == $past(out[0])
            );
        end
    endgenerate

endmodule