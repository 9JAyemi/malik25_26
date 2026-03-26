module ClockBufferDriver_sva #(
    parameter n = 4
) (
    input logic         clk,
    input logic [n-1:0] clk_out
);

    // clk_out rotates by one bit every rising edge.
    check_clk_out_rotates: assert property (
        @(posedge clk)
        1'b1 |=> (clk_out == {$past(clk_out[n-2:0]), $past(clk_out[n-1])})
    );

    // Bit 0 takes the previous cycle's MSB.
    check_clk_out_wrap_bit: assert property (
        @(posedge clk)
        1'b1 |=> (clk_out[0] == $past(clk_out[n-1]))
    );

    genvar i;
    generate
        for (i = 1; i < n; i++) begin : gen_clk_out_bit_rotate
            // Each bit i takes the previous cycle's bit i-1.
            check_clk_out_bit_shift: assert property (
                @(posedge clk)
                1'b1 |=> (clk_out[i] == $past(clk_out[i-1]))
            );
        end
    endgenerate

    // After n rising edges, the rotated vector returns to its prior value.
    check_clk_out_period_n: assert property (
        @(posedge clk)
        1'b1 |=> ##(n-1) (clk_out == $past(clk_out, n))
    );

endmodule