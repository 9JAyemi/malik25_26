module fifo_buffer_sva #(
    parameter int DATA_WIDTH = 8,
    parameter int DEPTH = 4
) (
    input logic clk,
    input logic aclr,
    input logic [DATA_WIDTH-1:0] din,
    input logic [DATA_WIDTH-1:0] dout
);

    localparam int SAMPLE_DELAY = DEPTH + 1;

    // A sampled reset drives dout low by the next clock.
    check_reset_zero_next_cycle: assert property (
        @(posedge clk) aclr |=> (dout == '0)
    );

    generate
        genvar j;
        for (j = 1; j <= SAMPLE_DELAY; j = j + 1) begin : gen_reset_flush_zero
            // After reset deasserts, dout stays low for the next j clocks.
            check_reset_flush_zero: assert property (
                @(posedge clk) aclr ##1 !aclr[*j] |-> (dout == '0)
            );
        end
    endgenerate

    // Without reset, sampled dout matches sampled din from SAMPLE_DELAY clocks earlier.
    check_output_delay: assert property (
        @(posedge clk) disable iff (aclr)
            !aclr[*SAMPLE_DELAY] |=> (dout == $past(din, SAMPLE_DELAY))
    );

endmodule