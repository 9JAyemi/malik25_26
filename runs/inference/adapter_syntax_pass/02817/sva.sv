module altera_tse_xcvr_resync_sva #(
    parameter int SYNC_CHAIN_LENGTH = 2,
    parameter int WIDTH             = 1,
    parameter int SLOW_CLOCK        = 0
) (
    input logic              clk,
    input logic [WIDTH-1:0]  d,
    input logic [WIDTH-1:0]  q
);

    localparam int INT_LEN = (SYNC_CHAIN_LENGTH > 0) ? SYNC_CHAIN_LENGTH : 1;

    generate
        if (SLOW_CLOCK == 0) begin : gen_fast_clock
            // q matches the registered input chain.
            check_fast_chain: assert property (
                @(posedge clk) 1'b1 |=> (q == $past(d, INT_LEN, 1'b0))
            );

            // q is the delayed version of d.
            check_fast_delay: assert property (
                @(posedge clk) 1'b1 |=> (q == $past(d, INT_LEN, '0))
            );

            // A sampled low input must appear at q after the chain latency.
            check_fast_low_propagates: assert property (
                @(posedge clk) (d == {WIDTH{1'b0}}) |=> (q == {WIDTH{1'b0}})
            );

            // A sampled high input must appear at q after the chain latency.
            check_fast_high_propagates: assert property (
                @(posedge clk) (d == {WIDTH{1'b1}}) |=> (q == {WIDTH{1'b1}})
            );
        end else begin : gen_slow_clock
            // q matches the registered input chain.
            check_slow_chain: assert property (
                @(posedge clk) 1'b1 |=> (q == $past(d, INT_LEN, 1'b0))
            );

            // q is the delayed version of d.
            check_slow_delay: assert property (
                @(posedge clk) 1'b1 |=> (q == $past(d, INT_LEN, '0))
            );

            // A sampled low input must appear at q after the chain latency.
            check_slow_low_propagates: assert property (
                @(posedge clk) (d == {WIDTH{1'b0}}) |=> (q == {WIDTH{1'b0}})
            );

            // A sampled high input must appear at q after the chain latency.
            check_slow_high_propagates: assert property (
                @(posedge clk) (d == {WIDTH{1'b1}}) |=> (q == {WIDTH{1'b1}})
            );
        end
    endgenerate

endmodule