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
        genvar ig;
        generate
            for (ig = 0; ig < WIDTH; ig = ig + 1) begin : gen_fast_chain
                // q reflects the previous cycle's d.
                check_fast_chain_pipeline: assert property (
                    @(posedge clk) disable iff (1'b0)
                    1'b1 |=> (q[ig] == $past(d[ig]))
                );
            end
        endgenerate
    end else begin : gen_slow_clock
        genvar ig;
        generate
            for (ig = 0; ig < WIDTH; ig = ig + 1) begin : gen_slow_chain
                // q reflects the previous cycle's d.
                check_slow_chain_pipeline: assert property (
                    @(posedge clk) disable iff (1'b0)
                    1'b1 |=> (q[ig] == $past(d[ig]))
                );
            end
        endgenerate
    end
endgenerate

endmodule