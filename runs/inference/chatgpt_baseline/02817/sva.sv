module altera_tse_xcvr_resync_sva #(
    parameter int SYNC_CHAIN_LENGTH = 2,
    parameter int WIDTH             = 1,
    parameter int SLOW_CLOCK        = 0
) (
    input  logic              clk,
    input  logic [WIDTH-1:0]  d,
    input  logic [WIDTH-1:0]  q
);
    localparam int INT_LEN = (SYNC_CHAIN_LENGTH > 0) ? SYNC_CHAIN_LENGTH : 1;

    genvar ig;
    generate
      for (ig = 0; ig < WIDTH; ig++) begin : gen_sva_per_bit

        if (SLOW_CLOCK == 0) begin : fast_path
          // q equals d delayed by INT_LEN cycles through the synchronizer.
          check_q_equals_delayed_d: assert property (
            @(posedge clk) q[ig] == $past(d[ig], INT_LEN, 1'b0)
          );

          // A rising edge on d produces a rising edge on q exactly INT_LEN cycles later.
          check_d_rise_to_q_rise_exact: assert property (
            @(posedge clk) $rose(d[ig]) |-> ##INT_LEN $rose(q[ig])
          );

          // A falling edge on d produces a falling edge on q exactly INT_LEN cycles later.
          check_d_fall_to_q_fall_exact: assert property (
            @(posedge clk) $fell(d[ig]) |-> ##INT_LEN $fell(q[ig])
          );

          // If d is held LOW for INT_LEN cycles, q must be LOW at the end of that window.
          check_zero_propagates_through_chain: assert property (
            @(posedge clk) (d[ig] == 1'b0)[*INT_LEN] |-> (q[ig] == 1'b0)
          );

          // If d is held HIGH for INT_LEN cycles, q must be HIGH at the end of that window.
          check_one_propagates_through_chain: assert property (
            @(posedge clk) (d[ig] == 1'b1)[*INT_LEN] |-> (q[ig] == 1'b1)
          );

        end else begin : slow_path
          // A rising event on d eventually causes q to be 1 within INT_LEN clk cycles.
          check_d_rise_eventually_sets_q: assert property (
            @(posedge clk) $rose(d[ig]) |-> ##[0:INT_LEN] (q[ig] == 1'b1)
          );

          // If q is 1 while d is 0, q must clear within INT_LEN clk cycles.
          check_q_clears_when_d_low: assert property (
            @(posedge clk) (q[ig] == 1'b1 && d[ig] == 1'b0) |-> ##[1:INT_LEN] (q[ig] == 1'b0)
          );

          // If d stays 0 for INT_LEN clk cycles, q must be 0 at the end of that window.
          check_d_low_flushes_q: assert property (
            @(posedge clk) (d[ig] == 1'b0)[*INT_LEN] |-> (q[ig] == 1'b0)
          );
        end

      end
    endgenerate
endmodule