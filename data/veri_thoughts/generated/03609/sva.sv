module delay_line_sva #(
    parameter integer DELAY = 0,
    parameter integer WIDTH = 8
) (
    input logic                 ce,
    input logic                 rst,
    input logic                 clk,
    input logic [WIDTH-1:0]     in,
    input logic [WIDTH-1:0]     out
);

    generate
        if (DELAY == 0) begin : gen_no_delay
            // With zero delay, output is the direct input path.
            check_bypass_path: assert property (
                @(posedge clk) disable iff (rst) out == in
            );

            // Reset does not change the zero-delay bypass behavior.
            check_bypass_path_on_reset: assert property (
                @(posedge clk) rst |-> out == in
            );
        end
        else begin : gen_delayed
            // A synchronous reset clears the delayed output by the next clock.
            check_reset_clears_output: assert property (
                @(posedge clk) rst |=> out == {WIDTH{1'b0}}
            );

            // When clock enable is low, the delayed output holds its value.
            check_hold_when_ce_low: assert property (
                @(posedge clk) disable iff (rst) !ce |=> out == $past(out)
            );

            // DELAY enabled clocks propagate input data to the output.
            check_pipeline_delay: assert property (
                @(posedge clk) disable iff (rst) ce[*DELAY] |=> out == $past(in, DELAY)
            );
        end
    endgenerate

endmodule