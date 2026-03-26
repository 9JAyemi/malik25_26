module top_module_sva (
    input logic        clk,
    input logic        reset,
    input logic [7:0]  d,
    input logic        select,
    input logic [7:0]  q,
    input logic [7:0]  register_output,
    input logic [3:0]  counter_output,
    input logic [7:0]  functional_output
);

    // Reset clears the register on the next cycle.
    check_register_clears_on_reset: assert property (
        @(posedge clk) reset |=> (register_output == 8'h00)
    );

    // Reset clears the counter on the next cycle.
    check_counter_clears_on_reset: assert property (
        @(posedge clk) reset |=> (counter_output == 4'h0)
    );

    // Reset forces the datapath outputs low on the next cycle.
    check_outputs_clear_on_reset: assert property (
        @(posedge clk) reset |=> ((functional_output == 8'h00) && (q == 8'h00))
    );

    // On each non-reset cycle, the register captures d.
    check_register_captures_d: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (register_output == $past(d))
    );

    // On each non-reset cycle, the counter increments modulo 16.
    check_counter_increments: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (counter_output == ($past(counter_output) + 4'd1))
    );

    // The mux forwards the counter when select is high.
    check_mux_selects_counter: assert property (
        @(posedge clk) disable iff (reset) select |-> (functional_output == {4'b0, counter_output})
    );

    // The mux forwards the register when select is low.
    check_mux_selects_register: assert property (
        @(posedge clk) disable iff (reset) !select |-> (functional_output == register_output)
    );

    // The final output matches the adder result.
    check_adder_matches_output: assert property (
        @(posedge clk) disable iff (reset) q == (functional_output + {4'b0, counter_output})
    );

    // With select high, q is twice the counter value.
    check_select_high_doubles_counter: assert property (
        @(posedge clk) disable iff (reset) select |-> (q == {3'b0, counter_output, 1'b0})
    );

    // With select low, q is register output plus the counter.
    check_select_low_adds_register_and_counter: assert property (
        @(posedge clk) disable iff (reset) !select |-> (q == (register_output + {4'b0, counter_output}))
    );

endmodule