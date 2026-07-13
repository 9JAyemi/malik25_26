module shift_register_sva (
    input logic clk,
    input logic [3:0] in,
    input logic load,
    input logic [3:0] out,
    input logic valid
);
    // Next cycle valid reflects load HIGH this cycle.
    valid_next_high_when_load_high: assert property (
        @(posedge clk) load |=> (valid == 1'b1)
    );

    // Next cycle valid reflects load LOW this cycle.
    valid_next_low_when_load_low: assert property (
        @(posedge clk) !load |=> (valid == 1'b0)
    );

    // A rise on load causes a rise on valid in the next cycle.
    valid_rise_follows_load_rise: assert property (
        @(posedge clk) $rose(load) |=> $rose(valid)
    );

    // A fall on load causes a fall on valid in the next cycle.
    valid_fall_follows_load_fall: assert property (
        @(posedge clk) $fell(load) |=> $fell(valid)
    );

    // When load is LOW, out is cleared to zero in the next cycle.
    out_cleared_next_on_no_load: assert property (
        @(posedge clk) !load |=> (out == 4'b0000)
    );

    // A falling load clears both valid and out in the next cycle.
    clear_valid_and_out_on_load_fall: assert property (
        @(posedge clk) $fell(load) |=> (!valid && (out == 4'b0000))
    );

    // Whenever valid is LOW, out must be zero in the same cycle.
    valid_low_implies_out_zero: assert property (
        @(posedge clk) (!valid) |-> (out == 4'b0000)
    );

    // Four consecutive cycles of load HIGH pipeline in to out with 4-cycle latency.
    four_cycle_load_delays_input_to_out: assert property (
        @(posedge clk) load[*4] |=> (out == $past(in,4))
    );

    // A fall on valid implies out is zero in the same cycle.
    out_zero_on_valid_fall: assert property (
        @(posedge clk) $fell(valid) |-> (out == 4'b0000)
    );

    // After four consecutive load HIGH cycles, valid is HIGH in the next cycle.
    valid_high_after_four_loads: assert property (
        @(posedge clk) load[*4] |=> (valid == 1'b1)
    );
endmodule