module round_sat_sva (
    input logic clk,
    input logic rst,
    input logic signed [15:0] in_val,
    input logic signed [15:0] min_val,
    input logic signed [15:0] max_val,
    input logic signed [15:0] out_round,
    input logic signed [15:0] out_sat
);

    // Synchronous reset clears both registered outputs.
    check_reset_clears_outputs: assert property (
        @(posedge clk)
        rst |=> (out_round == 16'sd0 && out_sat == 16'sd0)
    );

    // Odd input values are rounded up by one.
    check_round_odd_adds_one: assert property (
        @(posedge clk) disable iff (rst)
        in_val[0] |=> (out_round == ($past(in_val) + 16'sd1))
    );

    // Even input values pass through the round block unchanged.
    check_round_even_passthrough: assert property (
        @(posedge clk) disable iff (rst)
        !in_val[0] |=> (out_round == $past(in_val))
    );

    // Inputs below the minimum clamp to min_val.
    check_sat_low_clamps_to_min: assert property (
        @(posedge clk) disable iff (rst)
        (in_val < min_val) |=> (out_sat == $past(min_val))
    );

    // Inputs above the maximum clamp to max_val when not already below min_val.
    check_sat_high_clamps_to_max: assert property (
        @(posedge clk) disable iff (rst)
        (!(in_val < min_val) && (in_val > max_val)) |=> (out_sat == $past(max_val))
    );

    // Inputs within the range pass through the saturation block unchanged.
    check_sat_in_range_passthrough: assert property (
        @(posedge clk) disable iff (rst)
        (!(in_val < min_val) && !(in_val > max_val)) |=> (out_sat == $past(in_val))
    );

endmodule