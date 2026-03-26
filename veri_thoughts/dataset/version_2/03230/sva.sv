module top_module_sva (
    input logic clk,
    input logic rst,
    input logic en,
    input logic load,
    input logic [3:0] data_in,
    input logic sel,
    input logic [3:0] out,
    input logic [3:0] shift_reg_out,
    input logic [3:0] counter_out,
    input logic [3:0] sum_out
);

    // Clock: clk
    // Reset: rst, active-high synchronous
    // Mixed sequential and combinational checks

    // Top output must match the adder output.
    check_top_out_follows_sum_out: assert property (
        @(posedge clk) disable iff (rst)
        out == sum_out
    );

    // The adder output must equal the sum of the two instance outputs.
    check_sum_out_matches_inputs: assert property (
        @(posedge clk) disable iff (rst)
        sum_out == (shift_reg_out + counter_out)
    );

    // One cycle after reset, all visible data outputs are cleared.
    check_reset_clears_visible_outputs: assert property (
        @(posedge clk) disable iff (rst)
        $past(rst) |-> (shift_reg_out == 4'b0000) &&
                       (counter_out   == 4'b0000) &&
                       (sum_out       == 4'b0000) &&
                       (out           == 4'b0000)
    );

    // A load updates the first instance shift-register path with data_in.
    check_shift_output_loads_data: assert property (
        @(posedge clk) disable iff (rst)
        !$past(rst) && $past(en && load) && !sel |-> (shift_reg_out == $past(data_in))
    );

    // Without a load, the first instance shift-register path holds when sel stays low.
    check_shift_output_holds_when_sel_low: assert property (
        @(posedge clk) disable iff (rst)
        !$past(rst) && $past(!sel) && !sel && !$past(en && load) |-> (shift_reg_out == $past(shift_reg_out))
    );

    // The second instance low-selected path holds its previous value.
    check_counter_low_path_holds: assert property (
        @(posedge clk) disable iff (rst)
        !$past(rst) && $past(!sel) && !sel |-> (counter_out == $past(counter_out))
    );

    // The second instance counter increments by one iff en was high when sel stays high.
    check_counter_high_path_behavior: assert property (
        @(posedge clk) disable iff (rst)
        !$past(rst) && $past(sel) && sel |-> (counter_out == ($past(counter_out) + ($past(en) ? 4'b0001 : 4'b0000)))
    );

    // The first instance counter increments by one only when en was high and load was low.
    check_shift_counter_high_path_behavior: assert property (
        @(posedge clk) disable iff (rst)
        !$past(rst) && $past(sel) && sel |-> (shift_reg_out == ($past(shift_reg_out) + ($past(en && !load) ? 4'b0001 : 4'b0000)))
    );

    // The top output holds when sel stays low and there was no prior load.
    check_top_output_holds_when_sel_low: assert property (
        @(posedge clk) disable iff (rst)
        !$past(rst) && $past(!sel) && !sel && !$past(en && load) |-> (out == $past(out))
    );

    // With sel high, the top output changes by 0, 1, or 2 based on en and load.
    check_top_output_high_path_behavior: assert property (
        @(posedge clk) disable iff (rst)
        !$past(rst) && $past(sel) && sel |-> (out == ($past(out) + ($past(en) ? ($past(load) ? 4'b0001 : 4'b0010) : 4'b0000)))
    );

endmodule