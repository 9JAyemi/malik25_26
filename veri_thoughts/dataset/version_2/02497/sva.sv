module top_module_sva (
    input  logic        clk,
    input  logic        reset,       // synchronous active-high reset
    input  logic [255:0] in,
    input  logic [7:0]  sel,
    input  logic        direction,
    input  logic [2:0]  count,
    input  logic        out
);

    ///// Reset behavior /////
    // On a cycle where reset is 1, count becomes 0 on the next clock.
    reset_clears_count_next: assert property (
        @(posedge clk) reset |=> (count == 3'd0)
    );

    // While reset is held high across consecutive cycles, count is 0.
    reset_held_forces_zero: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (count == 3'd0)
    );

    ///// Counter step rules /////
    // When direction is 1 (and no reset), next count = prior count + 1 (mod 8).
    count_increments_on_dir1: assert property (
        @(posedge clk) disable iff (reset)
            (!$isunknown(count) && direction) |=> (reset || (count == ({1'b0,$past(count)} + 4'd1)[2:0]))
    );

    // When direction is 0 (and no reset), next count = prior count - 1 (mod 8).
    count_decrements_on_dir0: assert property (
        @(posedge clk) disable iff (reset)
            (!$isunknown(count) && !direction) |=> (reset || (count == ({1'b0,$past(count)} + 4'd7)[2:0]))
    );

    // On every non-reset cycle, next count changes by exactly +/-1 (mod 8).
    count_changes_by_one_each_cycle: assert property (
        @(posedge clk) disable iff (reset)
            (!$isunknown(count)) |=> (
                reset ||
                ({1'b0,count} == ({1'b0,$past(count)} + 4'd1)) ||
                ({1'b0,count} == ({1'b0,$past(count)} + 4'd7))
            )
    );

    ///// Combinational output function /////
    // out equals in[sel + count[1:0]] AND count[0].
    out_function_equivalence: assert property (
        @(posedge clk) disable iff (reset)
            (!$isunknown({count, sel, in})) |-> (out == (in[(sel + {6'd0, count[1:0]})] & count[0]))
    );

    // If count[0] is 0, out must be 0.
    out_zero_when_count_lsb_zero: assert property (
        @(posedge clk) disable iff (reset)
            (count[0] == 1'b0) |-> (out == 1'b0)
    );

    // If count[0] is 1, out equals the selected input bit.
    out_equals_selected_bit_when_count_lsb_one: assert property (
        @(posedge clk) disable iff (reset)
            (count[0] == 1'b1 && !$isunknown({sel, in})) |-> (out == in[(sel + {6'd0, count[1:0]})])
    );

    // If the selected input bit is 0, out must be 0.
    out_zero_when_selected_input_zero: assert property (
        @(posedge clk) disable iff (reset)
            (!$isunknown({sel, in})) && (in[(sel + {6'd0, count[1:0]})] == 1'b0) |-> (out == 1'b0)
    );

    // If the selected input bit and count[0] are 1, out must be 1.
    out_one_when_both_inputs_one: assert property (
        @(posedge clk) disable iff (reset)
            (!$isunknown({sel, in})) && (count[0] == 1'b1) && (in[(sel + {6'd0, count[1:0]})] == 1'b1) |-> (out == 1'b1)
    );

endmodule