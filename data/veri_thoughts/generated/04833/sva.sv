module calculator_sva (
    input logic clk,
    input logic areset,
    input logic load,
    input logic ena,
    input logic [2:0] bin_in,
    input logic shift_left,
    input logic operation,
    input logic [3:0] result
);

    // Reset forces the visible result to zero.
    check_reset_clears_result: assert property (
        @(posedge clk) areset |-> (result == 4'b0000)
    );

    // Load writes data_in[3:0], overriding any enabled shift.
    check_load_updates_result: assert property (
        @(posedge clk) disable iff (areset)
        load |=> (result == {$past(bin_in[0]), $past(bin_in[2]), $past(bin_in[1]), $past(bin_in[0])})
    );

    // Enabled left shift moves result left and inserts bin_in[2].
    check_shift_left_behavior: assert property (
        @(posedge clk) disable iff (areset)
        (!load && ena && shift_left) |=> (result == {$past(result[2:0]), $past(bin_in[2])})
    );

    // Enabled right shift moves result right and inserts bin_in[1].
    check_shift_right_behavior: assert property (
        @(posedge clk) disable iff (areset)
        (!load && ena && !shift_left) |=> (result == {$past(bin_in[1]), $past(result[3:1])})
    );

    // Without load or enable, result holds its value.
    check_idle_holds_result: assert property (
        @(posedge clk) disable iff (areset)
        (!load && !ena) |=> (result == $past(result))
    );

endmodule