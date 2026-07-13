module top_module_sva (
    input logic clk,
    input logic load,
    input logic up_down,
    input logic [3:0] D,
    input logic [3:0] OUT,
    input logic [3:0] up_counter,
    input logic [3:0] down_counter
);

    // OUT is always the XOR of the two counters.
    check_out_is_counter_xor: assert property (
        @(posedge clk) OUT == (up_counter ^ down_counter)
    );

    // A load updates the up counter with D on the next cycle.
    check_load_updates_up_counter: assert property (
        @(posedge clk) load |=> (up_counter == $past(D))
    );

    // A load updates the down counter with D on the next cycle.
    check_load_updates_down_counter: assert property (
        @(posedge clk) load |=> (down_counter == $past(D))
    );

    // Loading both counters with the same value makes OUT zero.
    check_load_drives_zero_out: assert property (
        @(posedge clk) load |=> (OUT == 4'h0)
    );

    // In up mode, the up counter increments when not at 15.
    check_up_counter_increments: assert property (
        @(posedge clk) (!load && up_down && (up_counter != 4'hf)) |=> (up_counter == ($past(up_counter) + 4'h1))
    );

    // In up mode, the up counter wraps from 15 to 0.
    check_up_counter_wraps: assert property (
        @(posedge clk) (!load && up_down && (up_counter == 4'hf)) |=> (up_counter == 4'h0)
    );

    // In down mode, the up counter holds its value.
    check_up_counter_holds_in_down_mode: assert property (
        @(posedge clk) (!load && !up_down) |=> (up_counter == $past(up_counter))
    );

    // In down mode, the down counter decrements when not at 0.
    check_down_counter_decrements: assert property (
        @(posedge clk) (!load && !up_down && (down_counter != 4'h0)) |=> (down_counter == ($past(down_counter) - 4'h1))
    );

    // In down mode, the down counter wraps from 0 to 15.
    check_down_counter_wraps: assert property (
        @(posedge clk) (!load && !up_down && (down_counter == 4'h0)) |=> (down_counter == 4'hf)
    );

    // In up mode, the down counter holds its value.
    check_down_counter_holds_in_up_mode: assert property (
        @(posedge clk) (!load && up_down) |=> (down_counter == $past(down_counter))
    );

endmodule