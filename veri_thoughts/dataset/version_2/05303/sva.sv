module up_down_counter_sva (
    input logic clk,
    input logic rst,
    input logic en,
    input logic [3:0] count,
    input logic dir
);

    // Reset drives the default state.
    check_reset_values: assert property (
        @(posedge clk)
        (!rst) |-> ((count == 4'h0) && (dir == 1'b1))
    );

    // Count holds when enable is low.
    check_count_holds_when_disabled: assert property (
        @(posedge clk) disable iff (!rst)
        (!en) |=> (count == $past(count))
    );

    // Direction holds when enable is low.
    check_dir_holds_when_disabled: assert property (
        @(posedge clk) disable iff (!rst)
        (!en) |=> (dir == $past(dir))
    );

    // In up mode, count increments when below 15.
    check_count_increment_up: assert property (
        @(posedge clk) disable iff (!rst)
        (en && dir && (count != 4'hF)) |=> ((count == ($past(count) + 4'd1)) && (dir == 1'b0))
    );

    // In up mode, count wraps from 15 to 0.
    check_count_wrap_up: assert property (
        @(posedge clk) disable iff (!rst)
        (en && dir && (count == 4'hF)) |=> ((count == 4'h0) && (dir == 1'b0))
    );

    // In down mode, count decrements when above 0.
    check_count_decrement_down: assert property (
        @(posedge clk) disable iff (!rst)
        (en && !dir && (count != 4'h0)) |=> ((count == ($past(count) - 4'd1)) && (dir == 1'b1))
    );

    // In down mode, count wraps from 0 to 15.
    check_count_wrap_down: assert property (
        @(posedge clk) disable iff (!rst)
        (en && !dir && (count == 4'h0)) |=> ((count == 4'hF) && (dir == 1'b1))
    );

    // Direction toggles on every enabled cycle.
    check_dir_toggles_when_enabled: assert property (
        @(posedge clk) disable iff (!rst)
        en |=> (dir == ~$past(dir))
    );

    // Count changes on every enabled cycle.
    check_count_changes_when_enabled: assert property (
        @(posedge clk) disable iff (!rst)
        en |=> (count != $past(count))
    );

endmodule