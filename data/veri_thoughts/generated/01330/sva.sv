module top_module_sva (
    input logic clk,
    input logic reset,
    input logic up_down,
    input logic load,
    input logic [3:0] data_in,
    input logic [3:0] count,
    input logic [3:0] sum
);
    // Reset drives outputs to zero.
    check_reset_outputs_zero: assert property (
        @(posedge clk) reset |-> (count == 4'h0) && (sum == 4'h0)
    );

    // On load, next cycle count equals data_in.
    check_count_load_next: assert property (
        @(posedge clk) disable iff (reset) load |=> (count == $past(data_in))
    );

    // On load, next cycle sum equals data_in + data_in (mod 16).
    check_sum_load_next: assert property (
        @(posedge clk) disable iff (reset) load |=> (sum == (($past(data_in) + $past(data_in)) & 4'hF))
    );

    // With no load in consecutive cycles, sum holds its previous value.
    check_sum_stable_no_load: assert property (
        @(posedge clk) disable iff (reset) ($past(!reset) && !load && !$past(load)) |-> (sum == $past(sum))
    );

    // If sum changes, a load must have occurred in the previous cycle.
    check_sum_change_implies_prev_load: assert property (
        @(posedge clk) disable iff (reset) ($past(!reset) && (sum != $past(sum))) |-> $past(load)
    );

    // With up_down=1 and no load in consecutive cycles, count increments by 1 (mod 16).
    check_count_inc_when_up: assert property (
        @(posedge clk) disable iff (reset)
            ( $past(!reset) && up_down && $past(up_down) && !load && !$past(load) )
            |-> (count == (($past(count) + 4'd1) & 4'hF))
    );

    // With up_down=0 and no load in consecutive cycles, count decrements by 1 (mod 16).
    check_count_dec_when_down: assert property (
        @(posedge clk) disable iff (reset)
            ( $past(!reset) && !up_down && !$past(up_down) && !load && !$past(load) )
            |-> (count == (($past(count) - 4'd1) & 4'hF))
    );

    // First cycle after reset deasserts, sum is zero.
    check_sum_zero_after_reset_release: assert property (
        @(posedge clk) ($past(reset) && !reset) |-> (sum == 4'h0)
    );

    // On back-to-back load cycles, count tracks the previous cycle's data_in each time.
    check_count_back_to_back_loads: assert property (
        @(posedge clk) disable iff (reset) ($past(!reset) && load && $past(load)) |-> (count == $past(data_in))
    );
endmodule