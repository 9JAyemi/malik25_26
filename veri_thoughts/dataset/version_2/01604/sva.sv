module up_down_counter_sva (
    input logic clk,
    input logic reset,
    input logic up_down,
    input logic load,
    input logic [3:0] data_in,
    input logic [3:0] count
);
    // Reset high forces count to zero at the clock edge.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |-> (count == 4'b0000)
    );

    // With load asserted (no reset), next count captures data_in.
    check_load_captures_data: assert property (
        @(posedge clk) disable iff (reset) load |=> (count == $past(data_in))
    );

    // With load deasserted and up_down=1 (no reset), next count increments by 1 (mod 16).
    check_increment_when_up: assert property (
        @(posedge clk) disable iff (reset) (!load && up_down) |=> (count == ($past(count) + 4'd1))
    );

    // With load deasserted and up_down=0 (no reset), next count decrements by 1 (mod 16).
    check_decrement_when_down: assert property (
        @(posedge clk) disable iff (reset) (!load && !up_down) |=> (count == ($past(count) - 4'd1))
    );

    // Wrap-around on increment from 0xF to 0x0 when load deasserted (no reset).
    check_wrap_on_increment_from_max: assert property (
        @(posedge clk) disable iff (reset) (!load && up_down && ($past(count) == 4'hF)) |=> (count == 4'h0)
    );

    // Wrap-around on decrement from 0x0 to 0xF when load deasserted (no reset).
    check_wrap_on_decrement_from_zero: assert property (
        @(posedge clk) disable iff (reset) (!load && !up_down && ($past(count) == 4'h0)) |=> (count == 4'hF)
    );
endmodule