module up_down_counter_sva (
    input logic clk,
    input logic up_down,
    input logic load,
    input logic [3:0] input_data,
    input logic [3:0] Q
);
    // When load is HIGH, next Q equals current input_data.
    check_load_captures_input_data: assert property (
        @(posedge clk) load |=> (Q == $past(input_data))
    );

    // When load is LOW and up_down is HIGH, next Q increments by 1 (mod 16).
    check_increment_when_up: assert property (
        @(posedge clk) (!load && up_down) |=> (Q == (($past(Q) + 1) & 4'hF))
    );

    // When load is LOW and up_down is LOW, next Q decrements by 1 (mod 16).
    check_decrement_when_down: assert property (
        @(posedge clk) (!load && !up_down) |=> (Q == (($past(Q) - 1) & 4'hF))
    );

    // Increment from 0xF wraps to 0x0 when not loading.
    check_wrap_increment_from_max: assert property (
        @(posedge clk) (!load && up_down && (Q == 4'hF)) |=> (Q == 4'h0)
    );

    // Decrement from 0x0 wraps to 0xF when not loading.
    check_wrap_decrement_from_min: assert property (
        @(posedge clk) (!load && !up_down && (Q == 4'h0)) |=> (Q == 4'hF)
    );

    // Each cycle Q equals the function of prior-cycle controls and data.
    check_functional_update_each_cycle: assert property (
        @(posedge clk)
        Q == ( $past(load)
               ? $past(input_data)
               : ( $past(up_down)
                   ? (($past(Q) + 1) & 4'hF)
                   : (($past(Q) - 1) & 4'hF)))
    );

    // Two consecutive UP steps (no load) increment Q by 2 (mod 16).
    check_two_cycle_increment: assert property (
        @(posedge clk) (!load && up_down) ##1 (!load && up_down) |=> (Q == (($past(Q,2) + 2) & 4'hF))
    );

    // Two consecutive DOWN steps (no load) decrement Q by 2 (mod 16).
    check_two_cycle_decrement: assert property (
        @(posedge clk) (!load && !up_down) ##1 (!load && !up_down) |=> (Q == (($past(Q,2) - 2) & 4'hF))
    );

    // UP followed by DOWN with no loads returns Q to original value after 2 cycles.
    check_up_then_down_cancels: assert property (
        @(posedge clk) (!load && up_down) ##1 (!load && !up_down) |=> (Q == $past(Q,2))
    );

    // DOWN followed by UP with no loads returns Q to original value after 2 cycles.
    check_down_then_up_cancels: assert property (
        @(posedge clk) (!load && !up_down) ##1 (!load && up_down) |=> (Q == $past(Q,2))
    );

    // Two consecutive loads use the second cycle's input_data value.
    check_two_consecutive_loads_use_second_value: assert property (
        @(posedge clk) load ##1 load |=> (Q == $past(input_data,1))
    );
endmodule