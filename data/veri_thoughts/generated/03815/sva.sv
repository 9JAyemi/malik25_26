module up_down_counter_sva (
    input logic       CLK,
    input logic       UP,
    input logic       DOWN,
    input logic       LOAD,
    input logic [3:0] in,
    input logic [3:0] OUT
);

    // LOAD has highest priority and copies in to OUT.
    check_load_captures_input: assert property (
        @(posedge CLK) LOAD |=> (OUT == $past(in))
    );

    // UP increments OUT when LOAD is low and OUT is not at max.
    check_count_up_step: assert property (
        @(posedge CLK) (!LOAD && UP && (OUT != 4'hF)) |=> (OUT == ($past(OUT) + 4'd1))
    );

    // UP wraps OUT from 15 to 0 when LOAD is low.
    check_count_up_wrap: assert property (
        @(posedge CLK) (!LOAD && UP && (OUT == 4'hF)) |=> (OUT == 4'h0)
    );

    // DOWN decrements OUT when selected and OUT is not zero.
    check_count_down_step: assert property (
        @(posedge CLK) (!LOAD && !UP && DOWN && (OUT != 4'h0)) |=> (OUT == ($past(OUT) - 4'd1))
    );

    // DOWN wraps OUT from 0 to 15 when selected.
    check_count_down_wrap: assert property (
        @(posedge CLK) (!LOAD && !UP && DOWN && (OUT == 4'h0)) |=> (OUT == 4'hF)
    );

    // OUT holds its value when no control input is asserted.
    check_hold_when_idle: assert property (
        @(posedge CLK) (!LOAD && !UP && !DOWN) |=> (OUT == $past(OUT))
    );

endmodule