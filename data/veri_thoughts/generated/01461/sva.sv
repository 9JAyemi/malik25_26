module top_module_sva (
    input logic clk,
    input logic reset,
    input logic slowena,
    input logic [2:0] select,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [3:0] c,
    input logic [3:0] q,
    // Internal signals from RTL
    input logic [3:0] counter,
    input logic [3:0] w
);

    ///// Counter behavior /////
    // While reset is asserted (active-low), counter is 0.
    reset_forces_counter_zero: assert property (
        @(posedge clk) !reset |-> (counter == 4'd0)
    );

    // When enabled, counter increments by 1 on the next cycle.
    counter_increments_when_enabled: assert property (
        @(posedge clk) disable iff (!reset) slowena |=> (counter == $past(counter) + 4'd1)
    );

    // When not enabled, counter holds its value.
    counter_holds_when_disabled: assert property (
        @(posedge clk) disable iff (!reset) !slowena |=> (counter == $past(counter))
    );

    ///// Output selection /////
    // When select is 3'b011, q equals counter.
    q_selects_counter_on_011: assert property (
        @(posedge clk) disable iff (!reset) (select == 3'b011) |-> (q == counter)
    );

    // When select is not 3'b011, q equals w.
    q_equals_w_when_not_011: assert property (
        @(posedge clk) disable iff (!reset) (select != 3'b011) |-> (q == w)
    );

    ///// w mux behavior /////
    // When select is 3'b000, w equals a.
    w_selects_a_on_000: assert property (
        @(posedge clk) disable iff (!reset) (select == 3'b000) |-> (w == a)
    );

    // When select is 3'b001, w equals b.
    w_selects_b_on_001: assert property (
        @(posedge clk) disable iff (!reset) (select == 3'b001) |-> (w == b)
    );

    // When select is 3'b010, w equals c.
    w_selects_c_on_010: assert property (
        @(posedge clk) disable iff (!reset) (select == 3'b010) |-> (w == c)
    );

    // For all other select values, w is 0.
    w_zero_on_other_selects: assert property (
        @(posedge clk) disable iff (!reset) ((select != 3'b000) && (select != 3'b001) && (select != 3'b010)) |-> (w == 4'd0)
    );

endmodule