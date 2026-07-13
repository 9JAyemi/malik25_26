module Control_assertions (
    input logic clk,
    input logic rst,
    input logic [7:0] in3,
    input logic [7:0] in2,
    input logic [7:0] in1,
    input logic [7:0] in0,
    input logic [3:0] anodo,
    input logic [7:0] catodo
);
    // During reset, outputs select in0 and anodo pattern 1110.
    reset_outputs_select0: assert property (
        @(posedge clk) rst |-> (anodo == 4'b1110) && (catodo == in0)
    );

    // anodo is always one of the four valid active-low one-hot patterns.
    anodo_valid_values: assert property (
        @(posedge clk) disable iff (rst) anodo inside {4'b1110, 4'b1101, 4'b1011, 4'b0111}
    );

    // When anodo selects digit0, catodo equals in0.
    map_sel0_cat_from_in0: assert property (
        @(posedge clk) disable iff (rst) (anodo == 4'b1110) |-> (catodo == in0)
    );

    // When anodo selects digit1, catodo equals in1.
    map_sel1_cat_from_in1: assert property (
        @(posedge clk) disable iff (rst) (anodo == 4'b1101) |-> (catodo == in1)
    );

    // When anodo selects digit2, catodo equals in2.
    map_sel2_cat_from_in2: assert property (
        @(posedge clk) disable iff (rst) (anodo == 4'b1011) |-> (catodo == in2)
    );

    // When anodo selects digit3, catodo equals in3.
    map_sel3_cat_from_in3: assert property (
        @(posedge clk) disable iff (rst) (anodo == 4'b0111) |-> (catodo == in3)
    );

    // Exactly one anodo bit is active (low).
    anodo_onehot_active_low: assert property (
        @(posedge clk) disable iff (rst) $onehot(~anodo)
    );

    // catodo always equals one of the four input buses.
    catodo_matches_some_input: assert property (
        @(posedge clk) disable iff (rst) (catodo == in0) || (catodo == in1) || (catodo == in2) || (catodo == in3)
    );

    // If anodo selects digit0 and both anodo and in0 are stable, catodo is stable.
    stable_catodo_when_sel0_stable: assert property (
        @(posedge clk) disable iff (rst) (anodo == 4'b1110 && $stable(anodo) && $stable(in0)) |-> $stable(catodo)
    );

    // If anodo selects digit1 and both anodo and in1 are stable, catodo is stable.
    stable_catodo_when_sel1_stable: assert property (
        @(posedge clk) disable iff (rst) (anodo == 4'b1101 && $stable(anodo) && $stable(in1)) |-> $stable(catodo)
    );

    // If anodo selects digit2 and both anodo and in2 are stable, catodo is stable.
    stable_catodo_when_sel2_stable: assert property (
        @(posedge clk) disable iff (rst) (anodo == 4'b1011 && $stable(anodo) && $stable(in2)) |-> $stable(catodo)
    );

    // If anodo selects digit3 and both anodo and in3 are stable, catodo is stable.
    stable_catodo_when_sel3_stable: assert property (
        @(posedge clk) disable iff (rst) (anodo == 4'b0111 && $stable(anodo) && $stable(in3)) |-> $stable(catodo)
    );

endmodule