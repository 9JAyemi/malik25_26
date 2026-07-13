module or4_2_custom_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

// X equals A|B|C|D whenever any input changes.
    check_or_function_on_input_change: assert property (
        @(posedge clk) disable iff (1'b0)
        ($changed(A) || $changed(B) || $changed(C) || $changed(D)) |-> (X == (A | B | C | D))
    );

// X equals A|B|C|D whenever any power/gate input changes.
    check_or_function_on_power_change: assert property (
        @(posedge clk) disable iff (1'b0)
        ($changed(VPWR) || $changed(VGND) || $changed(VPB) || $changed(VNB)) |-> (X == (A | B | C | D))
    );

// X is 0 when all data inputs are 0.
    check_zero_when_all_zero: assert property (
        @(posedge clk) disable iff (1'b0)
        (!A && !B && !C && !D) |-> (X == 1'b0)
    );

// X is 1 when any data input is 1.
    check_one_when_any_one: assert property (
        @(posedge clk) disable iff (1'b0)
        (A || B || C || D) |-> (X == 1'b1)
    );

// A rising edge on X implies at least one data input is 1.
    check_x_rise_has_cause: assert property (
        @(posedge clk) disable iff (1'b0)
        $rose(X) |-> (A || B || C || D)
    );

// A falling edge on X implies all data inputs are 0.
    check_x_fall_has_cause: assert property (
        @(posedge clk) disable iff (1'b0)
        $fell(X) |-> (!A && !B && !C && !D)
    );

endmodule
