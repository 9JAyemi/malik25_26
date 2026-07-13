module mux_2to1_assertions (
    input logic clk,
    input logic A,
    input logic B,
    input logic SEL,
    input logic Y
);

    // Output matches the RTL mux expression on every sampled cycle.
    check_mux_function: assert property (
        @(posedge clk) Y === ((SEL == 1'b1) ? A : B)
    );

    // When select is HIGH, output follows A.
    check_select_high_routes_a: assert property (
        @(posedge clk) (SEL === 1'b1) |-> (Y === A)
    );

    // When select is LOW, output follows B.
    check_select_low_routes_b: assert property (
        @(posedge clk) (SEL === 1'b0) |-> (Y === B)
    );

    // Equal inputs produce the same output regardless of select.
    check_equal_inputs_same_output: assert property (
        @(posedge clk) (A === B) |-> (Y === A)
    );

    // Changes on unselected B do not affect Y when A remains selected.
    check_unselected_b_ignored: assert property (
        @(posedge clk) (SEL === 1'b1 && $stable(SEL) && $stable(A) && !$stable(B)) |-> $stable(Y)
    );

    // Changes on unselected A do not affect Y when B remains selected.
    check_unselected_a_ignored: assert property (
        @(posedge clk) (SEL === 1'b0 && $stable(SEL) && $stable(B) && !$stable(A)) |-> $stable(Y)
    );

    // Toggling select does not change Y when both inputs are equal and stable.
    check_select_toggle_ignored_when_inputs_equal: assert property (
        @(posedge clk) ($stable(A) && $stable(B) && (A === B) && !$stable(SEL)) |-> ($stable(Y) && (Y === A))
    );

endmodule