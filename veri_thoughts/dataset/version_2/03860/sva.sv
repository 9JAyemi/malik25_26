module mux_4_1_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic c,
    input logic d,
    input logic s0,
    input logic s1,
    input logic y
);

    // Output matches the full 4-to-1 mux equation.
    check_full_mux_function: assert property (
        @(posedge clk) y == (s1 ? (s0 ? d : c) : (s0 ? b : a))
    );

    // When s1 is low, y comes from the a/b mux selected by s0.
    check_lower_half_selected: assert property (
        @(posedge clk) !s1 |-> (y == (s0 ? b : a))
    );

    // When s1 is high, y comes from the c/d mux selected by s0.
    check_upper_half_selected: assert property (
        @(posedge clk) s1 |-> (y == (s0 ? d : c))
    );

    // When s0 is low, y selects between a and c using s1.
    check_s0_low_path: assert property (
        @(posedge clk) !s0 |-> (y == (s1 ? c : a))
    );

    // When s0 is high, y selects between b and d using s1.
    check_s0_high_path: assert property (
        @(posedge clk) s0 |-> (y == (s1 ? d : b))
    );

endmodule