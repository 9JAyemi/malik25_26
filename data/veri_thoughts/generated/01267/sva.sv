module four_bit_selector_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [1:0] o
);
    // Output matches the RTL's ternary mapping.
    check_functional_mapping: assert property (
        @(posedge clk) disable iff (1'b0)
            o == ((a < 5) ? a[1:0] : ((a >> 2)[3:2]))
    );

    // For a < 5, output equals the 2 LSBs of a.
    check_low_range_path: assert property (
        @(posedge clk) disable iff (1'b0)
            (a < 5) |-> (o == a[1:0])
    );

    // For a >= 5, output is zero because (a >> 2)[3:2] == 2'b00.
    check_high_range_zero: assert property (
        @(posedge clk) disable iff (1'b0)
            (a >= 5) |-> (o == 2'b00)
    );

    // Boundary: a == 4 drives o == 2'b00 (a[1:0]).
    check_boundary_a_eq_4: assert property (
        @(posedge clk) disable iff (1'b0)
            (a == 4) |-> (o == 2'b00)
    );

    // Boundary: a == 5 drives o == 2'b00 ((a >> 2)[3:2]).
    check_boundary_a_eq_5: assert property (
        @(posedge clk) disable iff (1'b0)
            (a == 5) |-> (o == 2'b00)
    );

    // If input is stable across cycles, output remains stable (pure combinational).
    check_output_stable_when_a_stable: assert property (
        @(posedge clk) disable iff (1'b0)
            $stable(a) |-> $stable(o)
    );

    // Transition from a < 5 to a >= 5 yields o == 2'b00 on the latter cycle.
    check_transition_low_to_high: assert property (
        @(posedge clk) disable iff (1'b0)
            (a < 5) ##1 (a >= 5) |-> (o == 2'b00)
    );

    // Transition from a >= 5 to a < 5 yields o == a[1:0] on the latter cycle.
    check_transition_high_to_low: assert property (
        @(posedge clk) disable iff (1'b0)
            (a >= 5) ##1 (a < 5) |-> (o == a[1:0])
    );

    // Any non-zero output implies a < 5 and equals a[1:0].
    check_nonzero_output_implies_low_range: assert property (
        @(posedge clk) disable iff (1'b0)
            (o != 2'b00) |-> ((a < 5) && (o == a[1:0]))
    );

    // Uniqueness: o == 2'b01 only occurs when a == 4'd1.
    check_unique_output_01: assert property (
        @(posedge clk) disable iff (1'b0)
            (o == 2'b01) |-> (a == 4'd1)
    );

    // Uniqueness: o == 2'b10 only occurs when a == 4'd2.
    check_unique_output_10: assert property (
        @(posedge clk) disable iff (1'b0)
            (o == 2'b10) |-> (a == 4'd2)
    );

    // Uniqueness: o == 2'b11 only occurs when a == 4'd3.
    check_unique_output_11: assert property (
        @(posedge clk) disable iff (1'b0)
            (o == 2'b11) |-> (a == 4'd3)
    );
endmodule