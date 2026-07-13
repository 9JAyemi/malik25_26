module mux_with_nor_gate_sva (
    input logic a,
    input logic b,
    input logic c,
    input logic control,
    input logic w,
    input logic x,
    input logic y,
    input logic z
);
    // No clock/reset in RTL; pure combinational. Sample assertions on posedge of 'a'.

    // Replicated outputs must equal w.
    check_outputs_equal_w: assert property (
        @(posedge a) (x == w) && (y == w) && (z == w)
    );

    // When control is exactly 0, w must equal a.
    check_w_select_a_when_control_0: assert property (
        @(posedge a) (control === 1'b0) |-> (w == a)
    );

    // When control is exactly 1, w must equal b.
    check_w_select_b_when_control_1: assert property (
        @(posedge a) (control === 1'b1) |-> (w == b)
    );

    // When control is neither 0 nor 1, w must equal c.
    check_w_select_c_when_control_unknown: assert property (
        @(posedge a) ((control !== 1'b0) && (control !== 1'b1)) |-> (w == c)
    );

    // When control is exactly 0, all outputs must equal a.
    check_all_select_a_when_control_0: assert property (
        @(posedge a) (control === 1'b0) |-> ((x == a) && (y == a) && (z == a))
    );

    // When control is exactly 1, all outputs must equal b.
    check_all_select_b_when_control_1: assert property (
        @(posedge a) (control === 1'b1) |-> ((x == b) && (y == b) && (z == b))
    );

    // When control is neither 0 nor 1, all outputs must equal c.
    check_all_select_c_when_control_unknown: assert property (
        @(posedge a) ((control !== 1'b0) && (control !== 1'b1)) |-> ((x == c) && (y == c) && (z == c))
    );

endmodule