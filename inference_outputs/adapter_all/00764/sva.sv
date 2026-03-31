module xor_inv_multiplexer_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic sel_b1,
    input logic sel_b2,
    input logic sel_out,
    input logic out_always,
    input logic [3:0] out_xor,
    input logic [3:0] out_xor_inv,
    input logic out_logical_inv
);

    // out_xor is the XOR of the selected input with a.
    check_out_xor_function: assert property (
        @(posedge clk)
        out_xor == ((sel_b2 ? b : (sel_b1 ? b : a)) ^ a)
    );

    // out_xor_inv is the bitwise inversion of out_xor.
    check_out_xor_inv_function: assert property (
        @(posedge clk)
        out_xor_inv == ~out_xor
    );

    // out_logical_inv is the logical inversion of out_xor.
    check_out_logical_inv_function: assert property (
        @(posedge clk)
        out_logical_inv == !out_xor
    );

    // out_always captures the previous-cycle selected inverse output.
    check_out_always_registered_function: assert property (
        @(posedge clk)
        1'b1 |=> out_always == $past((sel_out ? !out_xor : ~out_xor))
    );

    // When sel_out is high, out_always reflects the previous-cycle logical inverse.
    check_out_always_selects_logical_inv: assert property (
        @(posedge clk)
        sel_out |=> out_always == $past(!out_xor)
    );

    // When sel_out is low, out_always reflects the previous-cycle XOR inverse.
    check_out_always_selects_xor_inv: assert property (
        @(posedge clk)
        !sel_out |=> out_always == $past(~out_xor)
    );

    // Equal XOR and logical inverse outputs imply the selected input equals a.
    check_equal_outputs_imply_selected_equals_a: assert property (
        @(posedge clk)
        (out_xor == out_logical_inv) |-> ((sel_b2 ? b : (sel_b1 ? b : a)) == a)
    );

    // Equal XOR and XOR inverse outputs imply the selected input differs from a.
    check_equal_xor_outputs_imply_selected_differs_a: assert property (
        @(posedge clk)
        (out_xor == out_xor_inv) |-> ((sel_b2 ? b : (sel_b1 ? b : a)) != a)
    );

endmodule