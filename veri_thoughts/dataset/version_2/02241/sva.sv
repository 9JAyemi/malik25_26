module bitwise_logical_mux_sva (
    input logic [2:0] a,
    input logic [2:0] b,
    input logic sel_b1,
    input logic sel_b2,
    input logic [2:0] out_or_bitwise,
    input logic out_or_logical,
    input logic [5:0] out_not
);
    // Bitwise OR output must equal a | b.
    check_out_or_bitwise_matches_a_or_b: assert property (
        @(posedge a[0] or posedge a[1] or posedge a[2] or
          posedge b[0] or posedge b[1] or posedge b[2] or
          posedge sel_b1 or posedge sel_b2)
        (out_or_bitwise == (a | b))
    );

    // Logical OR output must equal (|a) || (|b).
    check_out_or_logical_matches_reduce_or_of_inputs: assert property (
        @(posedge a[0] or posedge a[1] or posedge a[2] or
          posedge b[0] or posedge b[1] or posedge b[2] or
          posedge sel_b1 or posedge sel_b2)
        (out_or_logical == ((a[0] || a[1] || a[2]) || (b[0] || b[1] || b[2])))
    );

    // Inverted output must equal {~b, ~a}.
    check_out_not_matches_inverse_concat: assert property (
        @(posedge a[0] or posedge a[1] or posedge a[2] or
          posedge b[0] or posedge b[1] or posedge b[2] or
          posedge sel_b1 or posedge sel_b2)
        (out_not == {~b, ~a})
    );

    // Logical OR must equal reduction-OR of the bitwise OR output.
    check_out_or_logical_is_reduction_of_out_or_bitwise: assert property (
        @(posedge a[0] or posedge a[1] or posedge a[2] or
          posedge b[0] or posedge b[1] or posedge b[2] or
          posedge sel_b1 or posedge sel_b2)
        (out_or_logical == (|out_or_bitwise))
    );

    // Outputs must not change if inputs a and b are stable.
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge a[0] or posedge a[1] or posedge a[2] or
          posedge b[0] or posedge b[1] or posedge b[2] or
          posedge sel_b1 or posedge sel_b2)
        ($stable(a) && $stable(b)) |-> ($stable(out_or_bitwise) && $stable(out_or_logical) && $stable(out_not))
    );

    // Changing sel_b1 alone must not affect outputs.
    check_outputs_unchanged_on_sel_b1_rise_when_inputs_stable: assert property (
        @(posedge sel_b1)
        ($stable(a) && $stable(b)) |-> (out_or_bitwise == $past(out_or_bitwise) &&
                                        out_or_logical == $past(out_or_logical) &&
                                        out_not == $past(out_not))
    );

    // Changing sel_b2 alone must not affect outputs.
    check_outputs_unchanged_on_sel_b2_rise_when_inputs_stable: assert property (
        @(posedge sel_b2)
        ($stable(a) && $stable(b)) |-> (out_or_bitwise == $past(out_or_bitwise) &&
                                        out_or_logical == $past(out_or_logical) &&
                                        out_not == $past(out_not))
    );

    // When both inputs are zero, outputs are zero/zero and inverted all-ones.
    check_zero_inputs_outputs_consistency: assert property (
        @(posedge a[0] or posedge a[1] or posedge a[2] or
          posedge b[0] or posedge b[1] or posedge b[2] or
          posedge sel_b1 or posedge sel_b2)
        ((a == 3'b000) && (b == 3'b000)) |-> (out_or_bitwise == 3'b000 && out_or_logical == 1'b0 && out_not == 6'b111111)
    );

    // If any bit of a or b is 1, logical OR must be 1.
    check_nonzero_inputs_set_logical_or: assert property (
        @(posedge a[0] or posedge a[1] or posedge a[2] or
          posedge b[0] or posedge b[1] or posedge b[2] or
          posedge sel_b1 or posedge sel_b2)
        (((a != 3'b000) || (b != 3'b000)) |-> (out_or_logical == 1'b1))
    );

    // Lower out_not bits must match ~a and upper bits must match ~b.
    check_out_not_bit_mapping: assert property (
        @(posedge a[0] or posedge a[1] or posedge a[2] or
          posedge b[0] or posedge b[1] or posedge b[2] or
          posedge sel_b1 or posedge sel_b2)
        ((out_not[2:0] == ~a) && (out_not[5:3] == ~b))
    );
endmodule