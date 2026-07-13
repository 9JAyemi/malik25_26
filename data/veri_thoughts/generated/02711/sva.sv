module calculator_sva (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic       op,
    input logic [7:0] result
);
    // Combinational result matches selected op (mod 256) on any input change.
    check_result_matches_op: assert property (
        @(posedge a[0] or negedge a[0] or
          posedge a[1] or negedge a[1] or
          posedge a[2] or negedge a[2] or
          posedge a[3] or negedge a[3] or
          posedge a[4] or negedge a[4] or
          posedge a[5] or negedge a[5] or
          posedge a[6] or negedge a[6] or
          posedge a[7] or negedge a[7] or
          posedge b[0] or negedge b[0] or
          posedge b[1] or negedge b[1] or
          posedge b[2] or negedge b[2] or
          posedge b[3] or negedge b[3] or
          posedge b[4] or negedge b[4] or
          posedge b[5] or negedge b[5] or
          posedge b[6] or negedge b[6] or
          posedge b[7] or negedge b[7] or
          posedge op   or negedge op)
        {1'b0, result} == ( (op == 1'b0)
                            ? (({1'b0, a} + {1'b0, b}) & 9'h0FF)
                            : (({1'b0, a} - {1'b0, b}) & 9'h0FF) )
    );

    // When op selects addition, result equals a+b (mod 256) on any input change.
    check_add_branch: assert property (
        @(posedge a[0] or negedge a[0] or
          posedge a[1] or negedge a[1] or
          posedge a[2] or negedge a[2] or
          posedge a[3] or negedge a[3] or
          posedge a[4] or negedge a[4] or
          posedge a[5] or negedge a[5] or
          posedge a[6] or negedge a[6] or
          posedge a[7] or negedge a[7] or
          posedge b[0] or negedge b[0] or
          posedge b[1] or negedge b[1] or
          posedge b[2] or negedge b[2] or
          posedge b[3] or negedge b[3] or
          posedge b[4] or negedge b[4] or
          posedge b[5] or negedge b[5] or
          posedge b[6] or negedge b[6] or
          posedge b[7] or negedge b[7] or
          posedge op   or negedge op)
        (op == 1'b0) |-> ( {1'b0, result} == (({1'b0, a} + {1'b0, b}) & 9'h0FF) )
    );

    // When op selects subtraction, result equals a-b (mod 256) on any input change.
    check_sub_branch: assert property (
        @(posedge a[0] or negedge a[0] or
          posedge a[1] or negedge a[1] or
          posedge a[2] or negedge a[2] or
          posedge a[3] or negedge a[3] or
          posedge a[4] or negedge a[4] or
          posedge a[5] or negedge a[5] or
          posedge a[6] or negedge a[6] or
          posedge a[7] or negedge a[7] or
          posedge b[0] or negedge b[0] or
          posedge b[1] or negedge b[1] or
          posedge b[2] or negedge b[2] or
          posedge b[3] or negedge b[3] or
          posedge b[4] or negedge b[4] or
          posedge b[5] or negedge b[5] or
          posedge b[6] or negedge b[6] or
          posedge b[7] or negedge b[7] or
          posedge op   or negedge op)
        (op == 1'b1) |-> ( {1'b0, result} == (({1'b0, a} - {1'b0, b}) & 9'h0FF) )
    );

    // If only a changes, result updates immediately per selected op (mod 256).
    check_update_on_a_change: assert property (
        @(posedge a[0] or negedge a[0] or
          posedge a[1] or negedge a[1] or
          posedge a[2] or negedge a[2] or
          posedge a[3] or negedge a[3] or
          posedge a[4] or negedge a[4] or
          posedge a[5] or negedge a[5] or
          posedge a[6] or negedge a[6] or
          posedge a[7] or negedge a[7])
        ($changed(a) && $stable(b) && $stable(op))
        |-> ({1'b0, result} == ( (op == 1'b0)
                                 ? (({1'b0, a} + {1'b0, b}) & 9'h0FF)
                                 : (({1'b0, a} - {1'b0, b}) & 9'h0FF) ))
    );

    // If only b changes, result updates immediately per selected op (mod 256).
    check_update_on_b_change: assert property (
        @(posedge b[0] or negedge b[0] or
          posedge b[1] or negedge b[1] or
          posedge b[2] or negedge b[2] or
          posedge b[3] or negedge b[3] or
          posedge b[4] or negedge b[4] or
          posedge b[5] or negedge b[5] or
          posedge b[6] or negedge b[6] or
          posedge b[7] or negedge b[7])
        ($changed(b) && $stable(a) && $stable(op))
        |-> ({1'b0, result} == ( (op == 1'b0)
                                 ? (({1'b0, a} + {1'b0, b}) & 9'h0FF)
                                 : (({1'b0, a} - {1'b0, b}) & 9'h0FF) ))
    );

    // Result cannot change unless at least one input (a, b, or op) changed.
    check_result_change_requires_input_change: assert property (
        @(posedge result[0] or negedge result[0] or
          posedge result[1] or negedge result[1] or
          posedge result[2] or negedge result[2] or
          posedge result[3] or negedge result[3] or
          posedge result[4] or negedge result[4] or
          posedge result[5] or negedge result[5] or
          posedge result[6] or negedge result[6] or
          posedge result[7] or negedge result[7])
        (!$stable(a) || !$stable(b) || !$stable(op))
    );
endmodule