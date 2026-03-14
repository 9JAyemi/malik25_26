module my_module_sva (
    input  logic in1,
    input  logic in2,
    input  logic in3,
    input  logic in4,
    input  logic in5,
    input  logic in6,
    input  logic in7,
    input  logic in8,
    input  logic c1,
    input  logic b1,
    input  logic a2,
    input  logic a1,
    input  logic out1
);
    ///// Combinational AND definition /////
    // out1 must equal a1 & a2 & b1 & c1 whenever any of these inputs toggle HIGH.
    check_out1_is_and: assert property (
        @(posedge a1 or posedge a2 or posedge b1 or posedge c1)
            out1 == (a1 & a2 & b1 & c1)
    );

    ///// Basic implications of AND /////
    // If all inputs are 1, out1 must be 1.
    check_all_ones_impl_out1_one: assert property (
        @(posedge a1 or posedge a2 or posedge b1 or posedge c1)
            (a1 & a2 & b1 & c1) |-> (out1 == 1'b1)
    );
    // If any input is 0, out1 must be 0.
    check_any_zero_impl_out1_zero: assert property (
        @(posedge a1 or posedge a2 or posedge b1 or posedge c1)
            ((!a1) || (!a2) || (!b1) || (!c1)) |-> (out1 == 1'b0)
    );
    // If out1 is 1, all inputs must be 1.
    check_out1_one_impl_all_ones: assert property (
        @(posedge a1 or posedge a2 or posedge b1 or posedge c1)
            (out1 == 1'b1) |-> (a1 & a2 & b1 & c1)
    );

    ///// Output transition consistency /////
    // A rising edge on out1 can only occur when all inputs are 1.
    check_out1_rise_requires_all_ones: assert property (
        @(posedge a1 or posedge a2 or posedge b1 or posedge c1)
            $rose(out1) |-> (a1 & a2 & b1 & c1)
    );
    // A falling edge on out1 implies at least one input is 0.
    check_out1_fall_requires_some_zero: assert property (
        @(posedge a1 or posedge a2 or posedge b1 or posedge c1)
            $fell(out1) |-> !(a1 & a2 & b1 & c1)
    );
    // out1 can only change if at least one of a1/a2/b1/c1 changes.
    check_out1_changes_only_with_controls: assert property (
        @(posedge a1 or posedge a2 or posedge b1 or posedge c1 or
          posedge in1 or posedge in2 or posedge in3 or posedge in4 or
          posedge in5 or posedge in6 or posedge in7 or posedge in8)
            $changed(out1) |-> !($stable(a1) && $stable(a2) && $stable(b1) && $stable(c1))
    );

    ///// Independence from unused inputs /////
    // Changes on in1..in8 alone must not affect out1 (controls stable).
    check_unused_inputs_do_not_affect_out: assert property (
        @(posedge in1 or posedge in2 or posedge in3 or posedge in4 or
          posedge in5 or posedge in6 or posedge in7 or posedge in8)
            ($stable(a1) && $stable(a2) && $stable(b1) && $stable(c1)) |-> $stable(out1)
    );
endmodule