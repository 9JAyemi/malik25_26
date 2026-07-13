module add_sub_comp_sva (
    input logic clk,           // Sampling clock for assertions (DUT has no clock/reset)
    input logic [3:0] a,       // DUT input
    input logic [3:0] b,       // DUT input
    input logic sub,           // DUT input (does not affect out)
    input logic out            // DUT output: 1 when a < b, else 0
);
    // Analysis: No clock/reset in RTL; pure combinational. out=1 iff a<b; sub does not affect out.

    ///// Functional equivalence /////
    // out must reflect comparator result: out == (a < b).
    check_out_equals_less: assert property (
        @(posedge clk) out == (a < b)
    );

    ///// Case-specific behavior /////
    // When a < b, out is 1.
    check_out_one_when_less: assert property (
        @(posedge clk) (a < b) |-> (out == 1'b1)
    );
    // When a >= b, out is 0.
    check_out_zero_when_ge: assert property (
        @(posedge clk) (a >= b) |-> (out == 1'b0)
    );

    ///// Independence from sub /////
    // Changes on sub do not affect out when a and b are stable.
    check_out_independent_of_sub_when_inputs_stable: assert property (
        @(posedge clk) ($stable(a) && $stable(b) && (sub != $past(sub))) |-> $stable(out)
    );

    ///// Combinational determinism /////
    // If a and b are stable, out must remain stable.
    check_out_stable_if_inputs_stable: assert property (
        @(posedge clk) ($stable(a) && $stable(b)) |-> $stable(out)
    );

endmodule