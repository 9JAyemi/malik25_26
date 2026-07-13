module comparator_sva (
    input logic clk,          // External sampling clock for assertions
    input logic [1:0] in_0,   // DUT input
    input logic [1:0] in_1,   // DUT input
    input logic [1:0] out     // DUT output
);
    // Analysis: No clock/reset in RTL; pure combinational comparator; out encodes: 01(gt), 10(eq), 00(lt).

    ///// Functional mapping from inputs to output /////
    // If in_0 > in_1 then out must be 01.
    check_map_gt_to_01: assert property (
        @(posedge clk) (in_0 > in_1) |-> (out == 2'b01)
    );

    // If in_0 == in_1 then out must be 10.
    check_map_eq_to_10: assert property (
        @(posedge clk) (in_0 == in_1) |-> (out == 2'b10)
    );

    // If neither (in_0 > in_1) nor (in_0 == in_1) then out must be 00 (else branch).
    check_map_else_to_00: assert property (
        @(posedge clk) (!(in_0 > in_1) && !(in_0 == in_1)) |-> (out == 2'b00)
    );

    ///// Output code consistency /////
    // out never takes the invalid code 11.
    check_out_never_11: assert property (
        @(posedge clk) out != 2'b11
    );

    ///// Output implies condition (no spurious codes) /////
    // If out is 01, then in_0 > in_1 must have been true.
    check_out_01_implies_gt: assert property (
        @(posedge clk) (out == 2'b01) |-> (in_0 > in_1)
    );

    // If out is 10, then in_0 == in_1 must have been true.
    check_out_10_implies_eq: assert property (
        @(posedge clk) (out == 2'b10) |-> (in_0 == in_1)
    );

    ///// Stability under stable inputs /////
    // If inputs are stable across a cycle, output remains stable.
    check_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(in_0) && $stable(in_1)) |-> $stable(out)
    );

endmodule