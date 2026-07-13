module shift_right_sva (
    input logic clk,
    input logic rst,
    input logic ld,
    input logic shift,
    input logic [63:0] x,
    output logic out
);
    // Reset behavior: At reset, shiftreg and out should be 0
    reset: assert property (
        @(posedge clk) disable iff (!rst) (rst |-> (shiftreg == 64'b0) && (out == 1'b0))
    );

    // Load behavior: When ld is high, shiftreg should be loaded with x and out should be 0
    load: assert property (
        @(posedge clk) disable iff (!rst) (ld |-> (shiftreg == x) && (out == 1'b0))
    );

    // Shift behavior: When shift is high, out should be the least significant bit of shiftreg and shiftreg should be shifted right by one bit
    shift_right_behavior: assert property (
        @(posedge clk) disable iff (!rst) (shift |-> (out == shiftreg[0]) && (shiftreg == {1'b0, shiftreg[63:1]}))
    );

    // Ensure that out is not driven by any other logic when not in a transition state
    out_stable: assert property (
        @(posedge clk) disable iff (!rst) (!shift && !ld |-> out == out)
    );

    // Ensure that shiftreg is not driven by any other logic when not in a transition state
    shiftreg_stable: assert property (
        @(posedge clk) disable iff (!rst) (!shift && !ld |-> shiftreg == shiftreg)
    );

    // Ensure that ld and shift cannot be high at the same time
    ld_shift_exclusive: assert property (
        @(posedge clk) disable iff (!rst) (!(ld && shift))
    );

    // Ensure that out is always 0 when shiftreg is 0
    out_zero_when_shiftreg_zero: assert property (
        @(posedge clk) disable iff (!rst) (shiftreg == 64'b0 |-> out == 1'b0)
    );

    // Ensure that out is always 1 when shiftreg is all 1s
    out_one_when_shiftreg_all_ones: assert property (
        @(posedge clk) disable iff (!rst) (shiftreg == 64'b1111111111111111111111111111111111111111111111111111111111111111 |-> out == 1'b1)
    );

    // Ensure that shiftreg is always 0 when out is 0
    shiftreg_zero_when_out_zero: assert property (
        @(posedge clk) disable iff (!rst) (out == 1'b0 |-> shiftreg == 64'b0)
    );

    // Ensure that shiftreg is always all 1s when out is 1
    shiftreg_all_ones_when_out_one: assert property (
        @(posedge clk) disable iff (!rst) (out == 1'b1 |-> shiftreg == 64'b1111111111111111111111111111111111111111111111111111111111111111)
    );
endmodule