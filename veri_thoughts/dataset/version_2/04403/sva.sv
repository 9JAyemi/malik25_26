module top_module_sva (
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] sel,
    input logic       reset,
    input logic [3:0] out_assign,
    input logic [3:0] out_alwaysblock
);

    // reset is active high and is the only edge-triggered signal.
    // out_alwaysblock is combinational; out_assign only updates on posedge reset.

    // out_alwaysblock selects in0 when sel is 2'b00.
    check_out_alwaysblock_sel_00: assert property (
        @(negedge reset) disable iff (reset)
        (sel === 2'b00) |-> (out_alwaysblock == in0)
    );

    // out_alwaysblock selects in1 when sel is 2'b01.
    check_out_alwaysblock_sel_01: assert property (
        @(negedge reset) disable iff (reset)
        (sel === 2'b01) |-> (out_alwaysblock == in1)
    );

    // out_alwaysblock selects in2 when sel is 2'b10.
    check_out_alwaysblock_sel_10: assert property (
        @(negedge reset) disable iff (reset)
        (sel === 2'b10) |-> (out_alwaysblock == in2)
    );

    // out_alwaysblock selects in3 when sel is 2'b11.
    check_out_alwaysblock_sel_11: assert property (
        @(negedge reset) disable iff (reset)
        (sel === 2'b11) |-> (out_alwaysblock == in3)
    );

    // out_alwaysblock drives zero on the case default branch.
    check_out_alwaysblock_default: assert property (
        @(negedge reset) disable iff (reset)
        ((sel[1] !== 1'b0) && (sel[1] !== 1'b1)) |-> (out_alwaysblock == 4'b0000)
    );

    // After a prior reset assertion, out_assign is cleared to zero.
    check_out_assign_cleared_by_reset: assert property (
        @(negedge reset) disable iff (reset)
        !$isunknown($past(reset, 1, 1'b1, @(posedge reset))) |-> (out_assign == 4'b0000)
    );

endmodule