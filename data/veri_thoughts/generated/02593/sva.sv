module top_module_sva (
    input logic CLK,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] in,
    input logic select,
    input logic [15:0] out
);
    // When select=0, out equals the multiplier result.
    check_select0_path: assert property (
        @(posedge CLK) disable iff (1'b0) (select == 1'b0) |-> (out == (a * b))
    );

    // When select=1 and parity is 1, out equals the multiplier result.
    check_select1_parity1_path: assert property (
        @(posedge CLK) disable iff (1'b0) (select && (^in == 1'b1)) |-> (out == (a * b))
    );

    // When select=1 and parity is 0, out equals multiplier result plus {8'b0,1'b1}.
    check_select1_parity0_path: assert property (
        @(posedge CLK) disable iff (1'b0) (select && (^in == 1'b0)) |-> (out == ((a * b) + {8'b0, 1'b1}))
    );

    // For select=1, out - product equals 0 if parity=1 else 1 if parity=0.
    check_select1_diff_matches_parity: assert property (
        @(posedge CLK) disable iff (1'b0) select |-> ((out - (a * b)) == ( (^in) ? 16'd0 : 16'd1 ))
    );

    // If all inputs are stable, output must be stable (purely combinational behavior).
    check_stability_when_inputs_stable: assert property (
        @(posedge CLK) disable iff (1'b0) $stable(a) && $stable(b) && $stable(in) && $stable(select) |-> $stable(out)
    );

    // With select=0 and any zero multiplicand, out is zero.
    check_zero_mult_select0: assert property (
        @(posedge CLK) disable iff (1'b0) (select == 1'b0) && ((a == 8'd0) || (b == 8'd0)) |-> (out == 16'd0)
    );

    // With select=1, parity=1, and any zero multiplicand, out is zero.
    check_zero_mult_select1_parity1: assert property (
        @(posedge CLK) disable iff (1'b0) (select && (^in == 1'b1) && ((a == 8'd0) || (b == 8'd0))) |-> (out == 16'd0)
    );

    // With select=1, parity=0, and any zero multiplicand, out is {8'b0,1'b1}.
    check_zero_mult_select1_parity0: assert property (
        @(posedge CLK) disable iff (1'b0) (select && (^in == 1'b0) && ((a == 8'd0) || (b == 8'd0))) |-> (out == {7'd0, 9'h001}[15:0])
    );

    // With select=1 and parity=0, LSB toggles relative to product.
    check_lsb_toggle_parity0: assert property (
        @(posedge CLK) disable iff (1'b0) (select && (^in == 1'b0)) |-> (out[0] == ~((a * b)[0]))
    );

    // With select=1 and parity=1, LSB matches product LSB.
    check_lsb_equal_parity1: assert property (
        @(posedge CLK) disable iff (1'b0) (select && (^in == 1'b1)) |-> (out[0] == ((a * b)[0]))
    );
endmodule