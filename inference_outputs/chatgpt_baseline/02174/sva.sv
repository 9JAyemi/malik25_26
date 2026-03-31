module zet_bitlog_sva (
    input  logic        clk,
    input  logic [15:0] x,
    input  logic [15:0] o,
    input  logic        cfo,
    input  logic        ofo
);
    // o is the bitwise inversion of x.
    check_o_is_not_x: assert property (
        @(posedge clk) o == ~x
    );

    // cfo is permanently 0.
    check_cfo_const_zero: assert property (
        @(posedge clk) cfo == 1'b0
    );

    // ofo is permanently 0.
    check_ofo_const_zero: assert property (
        @(posedge clk) ofo == 1'b0
    );

    // If x is stable across a cycle, o is also stable.
    check_stable_x_implies_stable_o: assert property (
        @(posedge clk) $stable(x) |-> $stable(o)
    );

    // If any bit of x changes, o must change in the same cycle.
    check_x_change_implies_o_change: assert property (
        @(posedge clk) (x != $past(x)) |-> (o != $past(o))
    );

    // When x is all zeros, o is all ones.
    check_zero_x_allones_o: assert property (
        @(posedge clk) (x == 16'h0000) |-> (o == 16'hFFFF)
    );

    // When x is all ones, o is all zeros.
    check_allones_x_zero_o: assert property (
        @(posedge clk) (x == 16'hFFFF) |-> (o == 16'h0000)
    );
endmodule