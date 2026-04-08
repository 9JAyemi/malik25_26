module adder16_assertions (
    input logic        clk,
    input logic        rst,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic [15:0] Z
);

    // Z matches the value selected at the previous clock edge.
    check_registered_behavior: assert property (
        @(posedge clk) disable iff ($initstate)
        Z == ($past(rst) ? 16'h0000 : ($past(A) + $past(B)))
    );

    // A reset clock edge clears Z on the following sampled cycle.
    check_reset_clears_z: assert property (
        @(posedge clk) disable iff ($initstate)
        $past(rst) |-> (Z == 16'h0000)
    );

    // A non-reset clock edge makes Z capture the previous A+B value.
    check_sum_update: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        !$past(rst) |-> (Z == ($past(A) + $past(B)))
    );

    // If reset stays asserted across clocks, Z remains zero.
    check_reset_hold_zero: assert property (
        @(posedge clk) disable iff ($initstate)
        (rst && $past(rst)) |-> (Z == 16'h0000)
    );

endmodule