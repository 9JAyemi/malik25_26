module interface_module_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);

    // Y must implement the OR-AND-Invert combinational function.
    check_o22ai_function: assert property (
        @(posedge clk)
        Y == ~((A1 & A2) | (B1 & B2))
    );

    // When the A input pair is asserted, Y must be low.
    check_a_pair_drives_low: assert property (
        @(posedge clk)
        (A1 & A2) |-> (Y == 1'b0)
    );

    // When the B input pair is asserted, Y must be low.
    check_b_pair_drives_low: assert property (
        @(posedge clk)
        (B1 & B2) |-> (Y == 1'b0)
    );

    // When neither input pair is asserted, Y must be high.
    check_no_pair_drives_high: assert property (
        @(posedge clk)
        (!(A1 & A2) && !(B1 & B2)) |-> (Y == 1'b1)
    );

endmodule