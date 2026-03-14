module my_circuit_sva (
    input logic clk,   // Checker sampling clock (DUT has no clock/reset)
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);
    // Y equals the DUT's combinational function.
    check_y_definition: assert property (
        @(posedge clk) Y == ((A1 & A2) & (B1 | C1))
    );

    // A1 LOW forces Y LOW.
    check_y_low_when_a1_low: assert property (
        @(posedge clk) (A1 == 1'b0) |-> (Y == 1'b0)
    );

    // A2 LOW forces Y LOW.
    check_y_low_when_a2_low: assert property (
        @(posedge clk) (A2 == 1'b0) |-> (Y == 1'b0)
    );

    // B1 and C1 both LOW force Y LOW.
    check_y_low_when_b1c1_low: assert property (
        @(posedge clk) ((B1 == 1'b0) && (C1 == 1'b0)) |-> (Y == 1'b0)
    );

    // Y HIGH implies A1 and A2 are HIGH.
    check_y_high_implies_a1a2_high: assert property (
        @(posedge clk) (Y == 1'b1) |-> ((A1 == 1'b1) && (A2 == 1'b1))
    );

    // Y HIGH implies at least one of B1 or C1 is HIGH.
    check_y_high_implies_b1_or_c1_high: assert property (
        @(posedge clk) (Y == 1'b1) |-> ((B1 == 1'b1) || (C1 == 1'b1))
    );

    // When A1 and A2 are HIGH, Y equals (B1 | C1).
    check_a_enable_path: assert property (
        @(posedge clk) ((A1 == 1'b1) && (A2 == 1'b1)) |-> (Y == (B1 | C1))
    );

    // When B1 or C1 is HIGH, Y equals (A1 & A2).
    check_bc_enable_path: assert property (
        @(posedge clk) ((B1 == 1'b1) || (C1 == 1'b1)) |-> (Y == (A1 & A2))
    );

    // If A1 and A2 and B1 are HIGH, Y must be HIGH (independent of C1).
    check_y_high_when_a1a2b1_high: assert property (
        @(posedge clk) ((A1 == 1'b1) && (A2 == 1'b1) && (B1 == 1'b1)) |-> (Y == 1'b1)
    );

    // If A1 and A2 and C1 are HIGH, Y must be HIGH (independent of B1).
    check_y_high_when_a1a2c1_high: assert property (
        @(posedge clk) ((A1 == 1'b1) && (A2 == 1'b1) && (C1 == 1'b1)) |-> (Y == 1'b1)
    );
endmodule