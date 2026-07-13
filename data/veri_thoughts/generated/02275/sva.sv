module my_module_sva (
    input logic CLK,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1
);
    // Y equals NOR of B1 and (A1 & A2)
    check_y_equation: assert property (
        @(posedge CLK) Y == ~(B1 | (A1 & A2))
    );

    // B1 high forces Y low
    check_b1_high_forces_y0: assert property (
        @(posedge CLK) (B1 == 1'b1) |-> (Y == 1'b0)
    );

    // A1 and A2 both high force Y low
    check_a1a2_high_forces_y0: assert property (
        @(posedge CLK) ((A1 == 1'b1) && (A2 == 1'b1)) |-> (Y == 1'b0)
    );

    // When B1 is low and not (A1 & A2), Y must be high
    check_b1_low_and_no_and_implies_y1: assert property (
        @(posedge CLK) ((B1 == 1'b0) && !((A1 == 1'b1) && (A2 == 1'b1))) |-> (Y == 1'b1)
    );

    // Y high implies B1 low and not (A1 & A2)
    check_y1_conditions: assert property (
        @(posedge CLK) (Y == 1'b1) |-> ((B1 == 1'b0) && !((A1 == 1'b1) && (A2 == 1'b1)))
    );

    // Y low implies B1 high or (A1 & A2) high
    check_y0_causes: assert property (
        @(posedge CLK) (Y == 1'b0) |-> ((B1 == 1'b1) || ((A1 == 1'b1) && (A2 == 1'b1)))
    );
endmodule