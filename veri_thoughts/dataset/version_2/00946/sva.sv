module sky130_fd_sc_ms__o32ai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2
);
    ///// Combinational function checks (clocked for SVA) /////
    // Y implements ~( (A1|A2|A3) & (B1|B2) ).
    check_functional_nand_or: assert property (
        @(posedge clk) Y === ~((A1 | A2 | A3) & (B1 | B2))
    );

    // If all A inputs are 0 then Y must be 1.
    check_y_high_when_all_a_zero: assert property (
        @(posedge clk) (!A1 && !A2 && !A3) |-> (Y === 1'b1)
    );

    // If all B inputs are 0 then Y must be 1.
    check_y_high_when_all_b_zero: assert property (
        @(posedge clk) (!B1 && !B2) |-> (Y === 1'b1)
    );

    // If any A is 1 and any B is 1 then Y must be 0.
    check_y_low_when_a_or_and_b_or: assert property (
        @(posedge clk) ((A1 || A2 || A3) && (B1 || B2)) |-> (Y === 1'b0)
    );

    // If Y is 0 then (A1|A2|A3) and (B1|B2) are both 1.
    check_y_low_implies_group_ors_high: assert property (
        @(posedge clk) (Y === 1'b0) |-> ((A1 || A2 || A3) && (B1 || B2))
    );

    ///// Pairwise high cross-group forces Y low /////
    // A1=1 and B1=1 implies Y=0.
    check_y_low_when_A1_B1: assert property (
        @(posedge clk) (A1 && B1) |-> (Y === 1'b0)
    );
    // A1=1 and B2=1 implies Y=0.
    check_y_low_when_A1_B2: assert property (
        @(posedge clk) (A1 && B2) |-> (Y === 1'b0)
    );
    // A2=1 and B1=1 implies Y=0.
    check_y_low_when_A2_B1: assert property (
        @(posedge clk) (A2 && B1) |-> (Y === 1'b0)
    );
    // A2=1 and B2=1 implies Y=0.
    check_y_low_when_A2_B2: assert property (
        @(posedge clk) (A2 && B2) |-> (Y === 1'b0)
    );
    // A3=1 and B1=1 implies Y=0.
    check_y_low_when_A3_B1: assert property (
        @(posedge clk) (A3 && B1) |-> (Y === 1'b0)
    );
    // A3=1 and B2=1 implies Y=0.
    check_y_low_when_A3_B2: assert property (
        @(posedge clk) (A3 && B2) |-> (Y === 1'b0)
    );
endmodule