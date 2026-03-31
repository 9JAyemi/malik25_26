module nor_and_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

// Y equals ~(A|B) & ~(C|D) when sampled on clk.
    check_function_equivalence: assert property (
        @(posedge clk) Y == ((~(A | B)) & ~(C | D))
    );

// Y high implies both A|B and C|D are low.
    check_y_high_implies_inputs_low: assert property (
        @(posedge clk) Y |-> ((~(A | B)) && (~(C | D)))
    );

// Both A|B and C|D low implies Y high.
    check_inputs_low_implies_y_high: assert property (
        @(posedge clk) ((~(A | B)) && (~(C | D))) |-> Y
    );

// A high forces Y low.
    check_a_high_forces_y_low: assert property (
        @(posedge clk) A |-> !Y
    );

// B high forces Y low.
    check_b_high_forces_y_low: assert property (
        @(posedge clk) B |-> !Y
    );

// C high forces Y low.
    check_c_high_forces_y_low: assert property (
        @(posedge clk) C |-> !Y
    );

// D high forces Y low.
    check_d_high_forces_y_low: assert property (
        @(posedge clk) D |-> !Y
    );

endmodule
