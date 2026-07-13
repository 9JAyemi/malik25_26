module my_module_sva (
    input logic clk,
    input logic [1:0] A1,
    input logic [1:0] A2,
    input logic [1:0] B1,
    input logic [1:0] B2,
    input logic [1:0] C1,
    input logic [1:0] VPWR,
    input logic [1:0] VGND,
    input logic [1:0] VPB,
    input logic [1:0] VNB,
    input logic X
);

// X equals (A1==B1 && A2==B2) ? 1 : 0.
    check_x_matches_equal_inputs: assert property (
        @(posedge clk) X == ((A1 == B1) && (A2 == B2))
    );

// When A1==B1 and A2==B2, X must be 1.
    check_x_high_when_inputs_equal: assert property (
        @(posedge clk) (A1 == B1) && (A2 == B2) |-> (X == 1'b1)
    );

// When A1!=B1 or A2!=B2, X must be 0.
    check_x_low_when_inputs_unequal: assert property (
        @(posedge clk) (A1 != B1) || (A2 != B2) |-> (X == 1'b0)
    );

// If C1==VPWR and VPB==VGND, X is inverted.
    check_x_inverted_when_c1_vpwr_and_vpb_vgnd: assert property (
        @(posedge clk) (C1 == VPWR) && (VPB == VGND) |-> (X == ~((A1 == B1) && (A2 == B2)))
    );

// If C1!=VPWR or VPB!=VGND, X is not inverted.
    check_x_not_inverted_when_c1_not_vpwr_or_vpb_not_vgnd: assert property (
        @(posedge clk) (C1 != VPWR) || (VPB != VGND) |-> (X == ((A1 == B1) && (A2 == B2)))
    );

// With C1==VPWR and VPB==VGND, X equals (A1==B1 && A2==B2) ? 0 : 1.
    check_x_inverted_when_c1_vpwr_and_vpb_vgnd_then_not_equal: assert property (
        @(posedge clk) (C1 == VPWR) && (VPB == VGND) |-> (X == ~((A1 == B1) && (A2 == B2)))
    );

// With C1==VPWR and VPB==VGND, X equals (A1==B1 && A2==B2) ? 0 : 1.
    check_x_inverted_when_c1_vpwr_and_vpb_vgnd_then_not_equal: assert property (
        @(posedge clk) (C1 == VPWR) && (VPB == VGND) |-> (X == ~((A1 == B1) && (A2 == B2)))
    );

// With C1!=VPWR or VPB!=VGND, X equals (A1==B1 && A2==B2) ? 1 : 0.
    check_x_not_inverted_when_c1_not_vpwr_or_vpb_not_vgnd_then_equal: assert property (
        @(posedge clk) (C1 != VPWR) || (VPB != VGND) |-> (X == ((A1 == B1) && (A2 == B2)))
    );

// With C1!=VPWR or VPB!=VGND, X equals (A1==B1 && A2==B2) ? 1 : 0.
    check_x_not_inverted_when_c1_not_vpwr_or_vpb_not_vgnd_then_equal: assert property (
        @(posedge clk) (C1 != VPWR) || (VPB != VGND) |-> (X == ((A1 == B1) && (A2 == B2)))
    );

endmodule
