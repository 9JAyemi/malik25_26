module delay3stage_sva (
    input logic Y,
    input logic A,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // Y must be the bitwise complement of A when sampled on A rising edge.
    check_complement_on_A_posedge: assert property (
        @(posedge A) (Y == ~A)
    );

    // Y must be the bitwise complement of A when sampled on Y rising edge.
    check_complement_on_Y_posedge: assert property (
        @(posedge Y) (Y == ~A)
    );

    // When A rises, Y must fall (opposite toggle).
    check_y_falls_on_a_rise: assert property (
        @(posedge A) $fell(Y)
    );

    // When Y rises, A must fall (opposite toggle).
    check_a_falls_on_y_rise: assert property (
        @(posedge Y) $fell(A)
    );

    // A and Y are never equal when sampled on A rising edge.
    check_inequality_on_A_posedge: assert property (
        @(posedge A) (Y != A)
    );

    // Exactly one of A or Y is 1 when sampled on A rising edge.
    check_one_hot_on_A_posedge: assert property (
        @(posedge A) (A ^ Y) == 1'b1
    );

    // Complement relation holds regardless of VPWR events.
    check_complement_on_VPWR_posedge: assert property (
        @(posedge VPWR) (Y == ~A)
    );

    // Complement relation holds regardless of VGND events.
    check_complement_on_VGND_posedge: assert property (
        @(posedge VGND) (Y == ~A)
    );

    // Complement relation holds regardless of VPB events.
    check_complement_on_VPB_posedge: assert property (
        @(posedge VPB) (Y == ~A)
    );

    // Complement relation holds regardless of VNB events.
    check_complement_on_VNB_posedge: assert property (
        @(posedge VNB) (Y == ~A)
    );
endmodule