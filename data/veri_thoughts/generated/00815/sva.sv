module mux_2to1_sva (
    input logic [15:0] A,
    input logic [15:0] B,
    input logic S,
    input logic [15:0] MO
);
    // No clock or reset in RTL; purely combinational 2:1 mux.

    // On S rising edge, MO must equal B (select=1).
    check_select_B_on_S_rise: assert property (
        @(posedge S) MO == B
    );

    // On S falling edge, MO must equal A (select=0).
    check_select_A_on_S_fall: assert property (
        @(negedge S) MO == A
    );

    // MO must equal either A or B at sample points.
    check_mo_is_one_of_inputs: assert property (
        @(posedge S or negedge S or posedge A[0] or posedge B[0] or posedge MO[0]) (MO == A) || (MO == B)
    );

    genvar i;
    generate
        for (i = 0; i < 16; i++) begin : g_bit
            // If S=0 and A[i] rises, MO[i] must be 1.
            check_mo_tracks_A_rise_when_S0: assert property (
                @(posedge A[i]) (!S) |-> (MO[i] == 1'b1)
            );
            // If S=0 and A[i] falls, MO[i] must be 0.
            check_mo_tracks_A_fall_when_S0: assert property (
                @(negedge A[i]) (!S) |-> (MO[i] == 1'b0)
            );
            // If S=1 and B[i] rises, MO[i] must be 1.
            check_mo_tracks_B_rise_when_S1: assert property (
                @(posedge B[i]) (S) |-> (MO[i] == 1'b1)
            );
            // If S=1 and B[i] falls, MO[i] must be 0.
            check_mo_tracks_B_fall_when_S1: assert property (
                @(negedge B[i]) (S) |-> (MO[i] == 1'b0)
            );
        end
    endgenerate

    // If A and B are equal, MO must equal that value at sample points.
    check_equal_inputs_passthrough: assert property (
        @(posedge S or negedge S or posedge A[0] or posedge B[0]) (A == B) |-> (MO == A)
    );

    // If MO equals A, then S==0 or A==B at sample points.
    check_mo_equals_A_implies_S0_or_equal: assert property (
        @(posedge S or negedge S or posedge A[0] or posedge B[0] or posedge MO[0]) (MO == A) |-> ((!S) || (A == B))
    );

    // If MO equals B, then S==1 or A==B at sample points.
    check_mo_equals_B_implies_S1_or_equal: assert property (
        @(posedge S or negedge S or posedge A[0] or posedge B[0] or posedge MO[0]) (MO == B) |-> ((S) || (A == B))
    );
endmodule