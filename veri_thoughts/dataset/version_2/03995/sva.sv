module mux_4to1_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] C,
    input logic [3:0] D,
    input logic [1:0] S,
    input logic [3:0] OUT
);

    // When S selects A, OUT must equal A.
    check_select_00_routes_a: assert property (
        @(posedge clk) (S == 2'b00) |-> (OUT == A)
    );

    // When S selects B, OUT must equal B.
    check_select_01_routes_b: assert property (
        @(posedge clk) (S == 2'b01) |-> (OUT == B)
    );

    // When S selects C, OUT must equal C.
    check_select_10_routes_c: assert property (
        @(posedge clk) (S == 2'b10) |-> (OUT == C)
    );

    // When S selects D, OUT must equal D.
    check_select_11_routes_d: assert property (
        @(posedge clk) (S == 2'b11) |-> (OUT == D)
    );

    // If A and S stay on 00, OUT must remain stable.
    check_stable_a_keeps_out_stable: assert property (
        @(posedge clk) (S == 2'b00 && $stable(S) && $stable(A)) |-> $stable(OUT)
    );

    // If B and S stay on 01, OUT must remain stable.
    check_stable_b_keeps_out_stable: assert property (
        @(posedge clk) (S == 2'b01 && $stable(S) && $stable(B)) |-> $stable(OUT)
    );

    // If C and S stay on 10, OUT must remain stable.
    check_stable_c_keeps_out_stable: assert property (
        @(posedge clk) (S == 2'b10 && $stable(S) && $stable(C)) |-> $stable(OUT)
    );

    // If D and S stay on 11, OUT must remain stable.
    check_stable_d_keeps_out_stable: assert property (
        @(posedge clk) (S == 2'b11 && $stable(S) && $stable(D)) |-> $stable(OUT)
    );

endmodule