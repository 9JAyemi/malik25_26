module mux4_sva (
    input logic clk,              // Sampling clock for assertions (DUT has no clock/reset)
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] C,
    input logic [7:0] D,
    input logic       E,
    input logic [1:0] S,
    input logic [7:0] Y
);

    ///// Mux functionality /////
    // When disabled (E=0), Y must be 0.
    check_disabled_forces_zero: assert property (
        @(posedge clk) (E == 1'b0) |-> (Y == 8'h00)
    );

    // When E=1 and S=00, Y selects A.
    check_select_00_routes_A: assert property (
        @(posedge clk) (E == 1'b1 && S == 2'b00) |-> (Y == A)
    );

    // When E=1 and S=01, Y selects B.
    check_select_01_routes_B: assert property (
        @(posedge clk) (E == 1'b1 && S == 2'b01) |-> (Y == B)
    );

    // When E=1 and S=10, Y selects C.
    check_select_10_routes_C: assert property (
        @(posedge clk) (E == 1'b1 && S == 2'b10) |-> (Y == C)
    );

    // When E=1 and S=11, Y selects D.
    check_select_11_routes_D: assert property (
        @(posedge clk) (E == 1'b1 && S == 2'b11) |-> (Y == D)
    );

    // Y must equal the combinational mux function of E/S/A/B/C/D.
    check_mux_equivalence: assert property (
        @(posedge clk)
            Y == (E ? (S == 2'b00 ? A
                     : S == 2'b01 ? B
                     : S == 2'b10 ? C
                     :               D)
                  : 8'h00)
    );

endmodule