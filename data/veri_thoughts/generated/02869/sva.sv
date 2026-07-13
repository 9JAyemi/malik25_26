module and_8bit_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic clk,
    input logic [7:0] Y
);
    ///// Functional behavior /////
    // Next-cycle Y equals bitwise AND of current A and B.
    check_y_next_is_and_of_inputs: assert property (
        @(posedge clk) 1'b1 |=> (Y == $past(A & B))
    );

    // If B is all ones, next-cycle Y equals previous A.
    check_y_next_eq_prevA_when_B_all1: assert property (
        @(posedge clk) (B == 8'hFF) |=> (Y == $past(A))
    );

    // If A is all ones, next-cycle Y equals previous B.
    check_y_next_eq_prevB_when_A_all1: assert property (
        @(posedge clk) (A == 8'hFF) |=> (Y == $past(B))
    );

    // If A is all zeros, next-cycle Y is zero.
    check_y_next_zero_when_A_zero: assert property (
        @(posedge clk) (A == 8'h00) |=> (Y == 8'h00)
    );

    // If B is all zeros, next-cycle Y is zero.
    check_y_next_zero_when_B_zero: assert property (
        @(posedge clk) (B == 8'h00) |=> (Y == 8'h00)
    );

    // If A and B are stable over the last cycle, Y is stable over the next cycle.
    check_y_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(A) && $stable(B)) |=> $stable(Y)
    );
endmodule