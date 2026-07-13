module adder_sva (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    output logic [8:0] sum
);
    // Combinational logic: sum is calculated at every clock edge
    // Ensure sum is correct for given A and B
    comb_sum_correct: assert property (
        @(posedge clk) $stable(A) && $stable(B) |-> sum == {1'b0, A} + {1'b0, B}
    );
endmodule