module half_adder_sva (
    input logic A,
    input logic B,
    input logic sum,
    input logic carry_out
);
    // Combinational logic: sum should be the XOR of A and B
    comb_sum: assert property (
        @(posedge clk) disable iff (!resetn) sum == (A ^ B)
    );
    // Combinational logic: carry_out should be the AND of A and B
    comb_carry_out: assert property (
        @(posedge clk) disable iff (!resetn) carry_out == (A & B)
    );
endmodule