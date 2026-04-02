module four_bit_adder_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic cin,
    output logic [3:0] sum,
    output logic cout
);
    // Combinational logic: sum and cout are determined by a, b, and cin
    // Ensure that sum and cout are correctly calculated based on a, b, and cin
    comb_logic: assert property (
        @(posedge clk) disable iff (!reset_n) (sum == (a + b + cin)[3:0]) && (cout == (a + b + cin > 4'b1111))
    );
endmodule