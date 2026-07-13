module zbroji_sva (
    input logic [31:0] a,
    input logic [31:0] b,
    output logic [31:0] sum
);
    // Combinational logic: sum is the result of adding a and b
    comb_logic: assert property (
        @(posedge clk) disable iff (!RESETn) sum == a + b
    );
endmodule