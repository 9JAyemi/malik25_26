module d_to_t_ff_sva (
    input logic clk,
    input logic d,
    output logic q
);
    // XOR operation to convert D to T
    xor_conversion: assert property (
        @(posedge clk) disable iff (!clk) (q == (d ^ q))
    );

    // Combinational circuit to implement T flip-flop
    t_flip_flop: assert property (
        @(posedge clk) disable iff (!clk) (q == (t & q))
    );
endmodule