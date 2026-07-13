module decoder_2to4_with_enable_sva (
    input logic A,
    input logic B,
    input logic EN,
    output logic [3:0] Y
);
    // Combinational logic, so use @(posedge clk)
    // EN must be HIGH for Y to be driven by the decoder
    decoder_enable: assert property (
        @(posedge clk) disable iff (!EN) Y == 4'b0000
    );
    // When EN is HIGH, Y should be driven based on the values of A and B
    decoder_output: assert property (
        @(posedge clk) disable iff (!EN) (Y == (A ? (B ? 4'b1000 : 4'b0100) : (B ? 4'b0010 : 4'b0001)))
    );
endmodule