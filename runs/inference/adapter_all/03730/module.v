module d_to_t_ff (
    input clk,
    input d,
    output reg q );

    reg t;

    always @ (posedge clk) begin
        t <= d ^ q; // XOR operation to convert D to T
        q <= t & q; // Combinational circuit to implement T flip-flop
    end

endmodule