
module top_module(
    input clk,
    input a,
    input b,
    output reg out_always_ff
);
    wire out_xor;

    xor_gate xor_inst (
        .a(a),
        .b(b),
        .out(out_xor)
    );

    always @(posedge clk) begin
        out_always_ff <= out_xor;
    end

endmodule

module xor_gate(
    input a,
    input b,
    output out
);

    assign out = a ^ b;

endmodule
