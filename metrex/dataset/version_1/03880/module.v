
module and_or_gate(
    input a,
    input b,
    output wire out
);

    wire intermediate1;
    wire intermediate2;

    and gate1(intermediate1, a, b);
    and gate2(intermediate2, a, b);
    or gate3(out, intermediate1, intermediate2);

endmodule

module top_module(
    input clk,
    input a,
    input b,
    output reg out_always_ff
);

    wire and_or_out;

    and_or_gate and_or_inst(a, b, and_or_out);

    always @(posedge clk) begin
        out_always_ff <= and_or_out;
    end

endmodule
