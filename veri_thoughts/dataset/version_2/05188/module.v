
module shift_register (
    input clk,
    input reset,
    input d,
    output reg [2:0] q
);

    always @(posedge clk) begin
        if (reset) begin
            q <= 3'b000;
        end else begin
            q <= {q[1:0], d};
        end
    end

endmodule
module xor_gate (
    input a,
    input b,
    output wire y
);

    assign y = a ^ b;

endmodule
module functional_module (
    input [2:0] shift_reg_out,
    input a,
    input b,
    output wire y
);

    wire xor_out;

    xor_gate xor_gate_inst (
        .a(a),
        .b(b),
        .y(xor_out)
    );

    assign y = shift_reg_out[2] & xor_out;

endmodule
module top_module (
    input clk,
    input reset,
    input d,
    input a,
    input b,
    output reg out_always_ff,
    output [2:0] shift_reg_out,
    output wire functional_module_out
);

    shift_register shift_register_inst (
        .clk(clk),
        .reset(reset),
        .d(d),
        .q(shift_reg_out)
    );

    functional_module functional_module_inst (
        .shift_reg_out(shift_reg_out),
        .a(a),
        .b(b),
        .y(functional_module_out)
    );

    always @(posedge clk) begin
        if(reset) begin
            out_always_ff <= 1'b0;
        end else begin
            out_always_ff <= out_always_ff ? 1'b0 : functional_module_out;
        end
    end

endmodule