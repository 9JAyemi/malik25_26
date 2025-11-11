
module shift_register (
    input clk,
    input reset,
    input data_in,
    output reg [2:0] q
);

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            q <= 3'b0;
        end else begin
            q <= {q[1:0], data_in};
        end
    end

endmodule
module d_flip_flop (
    input clk,
    input reset,
    input d,
    output reg q
);

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            q <= 1'b0;
        end else begin
            q <= d;
        end
    end

endmodule
module functional_module (
    input [2:0] shift_register_out,
    input d_flip_flop_out,
    output reg [2:0] or_out
);

    always @(*) begin
        or_out = shift_register_out | d_flip_flop_out;
    end

endmodule
module control_logic (
    input select,
    input [2:0] shift_register_out,
    input d_flip_flop_out,
    input [2:0] functional_out,
    output reg [2:0] q
);

    always @(*) begin
        if (select) begin
            q = functional_out;
        end else begin
            q = shift_register_out;
        end
    end

endmodule
module top_module (
    input clk,
    input reset,
    input d,
    input select,
    output q
);

    wire [2:0] shift_register_out;
    wire d_flip_flop_out;
    wire [2:0] functional_out;
    wire [2:0] ctrl_logic_out;

    shift_register shift_reg(clk, reset, d, shift_register_out);
    d_flip_flop d_ff(clk, reset, d, d_flip_flop_out);
    functional_module func_mod(shift_register_out, d_flip_flop_out, functional_out);
    control_logic ctrl_logic(select, shift_register_out, d_flip_flop_out, functional_out, ctrl_logic_out);
    assign q = ctrl_logic_out[2];

endmodule