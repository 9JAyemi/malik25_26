module shift_register (
    input clk,
    input reset,
    input load,
    input [7:0] data_in,
    output reg [15:0] q
);

always @(posedge clk, posedge reset) begin
    if (reset) begin
        q <= 0;
    end else if (load) begin
        q <= {data_in, q[15:8]};
    end else begin
        q <= {q[14:0], q[15]};
    end
end

endmodule

module d_flip_flop (
    input clk,
    input reset,
    input d,
    output reg q
);

always @(negedge clk, posedge reset) begin
    if (reset) begin
        q <= 0;
    end else begin
        q <= d;
    end
end

endmodule

module functional_module (
    input [15:0] shift_register_out,
    input [0:0] d_flip_flop_out,
    output reg [15:0] q
);

always @(shift_register_out, d_flip_flop_out) begin
    q <= {shift_register_out, d_flip_flop_out};
end

endmodule

module top_module (
    input clk,
    input reset,
    input load,
    input [7:0] data_in,
    input d,
    output [15:0] q
);

wire [15:0] shift_register_out;
wire [0:0] d_flip_flop_out;

shift_register shift_reg(clk, reset, load, data_in, shift_register_out);
d_flip_flop d_ff(clk, reset, d, d_flip_flop_out);
functional_module func_mod(shift_register_out, d_flip_flop_out, q);

endmodule