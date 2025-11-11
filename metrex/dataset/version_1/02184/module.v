
module shift_register (
    input clk,
    input reset,
    input load,
    input [3:0] load_value,
    output [3:0] shift_out
);

reg [3:0] shift_reg;

always @(posedge clk, negedge reset) begin
    if (!reset) begin
        shift_reg <= 4'b0;
    end else if (load) begin
        shift_reg <= load_value;
    end else begin
        shift_reg <= {shift_reg[2:0], 1'b0};
    end
end

assign shift_out = shift_reg;

endmodule

module d_flip_flop (
    input clk,
    input d,
    input aset,
    input areset,
    output q
);

reg q;

always @(posedge clk, negedge areset) begin
    if (!areset) begin
        q <= 1'b0;
    end else if (aset) begin
        q <= 1'b1;
    end else begin
        q <= d;
    end
end

endmodule

module top_module (
    input clk,
    input reset,
    input load,
    input [3:0] load_value,
    input d,
    input aset,
    input areset,
    output q,
    output [3:0] shift_out
);

shift_register shift_reg (
    .clk(clk),
    .reset(reset),
    .load(load),
    .load_value(load_value),
    .shift_out(shift_out)
);

d_flip_flop d_ff (
    .clk(clk),
    .d(d),
    .aset(aset),
    .areset(areset),
    .q(q)
);

endmodule
