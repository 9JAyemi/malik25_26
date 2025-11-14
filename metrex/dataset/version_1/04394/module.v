
module top_module (
    input  clk,
    input  reset,
    input  [1:0] in,
    input  sel,
    input  [3:0] data_in,
    input  shift,
    input  load,
    output reg [3:0] out
);

reg [3:0] shift_reg;
wire [3:0] mux_out;

// Instantiate the 2-to-1 multiplexer module
mux_2to1 mux_inst (
    .sel(sel),
    .in0(data_in),
    .in1(shift_reg),
    .out(mux_out)
);

// Instantiate the 4-bit shift register module
shift_reg_4bit shift_reg_inst (
    .clk(clk),
    .reset(reset),
    .load(load),
    .shift(shift),
    .data_in(mux_out),
    .out(shift_reg)
);

// Functional module to calculate the sum of shift register output and selected input of the multiplexer
always @ (posedge clk) begin
    if (reset) begin
        out <= 0;
    end else begin
        out <= shift_reg;
    end
end

endmodule
module mux_2to1 (
    input [3:0] in0,
    input [3:0] in1,
    input sel,
    output reg [3:0] out
);

always @ (sel or in0 or in1) begin
    if (sel == 1'b0) begin
        out <= in0;
    end else begin
        out <= in1;
    end
end

endmodule
module shift_reg_4bit (
    input [3:0] data_in,
    input shift,
    input load,
    input clk,
    input reset,
    output reg [3:0] out
);

always @(posedge clk or posedge reset) begin
    if (reset) begin
        out <= 0;
    end else begin
        if (load) begin
            out <= data_in;
        end else if (shift) begin
            out <= {out[2:0], 1'b0};
        end
    end
end

endmodule