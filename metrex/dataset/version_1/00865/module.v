module top_module(
    input clk,
    input reset,
    input [3:0] in,
    input [7:0] sel,
    input [1:0] ena,
    input load,
    input select,
    output [3:0] q);

    wire [3:0] barrel_shift_out;
    wire [3:0] mux_out;
    wire [3:0] or_out;

    barrel_shifter barrel_shift(
        .clk(clk),
        .reset(reset),
        .in(in),
        .shift_sel(sel),
        .out(barrel_shift_out)
    );

    mux_256to1 mux(
        .sel(select ? sel : 8'hFF),
        .in_0(barrel_shift_out),
        .in_1(mux_out),
        .out(mux_out)
    );

    or_gate or_op(
        .in_0(barrel_shift_out),
        .in_1(mux_out),
        .out(or_out)
    );

    reg [3:0] q_reg;

    always @(posedge clk) begin
        if (reset) begin
            q_reg <= 4'b0000;
        end else if (load) begin
            q_reg <= in;
        end else if (ena) begin
            q_reg <= or_out;
        end
    end

    assign q = q_reg;

endmodule

module barrel_shifter(
    input clk,
    input reset,
    input [3:0] in,
    input [7:0] shift_sel,
    output [3:0] out
);

    reg [3:0] out_reg;

    always @(posedge clk) begin
        if (reset) begin
            out_reg <= 4'b0000;
        end else begin
            out_reg <= in << shift_sel[3:0];
        end
    end

    assign out = out_reg;

endmodule

module mux_256to1(
    input [7:0] sel,
    input [3:0] in_0,
    input [3:0] in_1,
    output [3:0] out
);

    reg [3:0] out_reg;

    always @(*) begin
        case (sel)
            8'h00: out_reg = in_0;
            8'h01: out_reg = in_1;
            // Add remaining cases for 254 inputs
            8'hFE: out_reg = in_1;
            8'hFF: out_reg = in_0;
        endcase
    end

    assign out = out_reg;

endmodule

module or_gate(
    input [3:0] in_0,
    input [3:0] in_1,
    output [3:0] out
);

    assign out = in_0 | in_1;

endmodule