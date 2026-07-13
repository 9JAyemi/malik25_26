
module mux_4to1 (
    input [3:0] in,
    input [1:0] sel,
    output reg out
);
    always @ (sel, in) begin
        case (sel)
            2'b00: out <= in[0];
            2'b01: out <= in[1];
            2'b10: out <= in[2];
            2'b11: out <= in[3];
        endcase
    end
endmodule
module dff_8 (
    input clk,
    input reset,
    output reg [7:0] q
);
    always @(posedge clk) begin
        if (reset) begin
            q <= 8'b0;
        end else begin
            q <= 8'b0;
        end
    end
endmodule
module functional_module (
    input [7:0] dff_out,
    input [0:0] mux_out,
    output reg [7:0] q
);
    always @* begin
        q = mux_out + dff_out;
    end
endmodule
module top_module (
    input clk,
    input reset,
    input [3:0] in,
    input [1:0] sel,
    output [7:0] q
);
    wire [0:0] mux_out;

    mux_4to1 mux_inst (
        .in(in),
        .sel(sel),
        .out(mux_out)
    );

    wire [7:0] dff_out;

    dff_8 dff_inst (
        .clk(clk),
        .reset(reset),
        .q(dff_out)
    );

    functional_module func_inst (
        .mux_out(mux_out),
        .dff_out(dff_out),
        .q(q)
    );
endmodule