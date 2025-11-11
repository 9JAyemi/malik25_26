
module top_module(
    input [1023:0] in,
    input [7:0] sel,
    input clk,
    input rst_n,
    output reg rise,
    output reg down,
    output reg [15:0] out
);

    reg [3:0] delay_sel;
    wire [3:0] delayed_in;
    reg [3:0] delayed_in_prev;
    reg [3:0] edge_rising;
    reg [3:0] edge_falling;

    // 256-to-1 multiplexer for programmable delay line
    mux256to1 mux(
        .in(in),
        .sel(delay_sel),
        .out(delayed_in)
    );

    // Delay line
    always @(posedge clk or negedge rst_n) begin
        if (~rst_n) begin
            delay_sel <= 0;
        end else begin
            delay_sel <= sel;
        end
    end

    // Edge detection
    always @(posedge clk or negedge rst_n) begin
        if (~rst_n) begin
            delayed_in_prev <= 0;
            rise <= 0;
            down <= 0;
            out <= 0;
        end else begin
            delayed_in_prev <= delayed_in;
            edge_rising <= (delayed_in_prev < delayed_in) ? delayed_in : 0;
            edge_falling <= (delayed_in_prev > delayed_in) ? delayed_in : 0;
            rise <= |edge_rising;
            down <= |edge_falling;
            if (rise && down && (out == 0)) begin
                out <= {{11{edge_rising[3]}}, edge_rising - edge_falling};
            end
        end
    end

endmodule
module mux256to1(
    input [1023:0] in,
    input [3:0] sel,
    output [3:0] out
);

    assign out = in[sel * 4 +: 4];

endmodule