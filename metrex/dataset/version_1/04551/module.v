
module hdmi_circle(
    input hdmi_clk,
    input hdmi_de,
    input hdmi_hs,
    input hdmi_vs,
    input [7:0] hdmi_r,
    input [7:0] hdmi_g,
    input [7:0] hdmi_b,
    output hdmi_vs_out,
    output hdmi_de_out,
    output [7:0] hdmi_data_out
);

parameter IMG_W = 64;
parameter IMG_H = 64;

// Calculate circle parameters
localparam RADIUS = IMG_W < IMG_H ? IMG_W / 2 : IMG_H / 2;
localparam CENTER_X = IMG_W / 2;
localparam CENTER_Y = IMG_H / 2;

reg [9:0] x;
reg [9:0] y;
wire inside_circle;

circle circ (
    .clk(hdmi_clk),
    .ce(1'b1),
    .rst(1'b0),
    .de(hdmi_de),
    .hsync(hdmi_hs),
    .vsync(hdmi_vs),
    .mask(1'b1),
    .x(x),
    .y(y),
    .inside_circle(inside_circle),
    .c_h(IMG_H),
    .c_w(IMG_W),
    .CENTER_X(CENTER_X),
    .CENTER_Y(CENTER_Y),
    .RADIUS(RADIUS)
);

reg [7:0] hdmi_r_out;
reg [7:0] hdmi_g_out;
reg [7:0] hdmi_b_out;

always @ (posedge hdmi_clk) begin
    if (inside_circle) begin
        hdmi_r_out <= 8'hFF;
        hdmi_g_out <= 8'h00;
        hdmi_b_out <= 8'h00;
    end else begin
        hdmi_r_out <= hdmi_r;
        hdmi_g_out <= hdmi_g;
        hdmi_b_out <= hdmi_b;
    end
end

assign hdmi_vs_out = hdmi_vs;
assign hdmi_de_out = hdmi_de;
assign hdmi_data_out = {8'b0, hdmi_r_out, hdmi_g_out, hdmi_b_out};

endmodule
module circle(
    input clk,
    input ce,
    input rst,
    input de,
    input hsync,
    input vsync,
    input mask,
    output reg [9:0] x,
    output reg [9:0] y,
    output reg inside_circle,
    input c_h,
    input c_w,
    input [9:0] CENTER_X,
    input [9:0] CENTER_Y,
    input [9:0] RADIUS
);

reg [9:0] x_count;
reg [9:0] y_count;

always @(posedge clk) begin
    if (ce) begin
        x_count <= x_count + 1;
        if (x_count == c_w) begin
            x_count <= 0;
            y_count <= y_count + 1;
        end
    end
end

always @* begin
    // Circle equation: (x - center_x)^2 + (y - center_y)^2 <= r^2
    if (ce) begin
        x = x_count;
        y = y_count;
        if ((x - CENTER_X)*(x - CENTER_X) + (y - CENTER_Y)*(y - CENTER_Y) <= RADIUS*RADIUS)
            inside_circle = 1'b1;
        else
            inside_circle = 1'b0;
    end
end

endmodule