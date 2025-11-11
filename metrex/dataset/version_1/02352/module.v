
module crosshair(
    input wire clk,
    input wire rst,
    input wire [7:0] hdmi_r,
    input wire [7:0] hdmi_g,
    input wire [7:0] hdmi_b,
    input wire hdmi_de,
    input wire hdmi_hs,
    input wire hdmi_vs,
    output reg [7:0] out_r,
    output reg [7:0] out_g,
    output reg [7:0] out_b,
    output reg out_de,
    output reg out_hs,
    output reg out_vs
);

wire [9:0] centr_x;
wire [9:0] centr_y;

assign centr_x = 32;
assign centr_y = 32;

always @ (posedge clk) begin
    if (hdmi_de) begin
        // Add crosshair overlay
        if (centr_x == 32) begin
            out_r <= 8'hFF;
            out_g <= 8'h00;
            out_b <= 8'h00;
        end else if (centr_y == 32) begin
            out_r <= 8'h00;
            out_g <= 8'hFF;
            out_b <= 8'h00;
        end else begin
            out_r <= hdmi_r;
            out_g <= hdmi_g;
            out_b <= hdmi_b;
        end
        out_de <= hdmi_de;
        out_hs <= hdmi_hs;
        out_vs <= hdmi_vs;
    end else begin
        // Blank output when DE is low
        out_r <= 8'h00;
        out_g <= 8'h00;
        out_b <= 8'h00;
        out_de <= 1'b0;
        out_hs <= 1'b0;
        out_vs <= 1'b0;
    end
end

endmodule