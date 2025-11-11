
module center_pos(
    input [15:0] x_row,
    input [15:0] y_col,
    input reset,
    input clk,
    input [15:0] valid,
    output reg [15:0] center_x,
    output reg [15:0] center_y
);

reg [31:0] center_x_temp;
reg [31:0] center_y_temp;
reg [31:0] pixel_counter;
reg [31:0] dirty;

wire [31:0] result_x;
wire [31:0] result_y;

// Replace the alt_div modules with generic division operators

// Calculate the center x position
assign result_x = (center_x_temp / pixel_counter);

// Calculate the center y position
assign result_y = (center_y_temp / pixel_counter);

always @(posedge clk) begin
    if (reset) begin
        center_x <= 16'h0;
        center_y <= 16'h0;
        center_x_temp <= 32'h0;
        center_y_temp <= 32'h0;
        pixel_counter <= 32'h0;
        dirty <= 32'h0;
    end else begin
        if (dirty >= 32'h00075300) begin
            center_x <= result_x[15:0];
            center_y <= result_y[15:0];
            center_x_temp <= 32'h0;
            center_y_temp <= 32'h0;
            pixel_counter <= 32'h0;
            dirty <= 32'h0;
        end else if (valid[dirty[31:16]]) begin
            center_x_temp <= center_x_temp + x_row;
            center_y_temp <= center_y_temp + y_col;
            pixel_counter <= pixel_counter + 1;
            dirty <= dirty + 1;
        end else begin
            dirty <= dirty + 1;
        end
    end
end

endmodule
