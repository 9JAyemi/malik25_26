
module opening_detector(
    input wire rx_pclk,
    input wire rx_de,
    input wire rx_hsync,
    input wire rx_vsync,
    input wire [7:0] rx_red,
    input wire [7:0] rx_green,
    input wire [7:0] rx_blue,
    output wire tx_de,
    output wire tx_hsync,
    output wire tx_vsync,
    output wire [7:0] tx_red,
    output wire [7:0] tx_green,
    output wire [7:0] tx_blue
);

wire opening;
wire opening_de;
wire opening_vsync;
wire opening_hsync;

opening3x3 open3(
    .clk(rx_pclk),
    .ce(1'b1),
    .rst(1'b0),
    .mask((rx_red == 8'hFF) ? 1'b1 : 1'b0),
    .in_de(rx_de),
    .in_vsync(rx_vsync),
    .in_hsync(rx_hsync),
    .opened(opening),
    .out_de(opening_de),
    .out_vsync(opening_vsync),
    .out_hsync(opening_hsync)
);

reg [7:0] opening_r;
reg [7:0] opening_g;
reg [7:0] opening_b;

always @(posedge rx_pclk) begin
    opening_r <= (opening) ? 8'hFF : rx_red;
    opening_g <= (opening) ? 8'hFF : rx_green;
    opening_b <= (opening) ? 8'hFF : rx_blue;
end

assign tx_de        = opening_de;
assign tx_hsync     = opening_hsync;
assign tx_vsync     = opening_vsync;
assign tx_red       = opening_r;
assign tx_green     = opening_g;
assign tx_blue      = opening_b;

endmodule
module opening3x3(
    input wire clk,
    input wire ce,
    input wire rst,
    input wire mask,
    input wire in_de,
    input wire in_vsync,
    input wire in_hsync,
    output reg opened,
    output reg out_de,
    output reg out_vsync,
    output reg out_hsync
);

parameter STATE_IDLE = 0,
          STATE_SEARCH = 1,
          STATE_FOUND = 2;

reg [1:0] state;

always @(posedge clk) begin
    if (rst) begin
        state    <= STATE_IDLE;
        opened   <= 0;
        out_de   <= 0;
        out_vsync<= 0;
        out_hsync<= 0;
    end else if (ce) begin
        case (state)
            STATE_IDLE: begin
                if (mask)
                    state = STATE_SEARCH;
                else
                    state = STATE_IDLE;
            end
            STATE_SEARCH: begin
                if (!mask) begin
                    state = STATE_IDLE;
                    opened = 0;
                end else if (in_de) begin
                    state = STATE_FOUND;
                    opened = 1;
                end
            end
            STATE_FOUND: begin
                if (!in_de) begin
                    state = STATE_IDLE;
                    opened = 0;
                end
            end
        endcase

        out_de = in_de;
        out_vsync = in_vsync;
        out_hsync = in_hsync;
    end
end

endmodule