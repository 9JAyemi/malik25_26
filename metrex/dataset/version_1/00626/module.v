module spi_master #(
    parameter CLK_DIVIDE=3 // divide clk by 2^CLK_DIVIDE to get spi_sclk
) (
    input clk, // 50 MHz system clk
    input reset,

    input spi_start,
    input [7:0] spi_data,
    output spi_fin,

    output spi_csn,
    output spi_sdo,
    output spi_sclk // max 10 MHz clk
);

`define SPI_MASTER_SM_W 2

localparam STATE_IDLE = `SPI_MASTER_SM_W'h0;
localparam STATE_SEND = `SPI_MASTER_SM_W'h1;
localparam STATE_HOLD = `SPI_MASTER_SM_W'h2;
localparam STATE_DONE = `SPI_MASTER_SM_W'h3;

reg [`SPI_MASTER_SM_W-1:0] spi_sm_state;
reg [CLK_DIVIDE-1:0] clk_divider;
reg [7:0] spi_data_shift;
reg [2:0] shift_counter;

assign spi_csn = ((spi_sm_state==STATE_IDLE) && (spi_start==1'b0)) ? 1'b1 : 1'b0;
assign spi_sdo = spi_data_shift[7];
assign spi_sclk = ((spi_sm_state==STATE_SEND) && (clk_divider[CLK_DIVIDE-1]==1'b1)) ? 1'b1 : 1'b0;

assign spi_fin = (spi_sm_state==STATE_DONE) ? 1'b1 : 1'b0;

always @(posedge clk or posedge reset) begin
    if (reset) begin
        spi_sm_state <= STATE_IDLE;  
        spi_data_shift <= 'b0;
        clk_divider <= 'b0;
        shift_counter <= 'b0;
    end else begin
        case (spi_sm_state)
            STATE_IDLE: begin
                if (spi_start==1'b1) begin
                    spi_sm_state <= STATE_SEND;
                    spi_data_shift <= spi_data;
                    clk_divider <= 'b0;
                    shift_counter <= 'b0;
                end
            end
            STATE_SEND: begin
                clk_divider <= clk_divider + 1;
                if (clk_divider == {CLK_DIVIDE{1'b1}}) begin
                    shift_counter <= shift_counter + 1;
                    spi_data_shift <= {spi_data_shift[6:0], 1'b0};
                    if (shift_counter==3'b111) begin
                        spi_sm_state <= STATE_HOLD;
                    end
                end
            end
            STATE_HOLD: begin
                clk_divider <= clk_divider + 1;
                if (clk_divider == {CLK_DIVIDE{1'b1}}) begin
                    spi_sm_state <= STATE_DONE;
                end
            end
            STATE_DONE: begin
                if (spi_start==1'b0) begin
                    spi_sm_state <= STATE_IDLE;
                end
            end
            default:
                spi_sm_state <= STATE_IDLE;

        endcase
    end
end

endmodule