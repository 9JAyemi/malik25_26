module led_sreg_driver #(
    // number of LEDs
    parameter COUNT = 8,
    // invert output
    parameter INVERT = 0,
    // clock prescale
    parameter PRESCALE = 31
)
(
    input  wire             clk,
    input  wire             rst,

    input  wire [COUNT-1:0] led,

    output wire             sreg_d,
    output wire             sreg_ld,
    output wire             sreg_clk
);

localparam CL_COUNT = $clog2(COUNT+1);
localparam CL_PRESCALE = $clog2(PRESCALE+1);

reg [CL_COUNT-1:0] count_reg = 0;
reg [CL_PRESCALE-1:0] prescale_count_reg = 0;
reg enable_reg = 1'b0;
reg update_reg = 1'b1;
reg cycle_reg = 1'b0;

reg [COUNT-1:0] led_sync_reg_1 = 0;
reg [COUNT-1:0] led_sync_reg_2 = 0;
reg [COUNT-1:0] led_reg = 0;

reg sreg_d_reg = 1'b0;
reg sreg_ld_reg = 1'b0;
reg sreg_clk_reg = 1'b0;

assign sreg_d = INVERT ? !sreg_d_reg : sreg_d_reg;
assign sreg_ld = sreg_ld_reg;
assign sreg_clk = sreg_clk_reg;

always @(posedge clk) begin
    led_sync_reg_1 <= led;
    led_sync_reg_2 <= led_sync_reg_1;

    enable_reg <= 1'b0;

    if (prescale_count_reg) begin
        prescale_count_reg <= prescale_count_reg - 1;
    end else begin
        enable_reg <= 1'b1;
        prescale_count_reg <= PRESCALE;
    end

    if (enable_reg) begin
        if (cycle_reg) begin
            cycle_reg <= 1'b0;
            sreg_clk_reg <= 1'b1;
        end else if (count_reg) begin
            sreg_clk_reg <= 1'b0;
            sreg_ld_reg <= 1'b0;

            if (count_reg < COUNT) begin
                count_reg <= count_reg + 1;
                cycle_reg <= 1'b1;
                sreg_d_reg <= led_reg[count_reg];
            end else begin
                count_reg <= 0;
                cycle_reg <= 1'b0;
                sreg_d_reg <= 1'b0;
                sreg_ld_reg <= 1'b1;
            end
        end else begin
            sreg_clk_reg <= 1'b0;
            sreg_ld_reg <= 1'b0;

            if (update_reg) begin
                update_reg <= 1'b0;

                count_reg <= 1;
                cycle_reg <= 1'b1;
                sreg_d_reg <= led_reg[0];
            end
        end
    end

    if (led_sync_reg_2 != led_reg) begin
        led_reg <= led_sync_reg_2;
        update_reg <= 1'b1;
    end

    if (rst) begin
        count_reg <= 0;
        prescale_count_reg <= 0;
        enable_reg <= 1'b0;
        update_reg <= 1'b1;
        cycle_reg <= 1'b0;
        led_reg <= 0;
        sreg_d_reg <= 1'b0;
        sreg_ld_reg <= 1'b0;
        sreg_clk_reg <= 1'b0;
    end
end

endmodule