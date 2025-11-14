
module my_fpga_count_dn_1k(
    input clk,
    input n_rst,
    input dn,
    output cnt,
    output cnt_1k
);

reg [31:0] cnt_reg;
reg [3:0] cnt_1k_reg;
reg [31:0] cnt_1k_period;
reg [31:0] cnt_1k_period_reg;
reg [31:0] cnt_1k_period_max = 50000; // 50ms
reg [31:0] cnt_1k_period_min = 9500; // 9.5ms
reg [31:0] cnt_1k_period_diff = 500; // 0.5ms
reg [31:0] cnt_1k_period_inc = 500; // 0.5ms
reg [31:0] cnt_1k_period_dec = 100; // 0.1ms
reg [2:0] cnt_1k_divider = 0;
reg [31:0] cnt_1k_divider_max = 50; // 50 cycles of 1KHz
reg [31:0] cnt_1k_divider_min = 1; // 1 cycle of 1KHz
reg [31:0] cnt_1k_divider_diff = 1; // 1 cycle of 1KHz
reg [31:0] cnt_1k_divider_inc = 1; // 1 cycle of 1KHz
reg [31:0] cnt_1k_divider_dec = 1; // 1 cycle of 1KHz

always @(posedge clk) begin
    if (n_rst) begin
        cnt_reg <= 0;
        cnt_1k_reg <= 0;
        cnt_1k_period <= 0;
        cnt_1k_period_reg <= 0;
        cnt_1k_divider <= 0;
    end else begin
        cnt_reg <= cnt_reg + dn;
        cnt_1k_period <= cnt_1k_period + 1;
        if (cnt_1k_period >= cnt_1k_period_max) begin
            cnt_1k_period_reg <= cnt_1k_period;
            cnt_1k_period <= 0;
            if (cnt_1k_divider < cnt_1k_divider_max) begin
                cnt_1k_divider <= cnt_1k_divider + cnt_1k_divider_inc;
            end
        end
        if (cnt_1k_divider > 0) begin
            cnt_1k_divider <= cnt_1k_divider - 1;
            if (cnt_1k_divider == 0) begin
                cnt_1k_divider <= cnt_1k_divider_min;
                cnt_1k_reg <= cnt_reg - cnt_1k_period_reg;
                cnt_1k_period_reg <= 0;
                if (cnt_1k_reg > cnt_1k_period_max) begin
                    cnt_1k_period_max <= cnt_1k_period_max + cnt_1k_period_diff;
                    cnt_1k_period_min <= cnt_1k_period_min + cnt_1k_period_diff;
                end else if (cnt_1k_reg < cnt_1k_period_min) begin
                    cnt_1k_period_max <= cnt_1k_period_max - cnt_1k_period_diff;
                    cnt_1k_period_min <= cnt_1k_period_min - cnt_1k_period_diff;
                end
            end
        end
    end
end

assign cnt = cnt_reg;
assign cnt_1k = cnt_1k_reg;

endmodule
