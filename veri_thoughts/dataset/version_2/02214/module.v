`define STATE_IDLE		        2'b00
`define STATE_LEADVERIFY		2'b01
`define STATE_DATARCV			2'b10

module ir_rcv (
    input clk50,
    input reset_n,
    input ir_rx,
	output reg [31:0] ir_code,
	output reg ir_code_ack
);

parameter LEADCODE_LO_THOLD     = 230000;  parameter LEADCODE_HI_THOLD     = 210000;  parameter LEADCODE_HI_RPT_THOLD = 105000;  parameter RPT_RELEASE_THOLD     = 6000000; parameter BIT_ONE_THOLD         = 41500;   parameter BIT_DETECT_THOLD      = 20000;   parameter IDLE_THOLD            = 262143;  reg [1:0] state;        reg [31:0] databuf;     reg [5:0] bits_detected;    reg [17:0] act_cnt;     reg [17:0] leadvrf_cnt; reg [17:0] datarcv_cnt; reg [22:0] rpt_cnt;     always @(posedge clk50 or negedge reset_n)
begin
    if (!reset_n)
        act_cnt <= 0;
	else
    begin
        if ((state == `STATE_IDLE) & (~ir_rx))
            act_cnt <= act_cnt + 1'b1;
        else
            act_cnt <= 0;
    end
end

always @(posedge clk50 or negedge reset_n)
begin
    if (!reset_n)
        leadvrf_cnt <= 0;
	else
    begin
        if ((state == `STATE_LEADVERIFY) & ir_rx)
            leadvrf_cnt <= leadvrf_cnt + 1'b1;
        else
            leadvrf_cnt <= 0;
    end
end


always @(posedge clk50 or negedge reset_n)
begin
    if (!reset_n)
    begin
        datarcv_cnt <= 0;
        bits_detected <= 0;
        databuf <= 0;
    end
	else
    begin
        if (state == `STATE_DATARCV)
        begin
            if (ir_rx)
                datarcv_cnt <= datarcv_cnt + 1'b1;
            else
                datarcv_cnt <= 0;

            if (datarcv_cnt == BIT_DETECT_THOLD)
                bits_detected <= bits_detected + 1'b1;
                
            if (datarcv_cnt == BIT_ONE_THOLD)
                databuf[32-bits_detected] <= 1'b1;
        end
        else
        begin
            datarcv_cnt <= 0;
            bits_detected <= 0;
            databuf <= 0;
        end
    end
end

always @(posedge clk50 or negedge reset_n)
begin
    if (!reset_n)
    begin
        ir_code_ack <= 1'b0;
        ir_code <= 32'h00000000;
    end
	else
    begin
        if ((bits_detected == 32) & (databuf[15:8] == ~databuf[7:0]))
        begin
            ir_code <= databuf;
            ir_code_ack <= 1'b1;
        end
        else if (rpt_cnt >= RPT_RELEASE_THOLD)
        begin
            ir_code <= 32'h00000000;
            ir_code_ack <= 1'b0;
        end
        else
            ir_code_ack <= 1'b0;
    end
end

always @(posedge clk50 or negedge reset_n)
begin
    if (!reset_n)
    begin
        state <= `STATE_IDLE;
        rpt_cnt <= 0;
    end
    else
    begin
        rpt_cnt <= rpt_cnt + 1'b1;
    
        case (state)
            `STATE_IDLE:
                if (act_cnt >= LEADCODE_LO_THOLD)
                    state <= `STATE_LEADVERIFY;
            `STATE_LEADVERIFY:
            begin
                if (leadvrf_cnt == LEADCODE_HI_RPT_THOLD)
                    rpt_cnt <= 0;
                if (leadvrf_cnt >= LEADCODE_HI_THOLD)
                    state <= `STATE_DATARCV;
            end    
            `STATE_DATARCV:
                if ((datarcv_cnt >= IDLE_THOLD) | (bits_detected >= 33))
                    state <= `STATE_IDLE;
            default:
                state <= `STATE_IDLE;
        endcase
    end
end

endmodule
