module uart_rx(
    input clk,
    input rst,
    input rxd,
    output [7:0] data_rx,
    output busy
);

reg [8:0] rxdata;
assign data_rx[7:0] = rxdata[8:1];

reg busy_reg;
assign busy = busy_reg;

reg [9:0] bitTmr;
reg [3:0] bitIndex;
reg rxState;

reg [9:0] bitCnt_0;
reg [9:0] bitCnt_1;

always@(posedge clk) begin
    if(rst)
        begin
            rxState  <= 1'b0;
            busy_reg <= 1'b0;
        end
    else
        begin
            case(rxState)
                1'b0 :
                    begin
                        bitIndex <= 4'd0;
                        bitTmr   <= 10'd0;
                        bitCnt_0 <= 10'd0;
                        bitCnt_1 <= 10'd0;
                        if( rxd == 1'b0 )
                            begin
                                rxState <= 1'b1;
                            end
                        else
                            rxState <= 1'b0;
                    end

                1'b1 :
                    begin
                        if (bitTmr == 10'd7)
                            begin
                                bitTmr   <= 10'd0;
                                bitCnt_0 <= 10'd0;
                                bitCnt_1 <= 10'd0;
                                rxdata[bitIndex] <= rxd;
                                if (bitIndex == 4'd7)
                                    begin
                                        // done!
                                        busy_reg <= 1'b0;
                                        rxState <= 1'b0;
                                    end
                                else
                                    begin
                                        busy_reg <= 1'b1;
                                        bitIndex <= bitIndex + 1'b1;
                                        rxState <= 1'b1;
                                    end
                            end
                        else
                            begin
                                bitTmr <= bitTmr + 1'b1;
                                if(rxd == 1'b0)
                                    bitCnt_0 <= bitCnt_0 + 1'b1;
                                else
                                    bitCnt_1 <= bitCnt_1 + 1'b1;
                                if( bitCnt_0 > bitCnt_1 )
                                    rxdata[bitIndex] <= 1'b0;
                                else
                                    rxdata[bitIndex] <= 1'b1;
                                rxState <= 1'b1;
                            end
                    end
                default :
                    begin
                        rxState  <= 1'b0;
                        busy_reg <= 1'b0;
                    end
            endcase
        end
end

endmodule