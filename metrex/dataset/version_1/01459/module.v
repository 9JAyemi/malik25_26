
module div_top(
    clk,
    reset,
    ce,
    din0,
    din1,
    dout);

parameter ID = 32'd1;
parameter NUM_STAGE = 32'd1;
parameter din0_WIDTH = 32'd1;
parameter din1_WIDTH = 32'd1;
parameter dout_WIDTH = 32'd1;

input clk;
input reset;
input ce;
input[din0_WIDTH - 1:0] din0;
input[din1_WIDTH - 1:0] din1;
output[dout_WIDTH - 1:0] dout;

wire[dout_WIDTH - 1:0] sig_remd;

div #(
.in0_WIDTH( din0_WIDTH ),
.in1_WIDTH( din1_WIDTH ),
.out_WIDTH( dout_WIDTH ))
div_U(
    .dividend( din0 ),
    .divisor( din1 ),
    .quot( dout ),
    .remd( sig_remd ),
    .clk( clk ),
    .ce( ce ),
    .reset( reset ));

endmodule
module div #(
parameter in0_WIDTH = 32,
parameter in1_WIDTH = 32,
parameter out_WIDTH = 32)
(
    input [in0_WIDTH - 1:0] dividend,
    input [in1_WIDTH - 1:0] divisor,
    output reg [out_WIDTH - 1:0] quot,
    output reg [out_WIDTH - 1:0] remd,
    input clk,
    input ce,
    input reset);

    reg [in0_WIDTH - 1:0] temp_dividend;
    reg [in1_WIDTH - 1:0] temp_divisor;
    reg [out_WIDTH - 1:0] temp_quot;
    reg [out_WIDTH - 1:0] temp_remd;

    always @(posedge clk) begin
        if (reset) begin
            temp_dividend <= 0;
            temp_divisor <= 0;
            temp_quot <= 0;
            temp_remd <= 0;
        end else if (ce) begin
            temp_dividend <= dividend;
            temp_divisor <= divisor;
            temp_quot <= quot;
            temp_remd <= remd;

            if (temp_divisor == 0) begin
                temp_quot <= 0;
                temp_remd <= temp_dividend;
            end else begin
                temp_quot <= temp_dividend / temp_divisor;
                temp_remd <= temp_dividend % temp_divisor;
            end
        end
    end

    always @(*) begin
        quot <= temp_quot;
        remd <= temp_remd;
    end

endmodule