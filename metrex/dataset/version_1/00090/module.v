module FIFO_image_filter_gray_data_stream_0_V_shiftReg #(
    parameter DATA_WIDTH = 8,
    parameter ADDR_WIDTH = 1
)(
    input clk,
    input [DATA_WIDTH-1:0] data,
    input ce,
    input [ADDR_WIDTH-1:0] a,
    output reg [DATA_WIDTH-1:0] q
);


parameter DEPTH = 2;

reg [DATA_WIDTH-1:0] SRL_SIG [0:DEPTH-1];
integer i;

always @ (posedge clk)
begin
    if (ce)
    begin
        for (i=0; i<DEPTH-1; i=i+1)
            SRL_SIG[i+1] <= SRL_SIG[i];
        SRL_SIG[0] <= data;
    end
end

always @*
begin
    q <= SRL_SIG[a];
end

endmodule