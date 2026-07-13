module EtherCAT_master #(
    parameter n = 8, 
    parameter m = 4  
)(
    input [n-1:0] in_send,
    input [m-1:0] in_receive,
    input clk,
    input rst,
    output reg [n-1:0] out_receive,
    output reg [m-1:0] out_send
);

always @(posedge clk or posedge rst) begin
    if (rst) begin
        out_receive <= 0;
        out_send <= 0;
    end else begin
        out_receive <= in_send;
        out_send <= in_receive;
    end
end

endmodule

