module EtherCAT_slave #(
    parameter n = 8 
)(
    input [n-1:0] in_receive,
    input clk,
    input rst,
    output reg [n-1:0] out_send
);

// Example data processing in the EtherCAT slave
always @(posedge clk or posedge rst) begin
    if (rst) begin
        out_send <= 0;
    end else begin
        out_send <= in_receive; 
    end
end

endmodule
