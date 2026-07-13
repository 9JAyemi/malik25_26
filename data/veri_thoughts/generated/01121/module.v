module ip_packet_filter (
    input wire clk,
    input wire rst,
    input wire input_ip_hdr_valid,
    output wire input_ip_hdr_ready,
    input wire [31:0] input_ip_dest_ip,
    output wire output_ip_hdr_valid,
    input wire output_ip_hdr_ready,
    output wire [31:0] output_ip_dest_ip,
    output wire [47:0] output_ip_eth_dest_mac,
    output wire [15:0] output_ip_length,
    output wire drop
);

parameter FILTER_IP = 32'hc0a80101; // Predefined IP address to filter

reg [31:0] input_ip_dest_ip_reg;
reg [47:0] output_ip_eth_dest_mac_reg;
reg [15:0] output_ip_length_reg;
reg drop_reg;

assign input_ip_hdr_ready = 1;
assign output_ip_hdr_valid = input_ip_hdr_valid;
assign output_ip_dest_ip = input_ip_dest_ip_reg;
assign output_ip_eth_dest_mac = output_ip_eth_dest_mac_reg;
assign output_ip_length = output_ip_length_reg;
assign drop = drop_reg;

always @(posedge clk) begin
    if (rst) begin
        input_ip_dest_ip_reg <= 0;
        output_ip_eth_dest_mac_reg <= 0;
        output_ip_length_reg <= 0;
        drop_reg <= 0;
    end else begin
        if (input_ip_hdr_valid & output_ip_hdr_ready) begin
            input_ip_dest_ip_reg <= input_ip_dest_ip;
            output_ip_eth_dest_mac_reg <= output_ip_eth_dest_mac;
            output_ip_length_reg <= output_ip_length;
            drop_reg <= (input_ip_dest_ip == FILTER_IP);
        end
    end
end

endmodule