module packet_transmit (
    input clk,
    input rst_n,
    input exe2disp_data_wr,
    input [7:0] exe2disp_data,
    input exe2disp_valid_wr,
    input exe2disp_valid,
    input exe2disp_direction_req,
    input exe2disp_direction,
    input um2npe_data_wr,
    input [7:0] um2npe_data,
    input um2npe_valid_wr,
    input um2npe_valid,
    input disp2usermux_data_wr,
    input [7:0] disp2usermux_data,
    input disp2usermux_valid_wr,
    input disp2usermux_valid,
    output reg [7:0] exe2disp_data_out,
    output reg exe2disp_valid_out,
    output reg disp2exe_alf,
    output reg [7:0] um2npe_data_out,
    output reg um2npe_valid_out,
    output reg um2npe_alf,
    output reg [7:0] disp2usermux_data_out,
    output reg disp2usermux_valid_out,
    output reg usermux2disp_alf
);

reg [7:0] pkt_buffer;
reg pkt_valid;
reg pkt_direction;

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        pkt_buffer <= 8'h00;
        pkt_valid <= 1'b0;
        pkt_direction <= 1'b0;
    end else begin
        if (exe2disp_data_wr && exe2disp_direction_req) begin
            pkt_buffer <= exe2disp_data;
            pkt_valid <= exe2disp_valid;
            pkt_direction <= exe2disp_direction;
        end else if (um2npe_data_wr) begin
            pkt_buffer <= um2npe_data;
            pkt_valid <= um2npe_valid;
            pkt_direction <= 0;
        end else if (disp2usermux_data_wr) begin
            pkt_buffer <= disp2usermux_data;
            pkt_valid <= disp2usermux_valid;
            pkt_direction <= 1;
        end
    end
end

always @* begin
    exe2disp_data_out = pkt_buffer;
    exe2disp_valid_out = pkt_valid && (pkt_direction == 0);
    disp2exe_alf = pkt_valid && (pkt_direction == 0);
    um2npe_data_out = pkt_buffer;
    um2npe_valid_out = pkt_valid && (pkt_direction == 0);
    um2npe_alf = pkt_valid && (pkt_direction == 0);
    disp2usermux_data_out = pkt_buffer;
    disp2usermux_valid_out = pkt_valid && (pkt_direction == 1);
    usermux2disp_alf = pkt_valid && (pkt_direction == 1);
end

endmodule